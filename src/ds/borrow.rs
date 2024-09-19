use super::atomic::Atomic;
use std::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    process, ptr,
    sync::{
        atomic::{self, Ordering},
        Arc,
    },
    thread,
};

pub type BorrowResult<B, A> = Result<Borrowed<B, A>, BorrowError>;

#[derive(Debug)]
pub enum BorrowError {
    /// Exclusive borrowing is only allowed when no one has borrowed it.
    ExclusiveFailed,

    /// For detecting anomaly, there exist limit you can immutably borrow.
    TooManyBorrow,

    /// If someone tried to borrow with out of bound index.
    OutOfBound,

    /// Failed to find the target.
    NotFound,
}

/// A shallow wrapper of [`Holder`].
#[derive(Debug)]
pub struct SimpleHolder<V, A: Atomic<i32>>(Holder<V, V, V, A>);

impl<V: Clone, A: Atomic<i32>> SimpleHolder<V, A> {
    pub fn new(value: V) -> Self {
        let fn_imm = |value: &V| -> V { value.clone() };
        let fn_mut = |value: &mut V| -> V { value.clone() };
        let inner = Holder::new(value, fn_imm, fn_mut);
        Self(inner)
    }
}

impl<V, A: Atomic<i32>> Deref for SimpleHolder<V, A> {
    type Target = Holder<V, V, V, A>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<V, A: Atomic<i32>> DerefMut for SimpleHolder<V, A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Holding a thing within this and borrow it as [`Borrowed`].
/// Multiple immutable borrowing is allowed, but mutable borrowing is exclusive.
/// This detects dropping `Borrowed`, then this causes panic or abort if this is dropped while any `Borrowed` is still alive.
/// You can check it out using [`Holder::borrow_count`] to see there's any `Borrowed`.
#[derive(Debug)]
pub struct Holder<V, BI, BM, A: Atomic<i32> = atomic::AtomicI32> {
    value: V,
    atomic_cnt: Arc<A>,
    fn_imm: fn(&V) -> BI,
    fn_mut: fn(&mut V) -> BM,
    _marker: PhantomData<(BI, BM)>,
}

impl<V, BI, BM, A: Atomic<i32>> Holder<V, BI, BM, A> {
    const CNT_INIT: i32 = 0;
    const CNT_EXC: i32 = -1;
    const CNT_MAX: i32 = 1024;

    pub fn new(value: V, fn_imm: fn(&V) -> BI, fn_mut: fn(&mut V) -> BM) -> Self {
        Self {
            value,
            atomic_cnt: Arc::new(A::new(Self::CNT_INIT)),
            fn_imm,
            fn_mut,
            _marker: PhantomData,
        }
    }

    pub fn get_fn_imm(&self) -> fn(&V) -> BI {
        self.fn_imm
    }

    pub fn get_fn_mut(&self) -> fn(&mut V) -> BM {
        self.fn_mut
    }

    pub fn borrow(&self) -> BorrowResult<BI, A> {
        self.count_ref()?;
        let value = (self.fn_imm)(&self.value);
        let exclusive = false;
        let atomic_cnt = Arc::clone(&self.atomic_cnt);
        Ok(Borrowed::new(value, exclusive, atomic_cnt))
    }

    pub fn borrow_mut(&mut self) -> BorrowResult<BM, A> {
        self.count_mut()?;
        let value = (self.fn_mut)(&mut self.value);
        let exclusive = true;
        let atomic_cnt = Arc::clone(&self.atomic_cnt);
        Ok(Borrowed::new(value, exclusive, atomic_cnt))
    }

    pub fn get(&self) -> BorrowResult<&V, A> {
        self.count_ref()?;
        let value = &self.value;
        let exclusive = false;
        let atomic_cnt = Arc::clone(&self.atomic_cnt);
        Ok(Borrowed::new(value, exclusive, atomic_cnt))
    }

    pub fn get_mut(&mut self) -> BorrowResult<&mut V, A> {
        self.count_mut()?;
        let value = &mut self.value;
        let exclusive = true;
        let atomic_cnt = Arc::clone(&self.atomic_cnt);
        Ok(Borrowed::new(value, exclusive, atomic_cnt))
    }

    /// Retrieves current reference count.
    /// If it is greater than zero, it means there exist immutable [`Borrowed`].
    /// If it is [`Self::CNT_EXC`], it means there exist mutable `Borrowed`.
    /// Otherwise, in other words, it's zero, there's no `Borrowed`.
    pub fn borrow_count(&self) -> i32 {
        self.atomic_cnt.load(Ordering::Relaxed)
    }

    fn count_ref(&self) -> Result<(), BorrowError> {
        let old = self.atomic_cnt.add(1, Ordering::Relaxed);
        if old > Self::CNT_MAX {
            self.atomic_cnt.sub(1, Ordering::Relaxed);
            Err(BorrowError::TooManyBorrow)
        } else if old == Self::CNT_EXC {
            self.atomic_cnt.sub(1, Ordering::Relaxed);
            Err(BorrowError::ExclusiveFailed)
        } else {
            Ok(())
        }
    }

    fn count_mut(&mut self) -> Result<(), BorrowError> {
        self.atomic_cnt
            .compare_exchange(
                Self::CNT_INIT,
                Self::CNT_EXC,
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .map_err(|_| BorrowError::ExclusiveFailed)?;
        Ok(())
    }
}

impl<V, BI, BM, A: Atomic<i32>> Drop for Holder<V, BI, BM, A> {
    fn drop(&mut self) {
        // Borrowed is dropped with Release ordering and it's synchronized with this Acquire.
        // Therefore, this thread can observe modification happend before when Borrowed is dropped.
        //
        // NOTE: Can we test whether it fails or not if we used Relaxed here?
        let cnt = self.atomic_cnt.load(Ordering::Acquire);
        if cnt != 0 {
            // Holder may be dropped while some threads are using Borrowed.
            // It's definitely unintended behavior.
            if thread::panicking() {
                process::abort();
            } else {
                panic!("Holder was dropped while someone is still using Borrowed");
            }
        }
    }
}

#[derive(Debug)]
pub struct Borrowed<B, A: Atomic<i32>> {
    value: B,
    exclusive: bool,
    atomic_cnt: Arc<A>,
}

impl<B, A: Atomic<i32>> Borrowed<B, A> {
    pub const fn new(value: B, exclusive: bool, atomic_cnt: Arc<A>) -> Self {
        Self {
            value,
            exclusive,
            atomic_cnt,
        }
    }

    pub fn map<T>(mut self, f: impl FnOnce(B) -> T) -> Borrowed<T, A> {
        // Safety: We're going to call forget() on `self`.
        let res = unsafe { self.map_copy(f) };
        mem::forget(self);
        res
    }

    /// Turns inner type into another type, then returns instance.
    /// But `self` will leave as it was, so do not use it any longer.
    /// That means you must not call drop on it as well.
    /// Consider using mem::forget() or something like that on `self` after calling this method.
    ///
    /// # Safety
    ///
    /// Undefined behavior if `self` is used again.
    pub unsafe fn map_copy<T>(&mut self, f: impl FnOnce(B) -> T) -> Borrowed<T, A> {
        let value: B = ptr::read(&self.value as *const _);
        let atomic_cnt = ptr::read(&self.atomic_cnt as *const _);
        Borrowed::new(f(value), self.exclusive, atomic_cnt)
    }

    pub fn map_ref<T>(&self, f: impl FnOnce(&B) -> &T) -> &T {
        f(&self.value)
    }

    pub fn map_mut<T>(&mut self, f: impl FnOnce(&mut B) -> &mut T) -> &mut T {
        f(&mut self.value)
    }
}

impl<B, A: Atomic<i32>> Deref for Borrowed<B, A> {
    type Target = B;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<B, A: Atomic<i32>> DerefMut for Borrowed<B, A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<B, A: Atomic<i32>> Drop for Borrowed<B, A> {
    fn drop(&mut self) {
        if self.exclusive {
            self.atomic_cnt.add(1, Ordering::Release);
        } else {
            self.atomic_cnt.sub(1, Ordering::Release);
        }
    }
}
