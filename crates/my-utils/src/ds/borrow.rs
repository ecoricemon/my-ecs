use std::{
    cell::UnsafeCell,
    fmt::{self, Debug},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

/// A [`Holder`] that lends its inner value itself by cloning.
#[derive(Debug)]
pub struct SimpleHolder<V>(Holder<V, V, V>);

impl<V: Clone> SimpleHolder<V> {
    pub fn new(value: V) -> Self {
        let fn_imm = |value: NonNull<V>| -> V { unsafe { value.as_ref().clone() } };
        let fn_mut = |value: NonNull<V>| -> V { unsafe { value.as_ref().clone() } };
        // Safety: `fn_imm` and `fn_mut` clones the value so that they don't require borrow check.
        let inner = unsafe { Holder::new(value, fn_imm, fn_mut) };
        Self(inner)
    }

    pub fn into_value(self) -> V {
        self.0.into_value()
    }
}

impl<V> Deref for SimpleHolder<V> {
    type Target = Holder<V, V, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<V> DerefMut for SimpleHolder<V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// A type that holds a value and allows us borrow the value.
///
/// When you want to borrow inner value you can call [`Holder::borrow`] or [`Holder::borrow_mut`].
/// They return the inner value wrapped in [`Borrowed`] which tracks borrow status.
///
/// Multiple immutable borrowing is allowed, but mutable borrowing is exclusive. If this struct is
/// dropped while any borrowed value is alive, it causes panic. You can check it out using
/// [`Holder::borrow_count`] to see there's any borrowed value.
///
/// # Features
///
/// Borrow check is enabled if and only if `check` feature is enabled. Otherwise, this struct does
/// nothing special.
pub struct Holder<V, BI, BM> {
    /// The inner value holder holds.
    value: UnsafeCell<V>,

    /// Function that borrows the inner value immutably.
    pub fn_imm: fn(NonNull<V>) -> BI,

    /// Function that borrows the inner value mutably.
    pub fn_mut: fn(NonNull<V>) -> BM,

    /// Reference count to check borrow status at runtime.
    #[cfg(feature = "check")]
    borrow_state: check_borrow::BorrowState,

    _marker: PhantomData<(BI, BM)>,
}

impl<V, BI, BM> Holder<V, BI, BM> {
    /// Creates a [`Holder`] with the given value.
    ///
    /// `Holder` checks borrow rule at runtime by enabled feature `check`. But it requires
    /// additional operations, so that if you are confident, you can use the `Holder` without the
    /// borrow check.
    ///
    /// * `fn_imm` - Function that borrows the value and returns borrowed immutable value.
    /// * `fn_mut` - Function that borrows the value and returns borrowed mutable value.
    ///
    /// # Safety
    ///
    /// `Holder` disables Rust default borrow checker. Borrow rule is not checked even if the
    /// `fn_imm` and `fn_mut` return references to the inner value. However, `Holder` checks the
    /// borrow rule at runtime by enabled feature `check`. If the feature is not enabled, this
    /// function is unsafe due to the disabled runtime borrow check.
    ///
    /// If the `fn_imm` and `fn_mut` returns static type instead of reference, it's safe regardless
    /// of enabling the feature because they don't need borrow check.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Holder;
    /// use std::ptr::NonNull;
    ///
    /// let fn_imm = |ptr: NonNull<i32>| unsafe { ptr.as_ref() };
    /// let fn_mut = |mut ptr: NonNull<i32>| unsafe { ptr.as_mut() };
    /// let holder = unsafe { Holder::new(42, fn_imm, fn_mut) };
    ///
    /// let value = holder.borrow_mut().unwrap();
    /// //holder.borrow().unwrap(); // panic if `check` feature enabled
    ///
    /// assert_eq!(**value, 42);
    /// ```
    // Lifetime `v` allows us to put something in like example above.
    pub unsafe fn new(
        value: V,
        fn_imm: fn(NonNull<V>) -> BI,
        fn_mut: fn(NonNull<V>) -> BM,
    ) -> Self {
        Self {
            value: UnsafeCell::new(value),
            fn_imm,
            fn_mut,
            #[cfg(feature = "check")]
            borrow_state: check_borrow::BorrowState::new(),
            _marker: PhantomData,
        }
    }

    /// Unwraps the holder then returns inner value.
    ///
    /// Note that the holder destroys so other borrowed values are assumed invalidated as well.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Holder;
    ///
    /// let holder = unsafe { Holder::new(0, |v| v, |v| v) };
    /// assert_eq!(holder.into_value(), 0);
    /// ```
    pub fn into_value(self) -> V {
        unsafe {
            // We takes out the value and drops other fields here.
            let value = ptr::read(&self.value);

            // Only cnt requires destroy procedure.
            #[cfg(feature = "check")]
            {
                let borrow_state = ptr::read(&self.borrow_state);
                borrow_state.set_value_is_dead();
            }

            mem::forget(self);

            value.into_inner()
        }
    }

    /// Borrows inner value.
    ///
    /// If `check` feature is enabled, runtime borrow checker works and blocks try borrowing value
    /// after mutable borrow.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Holder;
    /// use std::ptr::NonNull;
    ///
    /// let f = |ptr: NonNull<i32>| unsafe { *ptr.as_ref() };
    /// let holder = unsafe { Holder::new(42, f, f) };
    /// assert_eq!(*holder.borrow().unwrap(), 42);
    /// ```
    pub fn borrow(&self) -> BorrowResult<BI> {
        // Safety: Infallible
        let ptr = unsafe { NonNull::new_unchecked(self.value.get()) };
        let output = (self.fn_imm)(ptr);

        #[cfg(feature = "check")]
        {
            let exclusive = false;
            let borrow_state = self.borrow_state.clone_by_shared_borrow()?;
            Ok(Borrowed::new(output, exclusive, borrow_state))
        }

        #[cfg(not(feature = "check"))]
        Ok(Borrowed::new(output))
    }

    /// Borrows inner value mutably.
    ///
    /// If `check` feature is enabled, runtime borrow checker works and blocks try borrowing value
    /// after mutable or immutable borrow.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Holder;
    /// use std::ptr::NonNull;
    ///
    /// let fn_imm = |ptr: NonNull<i32>| unsafe { ptr.as_ref() };
    /// let fn_mut = |mut ptr: NonNull<i32>| unsafe { ptr.as_mut() };
    /// let holder = unsafe { Holder::new(42, fn_imm, fn_mut) };
    ///
    /// **holder.borrow_mut().unwrap() += 1;
    /// assert_eq!(**holder.borrow().unwrap(), 43);
    /// ```
    pub fn borrow_mut(&self) -> BorrowResult<BM> {
        // Safety: Infallible
        let ptr = unsafe {
            let ptr = self.value.get();
            NonNull::new_unchecked(ptr)
        };
        let output = (self.fn_mut)(ptr);

        #[cfg(feature = "check")]
        {
            let exclusive = true;
            let borrow_state = self.borrow_state.clone_by_mutable_borrow()?;
            Ok(Borrowed::new(output, exclusive, borrow_state))
        }

        #[cfg(not(feature = "check"))]
        Ok(Borrowed::new(output))
    }

    pub fn ptr_inner(&self) -> NonNull<V> {
        // Safety: Infallible
        unsafe { NonNull::new_unchecked(self.value.get()) }
    }

    /// Returns current reference count.
    pub fn borrow_count(&self) -> u32 {
        #[cfg(feature = "check")]
        {
            self.borrow_state.borrow_count()
        }

        #[cfg(not(feature = "check"))]
        {
            0
        }
    }
}

impl<V, BI, BM> Debug for Holder<V, BI, BM>
where
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Holder");

        d.field("value", &self.value);

        #[cfg(feature = "check")]
        d.field("borrow_state", &self.borrow_state);

        d.finish_non_exhaustive()
    }
}

/// A type generated by [`Holder`] that wraps a value in it shallowly.
///
/// This struct implements [`Deref`] and [`DerefMut`] for the inner value so that clients can use
/// this struct like the inner value.
///
/// If `check` feature is enabled, this struct tracks borrow status at runtime, and will warn you if
/// borrow rule was violated.
#[derive(Debug)]
pub struct Borrowed<B> {
    value: B,
    #[cfg(feature = "check")]
    exclusive: bool,
    #[cfg(feature = "check")]
    borrow_state: check_borrow::BorrowState,
}

impl<B> Borrowed<B> {
    const fn new(
        value: B,
        #[cfg(feature = "check")] exclusive: bool,
        #[cfg(feature = "check")] borrow_state: check_borrow::BorrowState,
    ) -> Self {
        Self {
            value,
            #[cfg(feature = "check")]
            exclusive,
            #[cfg(feature = "check")]
            borrow_state,
        }
    }

    pub fn try_clone(&self) -> BorrowResult<B>
    where
        B: Clone,
    {
        #[cfg(feature = "check")]
        {
            if !self.exclusive {
                Ok(Self {
                    value: self.value.clone(),
                    exclusive: false,
                    borrow_state: self.borrow_state.clone_by_shared_borrow()?,
                })
            } else {
                Err(BorrowError::Exclusive)
            }
        }

        #[cfg(not(feature = "check"))]
        Ok(Self {
            value: self.value.clone(),
        })
    }

    /// Converts inner value through the given function while maintaining borrow state.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SimpleHolder;
    ///
    /// let holder = SimpleHolder::new(42);
    /// let value = holder.borrow().unwrap();
    /// let value = value.map(|v: i32| v.to_string());
    /// assert_eq!(*value, "42");
    /// ```
    pub fn map<T>(mut self, f: impl FnOnce(B) -> T) -> Borrowed<T> {
        // Safety: self is not used again due to forget.
        let res = unsafe { self.map_copy(f) };
        mem::forget(self);
        res
    }

    /// Turns inner value into another type, then returns converted value wrapped in [`Borrowed`]
    /// while keeping borrow status.
    ///
    /// The operation looks like `move` with type-conversion. But `self` will leave as it was, so
    /// caller must not use it any longer. That means caller must not call even drop function on it.
    /// Consider using [`forget`](mem::forget) or something like that to `self` after calling this
    /// method.
    ///
    /// # Safety
    ///
    /// Undefined behavior if `self` is used again.
    unsafe fn map_copy<T>(&mut self, f: impl FnOnce(B) -> T) -> Borrowed<T> {
        let value: B = unsafe { ptr::read(&self.value as *const B) };

        #[cfg(feature = "check")]
        {
            let borrow_state = unsafe { ptr::read(&self.borrow_state as *const _) };
            Borrowed::new(f(value), self.exclusive, borrow_state)
        }

        #[cfg(not(feature = "check"))]
        Borrowed::new(f(value))
    }
}

impl<B> Deref for Borrowed<B> {
    type Target = B;

    fn deref(&self) -> &Self::Target {
        #[cfg(feature = "check")]
        if !self.borrow_state.exists_value() {
            panic!("dereferencing borrowed value after free")
        }

        &self.value
    }
}

impl<B> DerefMut for Borrowed<B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        #[cfg(feature = "check")]
        if !self.borrow_state.exists_value() {
            panic!("dereferencing borrowed value after free")
        }

        &mut self.value
    }
}

impl<B> Drop for Borrowed<B> {
    fn drop(&mut self) {
        #[cfg(feature = "check")]
        {
            if self.exclusive {
                self.borrow_state.reflect_mutable_borrow_release().unwrap();
            } else {
                self.borrow_state.reflect_shared_borrow_release().unwrap();
            }
        }
    }
}

/// Result type for [`Borrowed`] with [`BorrowError`] for error propagation.
pub type BorrowResult<B> = Result<Borrowed<B>, BorrowError>;

/// An error type associated with borrow.
///
/// This error type will be commonly seen with [`Holder`], which can borrow its inner value to you.
#[derive(Debug)]
#[non_exhaustive]
pub enum BorrowError {
    /// Borrow is not allowed while exclusive borrow exists.
    Exclusive,

    /// For detecting anomaly, there exist the limit how many you can immutably borrow.
    TooManyBorrow,

    /// Borrow failed because of index out of bounds.
    OutOfBound,

    /// Borrow failed because of not found key.
    NotFound,

    Other(String),
}

#[cfg(feature = "check")]
mod check_borrow {
    use super::BorrowError;
    use std::{
        fmt::{self, Debug},
        sync::{Arc, Mutex},
    };

    pub(super) struct BorrowState {
        state: Arc<Mutex<u32>>,
    }

    impl BorrowState {
        const BIT_IS_ALIVE: u32 = 1 << 31;
        const BIT_IS_EXCLUSIVE: u32 = 1 << 30;
        const MASK_COUNT: u32 = u32::MAX ^ Self::BIT_IS_ALIVE ^ Self::BIT_IS_EXCLUSIVE;
        const SHARED_BORROW_LIMIT: u32 = 1000;

        pub(super) fn new() -> Self {
            let initial_state = Self::BIT_IS_ALIVE;
            Self {
                state: Arc::new(Mutex::new(initial_state)),
            }
        }

        pub(super) fn clone_by_shared_borrow(&self) -> Result<Self, BorrowError> {
            let mut state = self
                .state
                .lock()
                .map_err(|e| BorrowError::Other(e.to_string()))?;
            let cur_state = *state;

            Self::check_no_exclusive_borrow(cur_state)?;
            Self::check_under_borrow_limit(cur_state)?;

            let bit_is_alive = cur_state & Self::BIT_IS_ALIVE;
            let new_cnt = (cur_state & Self::MASK_COUNT) + 1;
            *state = bit_is_alive | new_cnt;

            Ok(Self {
                state: self.state.clone(),
            })
        }

        pub(super) fn clone_by_mutable_borrow(&self) -> Result<Self, BorrowError> {
            let mut state = self
                .state
                .lock()
                .map_err(|e| BorrowError::Other(e.to_string()))?;
            let cur_state = *state;

            Self::check_no_exclusive_borrow(cur_state)?;
            Self::check_under_borrow_limit(cur_state)?;

            let bit_is_alive = cur_state & Self::BIT_IS_ALIVE;
            let new_cnt = 1;
            *state = bit_is_alive | Self::BIT_IS_EXCLUSIVE | new_cnt;

            Ok(Self {
                state: self.state.clone(),
            })
        }

        pub(super) fn reflect_shared_borrow_release(&self) -> Result<(), BorrowError> {
            let mut state = self
                .state
                .lock()
                .map_err(|e| BorrowError::Other(e.to_string()))?;
            let cur_state = *state;

            let bit_is_alive = cur_state & Self::BIT_IS_ALIVE;
            let new_cnt = (cur_state & Self::MASK_COUNT) - 1;
            *state = bit_is_alive | new_cnt;
            Ok(())
        }

        pub(super) fn reflect_mutable_borrow_release(&self) -> Result<(), BorrowError> {
            let mut state = self
                .state
                .lock()
                .map_err(|e| BorrowError::Other(e.to_string()))?;
            let cur_state = *state;

            let bit_is_alive = cur_state & Self::BIT_IS_ALIVE;
            let new_cnt = 0;
            *state = bit_is_alive | new_cnt;
            Ok(())
        }

        pub(super) fn exists_value(&self) -> bool {
            let state = *self.state.lock().unwrap();
            state & Self::BIT_IS_ALIVE != 0
        }

        pub(super) fn set_value_is_dead(&self) {
            let mut state = self.state.lock().unwrap();
            *state &= !Self::BIT_IS_ALIVE;
        }

        pub(super) fn borrow_count(&self) -> u32 {
            let state = self.state.lock().unwrap();
            *state & Self::MASK_COUNT
        }

        #[inline]
        fn check_no_exclusive_borrow(state: u32) -> Result<(), BorrowError> {
            if state & Self::BIT_IS_EXCLUSIVE == 0 {
                Ok(())
            } else {
                Err(BorrowError::Exclusive)
            }
        }

        #[inline]
        fn check_under_borrow_limit(state: u32) -> Result<(), BorrowError> {
            if state & Self::MASK_COUNT < Self::SHARED_BORROW_LIMIT {
                Ok(())
            } else {
                Err(BorrowError::TooManyBorrow)
            }
        }
    }

    impl Debug for BorrowState {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let state = *self.state.lock().unwrap();
            f.debug_struct("BorrowState")
                .field("is_alive", &(state & Self::BIT_IS_ALIVE != 0))
                .field("is_exclusive", &(state & Self::BIT_IS_EXCLUSIVE != 0))
                .field("count", &(state & Self::MASK_COUNT))
                .finish()
        }
    }
}
