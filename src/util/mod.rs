pub mod macros;
pub mod str;
pub mod web;

pub mod prelude {
    pub use super::str as str_util;
    #[cfg(target_arch = "wasm32")]
    pub use super::web as web_util;
    pub use super::{Multi, Or, PowerOfTwo, Take, WithResult};
    pub use crate::{debug_format, impl_from_for_enum, log, tinfo, unwrap_or};
}

use std::{
    fmt,
    ops::{Deref, DerefMut},
    slice,
};

pub trait Take {
    type Inner;

    fn take(self) -> Self::Inner;
}

/// A struct representing 2^k value.
/// But you can designate zero to this struct although zero is not 2^k.
/// In that case, zero is considered as usize::MAX + 1.
#[derive(Debug, Clone, Copy)]
pub struct PowerOfTwo {
    value: usize,
    k: u32,
    mask: usize,
}

impl PowerOfTwo {
    pub const fn new(value: usize) -> Option<Self> {
        if value == 0 {
            Some(Self {
                value,
                k: 0,
                mask: 0,
            })
        } else if value.is_power_of_two() {
            Some(Self {
                value,
                k: value.trailing_zeros(),
                mask: usize::MAX,
            })
        } else {
            None
        }
    }

    pub const fn get(&self) -> usize {
        self.value
    }

    pub const fn quotient(&self, lhs: usize) -> usize {
        (lhs >> self.k) & self.mask
    }

    pub const fn remainder(&self, lhs: usize) -> usize {
        lhs & self.value.wrapping_sub(1)
    }
}

#[derive(Debug, Clone)]
pub struct Multi<T, const N: usize> {
    items: [T; N],
    cur: usize,
}

impl<T, const N: usize> Multi<T, N> {
    pub const fn new(items: [T; N]) -> Self {
        // Validates that N is non zero at compile time.
        let _: () = const { assert!(N > 0, "N must be greater than 0") };

        Self { items, cur: 0 }
    }

    pub fn items(&self) -> &[T; N] {
        &self.items
    }

    pub fn items_mut(&mut self) -> &mut [T; N] {
        &mut self.items
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.items.get_mut(index)
    }

    pub fn switch_to(&mut self, index: usize) -> &mut Self {
        assert!(index < N);
        self.cur = index;
        self
    }

    #[allow(clippy::len_without_is_empty)]
    pub const fn len(&self) -> usize {
        N
    }

    pub const fn is(&self, index: usize) -> bool {
        self.cur == index
    }

    pub fn iter(&self) -> slice::Iter<T> {
        self.items.iter()
    }

    pub fn iter_mut(&mut self) -> slice::IterMut<T> {
        self.items.iter_mut()
    }
}

impl<T, const N: usize> Deref for Multi<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: N must be greater than 0, and index must be in bounds.
        unsafe { self.items.get_unchecked(self.cur) }
    }
}

impl<T, const N: usize> DerefMut for Multi<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: N must be greater than 0, and index must be in bounds.
        unsafe { self.items.get_unchecked_mut(self.cur) }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Or<A, B> {
    A(A),
    B(B),
}

impl<A: fmt::Debug, B: fmt::Debug> fmt::Debug for Or<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A(a) => a.fmt(f),
            Self::B(b) => b.fmt(f),
        }
    }
}

#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WithResult<O, T, E> {
    outer: O,
    res: Result<T, E>,
}

impl<O, T, E> WithResult<O, T, E> {
    pub const fn new(outer: O, res: Result<T, E>) -> Self {
        Self { outer, res }
    }

    pub fn take(self) -> Result<T, E> {
        self.res
    }

    /// See [`Result::is_ok`].
    pub const fn is_ok(&self) -> bool {
        self.res.is_ok()
    }

    /// See [`Result::is_ok_and`].
    pub fn is_ok_and(self, f: impl FnOnce(T) -> bool) -> bool {
        self.res.is_ok_and(f)
    }

    /// See [`Result::is_err`].
    pub const fn is_err(&self) -> bool {
        self.res.is_err()
    }

    /// See [`Result::is_err_and`].
    pub fn is_err_and(self, f: impl FnOnce(E) -> bool) -> bool {
        self.res.is_err_and(f)
    }

    /// See [`Result::ok`].
    pub fn ok(self) -> Option<T> {
        self.res.ok()
    }

    /// See [`Result::err`].
    pub fn err(self) -> Option<E> {
        self.res.err()
    }

    /// See [`Result::as_ref`].
    pub const fn as_ref(&self) -> Result<&T, &E> {
        self.res.as_ref()
    }

    /// See [`Result::as_mut`].
    pub fn as_mut(&mut self) -> Result<&mut T, &mut E> {
        self.res.as_mut()
    }

    pub fn map<U, F>(self, op: F) -> WithResult<O, U, E>
    where 
        F: FnOnce(T) -> U,
    {
        WithResult::new(self.outer, self.res.map(op))
    }

    /// See [`Result::expect`].
    pub fn expect(self, msg: &str) -> T
    where
        E: fmt::Debug,
    {
        self.res.expect(msg)
    }

    /// See [`Result::unwrap`].
    pub fn unwrap(self) -> T
    where
        E: fmt::Debug,
    {
        self.res.unwrap()
    }
}

impl<O, T, E: fmt::Debug> Deref for WithResult<O, T, E> {
    type Target = O;

    fn deref(&self) -> &Self::Target {
        if let Err(e) = &self.res {
            panic!("{e:?}");
        }
        &self.outer
    }
}

impl<O, T, E: fmt::Debug> DerefMut for WithResult<O, T, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        if let Err(e) = &self.res {
            panic!("{e:?}");
        }
        &mut self.outer
    }
}
