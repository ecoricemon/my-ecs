pub mod ds;
pub(crate) mod macros;
pub mod str;
pub mod test_utils;

pub type FxBuildHasher = fxhash::FxBuildHasher;

// === impl ===

use std::{
    borrow::{Borrow, BorrowMut},
    cmp,
    fmt::{self, Debug, Display},
    hash::{self, Hash},
    ops::{Deref, DerefMut},
    sync::{Arc, Condvar, Mutex},
    thread,
};

/// A trait for taking inner value out.
///
/// Various types have methods like `take()` to take something out by consuming the type itself. If
/// the taken value also can be unwrapped, then clients need to write code like `take().take()`.
/// This trait helps to avoid something like that and replace it with just one call.
///
/// # Examples
///
/// ```
/// use my_utils::TakeRecur;
///
/// struct A(B);
/// struct B(C);
/// struct C(i32);
///
/// impl TakeRecur for A
/// where
///     B: TakeRecur
/// {
///     type Inner = <B as TakeRecur>::Inner;
///     fn take_recur(self) -> Self::Inner { self.0.take_recur() }
/// }
///
/// impl TakeRecur for B
/// where
///     C: TakeRecur,
/// {
///     type Inner = <C as TakeRecur>::Inner;
///     fn take_recur(self) -> Self::Inner { self.0.take_recur() }
/// }
///
/// impl TakeRecur for C {
///     type Inner = i32;
///     fn take_recur(self) -> Self::Inner { self.0 }
/// }
///
/// let value = A(B(C(42)));
/// assert_eq!(value.take_recur(), 42);
/// ```
pub trait TakeRecur {
    type Inner;

    /// Takes out inner value recursively then returns it.
    ///
    /// # Examples
    ///
    /// See [`TakeRecur`] documentation.
    fn take_recur(self) -> Self::Inner;
}

/// Implements [`TakeRecur`] for (A0, A1), (A0, A1, A2), ...
macro_rules! impl_take_recur_for_tuple {
    ($n:expr, $($i:expr),*) => {const _: () = {
        paste::paste! {
            impl<$([<A $i>]: TakeRecur),*> TakeRecur for ( $([<A $i>]),* ) {
                type Inner = ( $([<A $i>]::Inner),* );

                fn take_recur(self) -> Self::Inner {
                    ( $( self.$i.take_recur(), )* )
                }
            }
        }
    };};
}
impl_take_recur_for_tuple!(2, 0, 1);
impl_take_recur_for_tuple!(3, 0, 1, 2);
impl_take_recur_for_tuple!(4, 0, 1, 2, 3);
impl_take_recur_for_tuple!(5, 0, 1, 2, 3, 4);
impl_take_recur_for_tuple!(6, 0, 1, 2, 3, 4, 5);
impl_take_recur_for_tuple!(7, 0, 1, 2, 3, 4, 5, 6);
impl_take_recur_for_tuple!(8, 0, 1, 2, 3, 4, 5, 6, 7);

/// A type representing 2^k `usize`.
///
/// Zero is not 2^k though you can create [`PowerOfTwo`] by zero. In that case, zero is considered
/// as `usize::MAX + 1` which is another 2^k.
#[derive(Debug, Clone, Copy)]
pub struct PowerOfTwo {
    value: usize,
    k: u32,
    mask: usize,
}

impl PowerOfTwo {
    /// Creates a new [`PowerOfTwo`] from the given value.
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

    /// Returns inner value.
    pub const fn get(&self) -> usize {
        self.value
    }

    /// Returns `numerator / self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::PowerOfTwo;
    ///
    /// let v = PowerOfTwo::new(4).unwrap();
    /// assert_eq!(v.quotient(3), 0);
    /// assert_eq!(v.quotient(4), 1);
    /// assert_eq!(v.quotient(5), 1);
    /// ```
    pub const fn quotient(&self, numerator: usize) -> usize {
        (numerator >> self.k) & self.mask
    }

    /// Returns `numerator % self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::PowerOfTwo;
    ///
    /// let v = PowerOfTwo::new(4).unwrap();
    /// assert_eq!(v.remainder(3), 3);
    /// assert_eq!(v.remainder(4), 0);
    /// assert_eq!(v.remainder(5), 1);
    /// ```
    pub const fn remainder(&self, numerator: usize) -> usize {
        numerator & self.value.wrapping_sub(1)
    }
}

impl PartialEq for PowerOfTwo {
    fn eq(&self, other: &Self) -> bool {
        // It's sufficient to compare `value` only because others are determined by the value.
        self.value == other.value
    }
}

impl Eq for PowerOfTwo {}

impl PartialOrd for PowerOfTwo {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PowerOfTwo {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // It's sufficient to compare `value` only because others are determined by the value.
        self.value.cmp(&other.value)
    }
}

impl hash::Hash for PowerOfTwo {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        // It's sufficient to hash `value` only because others are determined by the value.
        self.value.hash(state);
    }
}

/// A type that either `A` or `B`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Or<A, B> {
    A(A),
    B(B),
}

impl<A, B> Or<A, B> {
    /// Applies the given function to the value `A` then returns the result.
    pub fn map_a<F, X>(self, op: F) -> Or<X, B>
    where
        F: FnOnce(A) -> X,
    {
        match self {
            Or::A(a) => Or::A(op(a)),
            Or::B(b) => Or::B(b),
        }
    }

    /// Applies the given function to the value `B` then returns the result.
    pub fn map_b<G, Y>(self, op: G) -> Or<A, Y>
    where
        G: FnOnce(B) -> Y,
    {
        match self {
            Or::A(a) => Or::A(a),
            Or::B(b) => Or::B(op(b)),
        }
    }

    /// Applies the given functions to the value `A` and `B` respectively then returns the result.
    pub fn map_ab<F, G, X, Y>(self, op_a: F, op_b: G) -> Or<X, Y>
    where
        F: FnOnce(A) -> X,
        G: FnOnce(B) -> Y,
    {
        match self {
            Or::A(a) => Or::A(op_a(a)),
            Or::B(b) => Or::B(op_b(b)),
        }
    }
}

impl<A: Debug, B: Debug> Debug for Or<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A(a) => a.fmt(f),
            Self::B(b) => b.fmt(f),
        }
    }
}

/// A value with another value.
///
/// This type is almost the same as tuple `(T, U)` except how the type is displayed by
/// [`Display`]. This type only prints first value only.
#[derive(Default, Clone, Copy)]
#[repr(C)]
pub struct With<F, B> {
    /// Exposing data.
    front: F,
    /// Backing data.
    back: B,
}

impl<F, B> With<F, B> {
    pub const fn new(front: F, back: B) -> Self {
        Self { front, back }
    }

    pub fn into_inner(self) -> (F, B) {
        (self.front, self.back)
    }

    pub fn into_front(self) -> F {
        self.front
    }

    pub fn into_back(self) -> B {
        self.back
    }

    pub fn as_refs(&self) -> With<&F, &B> {
        With {
            front: &self.front,
            back: &self.back,
        }
    }

    pub fn as_muts(&mut self) -> With<&mut F, &mut B> {
        With {
            front: &mut self.front,
            back: &mut self.back,
        }
    }

    pub const fn get_back(&self) -> &B {
        &self.back
    }

    pub fn get_back_mut(&mut self) -> &mut B {
        &mut self.back
    }

    pub fn map_front<Op: FnOnce(F) -> G, G>(self, op: Op) -> With<G, B> {
        With {
            front: op(self.front),
            back: self.back,
        }
    }

    pub fn map_back<Op: FnOnce(B) -> C, C>(self, op: Op) -> With<F, C> {
        With {
            front: self.front,
            back: op(self.back),
        }
    }
}

impl<F, B> Deref for With<F, B> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        &self.front
    }
}

impl<F, B> DerefMut for With<F, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.front
    }
}

impl<F, B> AsRef<F> for With<F, B> {
    fn as_ref(&self) -> &F {
        &self.front
    }
}

impl<F, B> AsMut<F> for With<F, B> {
    fn as_mut(&mut self) -> &mut F {
        &mut self.front
    }
}

impl<F, B> From<(F, B)> for With<F, B> {
    fn from((front, back): (F, B)) -> Self {
        Self::new(front, back)
    }
}

impl<F, B> Borrow<F> for With<F, B> {
    fn borrow(&self) -> &F {
        &self.front
    }
}

impl<F, B> BorrowMut<F> for With<F, B> {
    fn borrow_mut(&mut self) -> &mut F {
        &mut self.front
    }
}

impl<F: PartialEq, B> PartialEq for With<F, B> {
    fn eq(&self, other: &Self) -> bool {
        self.front == other.front
    }
}

impl<F: PartialEq, B> PartialEq<F> for With<F, B> {
    fn eq(&self, other_front: &F) -> bool {
        &self.front == other_front
    }
}

impl<F: Eq, B> Eq for With<F, B> {}

impl<F: PartialOrd, B> PartialOrd for With<F, B> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.front.partial_cmp(&other.front)
    }
}

impl<F: PartialOrd, B> PartialOrd<F> for With<F, B> {
    fn partial_cmp(&self, other_front: &F) -> Option<cmp::Ordering> {
        self.front.partial_cmp(other_front)
    }
}

impl<F: Ord, B> Ord for With<F, B> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.front.cmp(&other.front)
    }
}

impl<F: Hash, B> Hash for With<F, B> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.front.hash(state)
    }
}

impl<F: Display, B> Display for With<F, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.front.fmt(f)
    }
}

impl<F: Debug, B> Debug for With<F, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.front.fmt(f)
    }
}

/// A value with [`Result`].
///
/// This type implements [`Deref`] and [`DerefMut`] for the value, therefore it looks like value.
/// But the type provides some `Result` methods as well.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct WithResult<F, O, E>(With<F, Result<O, E>>);

impl<F, O, E> WithResult<F, O, E> {
    pub const fn new(front: F, result: Result<O, E>) -> Self {
        Self(With::new(front, result))
    }

    pub fn into_front(self) -> F {
        let (front, _result) = self.0.into_inner();
        front
    }

    pub fn into_result(self) -> Result<O, E> {
        let (_front, result) = self.0.into_inner();
        result
    }

    /// See [`Result::is_ok`].
    pub const fn is_ok(&self) -> bool {
        self.0.back.is_ok()
    }

    /// See [`Result::is_err`].
    pub const fn is_err(&self) -> bool {
        self.0.back.is_err()
    }

    /// See [`Result::ok`].
    pub fn ok(self) -> Option<O> {
        self.0.back.ok()
    }

    /// See [`Result::err`].
    pub fn err(self) -> Option<E> {
        self.0.back.err()
    }

    /// See [`Result::as_ref`].
    pub const fn as_ref_result(&self) -> Result<&O, &E> {
        self.0.back.as_ref()
    }

    /// See [`Result::as_mut`].
    pub fn as_mut_result(&mut self) -> Result<&mut O, &mut E> {
        self.0.back.as_mut()
    }

    pub fn map<Op: FnOnce(F) -> G, G>(self, op: Op) -> WithResult<G, O, E> {
        let with = self.0.map_front(op);
        WithResult(with)
    }

    /// Applies the given function to the result. See [`Result::map`].
    pub fn map_ok<Op: FnOnce(O) -> P, P>(self, op: Op) -> WithResult<F, P, E> {
        let with = self.0.map_back(|res| res.map(op));
        WithResult(with)
    }

    /// Applies the given function to the result. See [`Result::map_err`].
    pub fn map_err<Op: FnOnce(E) -> D, D>(self, op: Op) -> WithResult<F, O, D> {
        let with = self.0.map_back(|res| res.map_err(op));
        WithResult(with)
    }

    /// See [`Result::expect`].
    pub fn expect(self, msg: &str) -> O
    where
        E: Debug,
    {
        self.0.back.expect(msg)
    }

    /// See [`Result::unwrap`].
    pub fn unwrap(self) -> O
    where
        E: Debug,
    {
        self.0.back.unwrap()
    }
}

impl<F, O, E> Deref for WithResult<F, O, E> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        &self.0.front
    }
}

impl<F, O, E> DerefMut for WithResult<F, O, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.front
    }
}

impl<F, O, E> AsRef<F> for WithResult<F, O, E> {
    fn as_ref(&self) -> &F {
        &self.0.front
    }
}

impl<F, O, E> AsMut<F> for WithResult<F, O, E> {
    fn as_mut(&mut self) -> &mut F {
        &mut self.0.front
    }
}

impl<F, O, E> Borrow<F> for WithResult<F, O, E> {
    fn borrow(&self) -> &F {
        &self.0.front
    }
}

impl<F, O, E> BorrowMut<F> for WithResult<F, O, E> {
    fn borrow_mut(&mut self) -> &mut F {
        &mut self.0.front
    }
}

impl<F: PartialEq, O, E> PartialEq<F> for WithResult<F, O, E> {
    fn eq(&self, other_front: &F) -> bool {
        &self.0.front == other_front
    }
}

impl<F: PartialOrd, O, E> PartialOrd<F> for WithResult<F, O, E> {
    fn partial_cmp(&self, other_front: &F) -> Option<cmp::Ordering> {
        self.0.front.partial_cmp(other_front)
    }
}

impl<F: Display, O, E> Display for WithResult<F, O, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.front.fmt(f)
    }
}

impl<F: Debug, O, E> Debug for WithResult<F, O, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.front.fmt(f)
    }
}

pub fn call_timeout<F>(mut f: F, name: &str, repeat: usize, mut timeout: std::time::Duration)
where
    F: FnMut() + Send + 'static,
{
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    let _handle = thread::spawn(move || {
        for _ in 0..repeat {
            f();
        }

        let (lock, cvar) = &*pair2;
        let mut fin = lock.lock().unwrap();
        *fin = true;
        cvar.notify_one();
    });

    let (lock, cvar) = &*pair;
    let mut fin = lock.lock().unwrap();
    while !*fin {
        let start = std::time::Instant::now();

        let res = cvar.wait_timeout(fin, timeout).unwrap();
        fin = res.0;

        let elapsed = start.elapsed();
        if let Some(remain) = timeout.checked_sub(elapsed) {
            timeout = remain;
        } else {
            #[cfg(unix)]
            {
                use std::os::unix::thread::JoinHandleExt;
                unsafe { libc::pthread_cancel(_handle.into_pthread_t()) };
                panic!("timed out: {name}");
            }

            #[cfg(not(unix))]
            {
                eprintln!("timed out: {name}");
                std::process::exit(101); // Panic result.
            }
        }
    }
}

/// * align - must be a power of 2
pub(crate) const fn round_up(value: usize, align: usize) -> usize {
    (value + align - 1) & (!(align - 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_power_of_two() {
        // Test new method with valid powers of two
        let v4 = PowerOfTwo::new(4).unwrap();
        assert_eq!(v4.get(), 4);
        assert_eq!(v4.quotient(3), 0);
        assert_eq!(v4.quotient(4), 1);
        assert_eq!(v4.quotient(5), 1);

        // Test new method with invalid number
        assert_eq!(PowerOfTwo::new(3), None);

        // Test zero case
        let v0 = PowerOfTwo::new(0).unwrap();
        assert_eq!(v0.get(), 0);
        assert_eq!(v0.quotient(0), 0);
        assert_eq!(v0.quotient(42), 0);
        assert_eq!(v0.remainder(0), 0);
        assert_eq!(v0.remainder(1), 1);

        // Test one case
        let v1 = PowerOfTwo::new(1).unwrap();
        assert_eq!(v1.get(), 1);
        assert_eq!(v1.quotient(3), 3);
        assert_eq!(v1.quotient(4), 4);
        assert_eq!(v1.remainder(2), 0);
    }
}
