use super::ptr::SendSyncPtr;
use rayon::iter::IntoParallelIterator;
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

pub trait AsRawIter {
    fn iter(&self) -> RawIter;
    fn par_iter(&self) -> ParRawIter;

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn iter_of<T>(&self) -> Iter<'_, T>
    where
        Self: Sized,
    {
        Iter::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn iter_mut_of<T>(&mut self) -> IterMut<'_, T>
    where
        Self: Sized,
    {
        IterMut::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn par_iter_of<T>(&self) -> ParIter<'_, T>
    where
        Self: Sized,
    {
        ParIter::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn par_iter_mut_of<T>(&mut self) -> ParIterMut<'_, T>
    where
        Self: Sized,
    {
        ParIterMut::new(self)
    }
}

pub trait AsFlatRawIter {
    /// # Safety
    ///
    /// Returned itereator is not bounded by lifetime.
    /// But it actually relies on `&self`, so it must be used as if
    /// it's borrowed.
    unsafe fn iter(&self) -> FlatRawIter;

    /// # Safety
    ///
    /// Returned itereator is not bounded by lifetime.
    /// But it actually relies on `&self`, so it must be used as if
    /// it's borrowed.
    unsafe fn par_iter(&self) -> ParFlatRawIter;

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn iter_of<T>(&self) -> FlatIter<'_, T>
    where
        Self: Sized,
    {
        FlatIter::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn iter_mut_of<T>(&mut self) -> FlatIterMut<'_, T>
    where
        Self: Sized,
    {
        FlatIterMut::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn par_iter_of<T>(&self) -> ParFlatIter<'_, T>
    where
        Self: Sized,
    {
        ParFlatIter::new(self)
    }

    /// # Safety
    ///
    /// Given container must contain type `T` data.
    #[inline]
    unsafe fn par_iter_mut_of<T>(&mut self) -> ParFlatIterMut<'_, T>
    where
        Self: Sized,
    {
        ParFlatIterMut::new(self)
    }
}

/// Iterator for slice without explict type.
/// It's recommended to wrap this iterator with concrete type and liftime.
#[derive(Debug, Clone, Copy)]
pub struct RawIter {
    pub(crate) cur: SendSyncPtr<u8>,
    pub(crate) end: SendSyncPtr<u8>,
    pub(crate) stride: usize,
}

impl RawIter {
    /// # Safety
    ///
    /// Undefined behavior if
    /// - `end` is less then `start`.
    /// - `end` exceeds isize::MAX.
    /// - `stride` is zero.
    /// - Diffrence between `start` and `end` cannot be divided by `stride`.
    pub const unsafe fn new(start: NonNull<u8>, end: NonNull<u8>, stride: usize) -> Self {
        Self {
            cur: SendSyncPtr::new(start),
            end: SendSyncPtr::new(end),
            stride,
        }
    }

    pub const fn empty() -> Self {
        Self {
            cur: SendSyncPtr::dangling(),
            end: SendSyncPtr::dangling(),
            stride: 1,
        }
    }

    #[inline]
    pub const fn into_par(self) -> ParRawIter {
        ParRawIter(self)
    }

    #[inline]
    pub const fn len(&self) -> usize {
        let end = self.end.as_ptr();
        let cur = self.cur.as_ptr();
        // Safety: Owners guarantee safety.
        unsafe { end.offset_from(cur) as usize / self.stride }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Iterator for RawIter {
    type Item = SendSyncPtr<u8>;

    // `inline` can actually result in better optimization in terms of speed.
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.end {
            let res = self.cur;
            // Safety: Owners guarantee safety.
            self.cur = unsafe { self.cur.add(self.stride) };
            Some(res)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl ExactSizeIterator for RawIter {
    #[inline]
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl DoubleEndedIterator for RawIter {
    // `inline` can actually result in better optimization in terms of speed.
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.cur < self.end {
            // Safety: Owners guarantee safety.
            self.end = unsafe { self.end.sub(self.stride) };
            Some(self.end)
        } else {
            None
        }
    }
}

/// Parallel [`RawIter`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct ParRawIter(RawIter);

impl ParRawIter {
    pub const fn into_seq(self) -> RawIter {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Deref for ParRawIter {
    type Target = RawIter;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ParRawIter {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// [`RawIter`] with concrete type and lifetime.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Iter<'a, T> {
    inner: RawIter,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> Iter<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub unsafe fn new(cont: &impl AsRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        Self::from_raw(cont.iter())
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub const unsafe fn from_raw(raw: RawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub const fn into_par(self) -> ParIter<'a, T> {
        let raw = self.inner.into_par();
        unsafe { ParIter::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ptr| unsafe { ptr.cast().as_ref() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|ptr| unsafe { ptr.cast().as_ref() })
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct IterMut<'a, T> {
    inner: RawIter,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> IterMut<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub unsafe fn new(v: &mut impl AsRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub unsafe fn from_raw(raw: RawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn into_par(self) -> ParIterMut<'a, T> {
        let raw = self.inner.into_par();
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { ParIterMut::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ptr| unsafe { ptr.cast().as_mut() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|ptr| unsafe { ptr.cast().as_mut() })
    }
}

/// [`ParRawIter`] with concrete type and lifetime.
/// This is parallel version of [`Iter`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ParIter<'a, T> {
    pub(crate) inner: ParRawIter,
    pub(crate) _marker: PhantomData<&'a T>,
}

impl<'a, T> ParIter<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub unsafe fn new(v: &'a impl AsRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.par_iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub const unsafe fn from_raw(raw: ParRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    pub const fn into_seq(self) -> Iter<'a, T> {
        let raw = self.inner.into_seq();
        // Safety: This iterator is borrowing a vector.
        unsafe { Iter::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// [`ParRawIter`] with concrete type and lifetime.
/// This is parallel version of [`IterMut`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug)]
#[repr(transparent)]
pub struct ParIterMut<'a, T> {
    pub(crate) inner: ParRawIter,
    pub(crate) _marker: PhantomData<&'a mut T>,
}

impl<'a, T> ParIterMut<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub fn new(v: &mut impl AsRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.par_iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub unsafe fn from_raw(raw: ParRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    pub fn into_seq(self) -> IterMut<'a, T> {
        let raw = self.inner.into_seq();
        // Safety: This iterator is borrowing a vector.
        unsafe { IterMut::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Nested [`RawIter`] which yields `RawIter`.
/// You can call [`Iterator::flatten`] to access each item,
/// which is [`SendSyncPtr`], but it may be slower than you thought.
/// In that case, consider using [`FlatRawIter`] instaed.
#[derive(Debug, Clone)]
pub struct NestedRawIter {
    this: NonNull<u8>,
    fn_iter: unsafe fn(this: NonNull<u8>, index: usize) -> RawIter,
    cur: usize,
    len: usize,
}

impl NestedRawIter {
    /// # Safety
    ///
    /// `fn_iter` must operate safely while the iterator lives.
    pub const unsafe fn new(
        this: NonNull<u8>,
        fn_iter: unsafe fn(this: NonNull<u8>, index: usize) -> RawIter,
        len: usize,
    ) -> Self {
        Self {
            this,
            fn_iter,
            cur: 0,
            len,
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Iterator for NestedRawIter {
    type Item = RawIter;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.len {
            // Safety: Owners guarantee safety.
            let res = unsafe { (self.fn_iter)(self.this, self.cur) };
            self.cur += 1;
            Some(res)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl ExactSizeIterator for NestedRawIter {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

/// Nested [RawIter], but flatten iterator.
/// Explicit flatten iterator can give us better optimization in for loop.
//
// To implement rayon's ParallelIterator, we have to implement
// `ExactSizeIterator` and `DoubleEndedIterator`.
// So we track right side status and total number of items.
#[derive(Debug, Clone, Copy)]
pub struct FlatRawIter {
    /// Left [RawIter::cur].
    /// When [Iterator::next] is called, this pointer may be returned.
    pub(crate) ll: SendSyncPtr<u8>,

    /// Left [RawIter::end], which is right boundary of the left iterator.
    /// Note that `end` is not included in the range. It's the next pointer of
    /// the right bound.
    pub(crate) lr: SendSyncPtr<u8>,

    /// Right [RawIter::cur], which is left boundary of the right iterator.
    pub(crate) rl: SendSyncPtr<u8>,

    /// Right [RawIter::end].
    /// When [DoubleEndedIterator::next_back] is called,
    /// the pointer before this may be returned.
    /// Note that `end` is not included in the range. It's the next pointer of
    /// the right bound.
    pub(crate) rr: SendSyncPtr<u8>,

    /// Pointer to the actual container.
    pub(crate) this: SendSyncPtr<u8>,

    /// Left chunk index for the next left [RawIter].
    /// This index always points to the next left iterator, not current one.
    pub(crate) li: usize,

    /// Right chunk index for the next right [RawIter].
    /// This index always points to the current right iterator.
    pub(crate) ri: usize,

    /// Function that returns [RawIter] of a chunk.
    pub(crate) fn_iter: unsafe fn(this: NonNull<u8>, chunk_idx: usize) -> RawIter,

    /// Function that returns [RawIter], chunk index, and offset from an item index.
    pub(crate) fn_find: unsafe fn(this: NonNull<u8>, item_idx: usize) -> (RawIter, usize, usize),

    /// Stride in bytes.
    pub(crate) stride: usize,

    // used for parallel.
    pub(crate) off: usize,

    /// Number of remaining items.
    pub(crate) len: usize,
}

impl FlatRawIter {
    /// * this - Pointer to container.
    /// * chunks - Number of chunks.
    /// * fn_iter - Function that returns [RawIter] for an index.
    /// * stride - Stride in bytes.
    /// * len - Total number of items.
    ///
    /// # Safety
    ///
    /// `fn_iter` must operate safely while the iterator lives.
    pub unsafe fn new(
        this: NonNull<u8>,
        chunks: usize,
        fn_iter: unsafe fn(this: NonNull<u8>, chunk_idx: usize) -> RawIter,
        fn_find: unsafe fn(this: NonNull<u8>, item_idx: usize) -> (RawIter, usize, usize),
        stride: usize,
        len: usize,
    ) -> Self {
        Self {
            ll: SendSyncPtr::dangling(),
            lr: SendSyncPtr::dangling(),
            rl: SendSyncPtr::dangling(),
            rr: SendSyncPtr::dangling(),
            this: SendSyncPtr::new(this),
            li: 0,
            ri: chunks,
            fn_iter,
            fn_find,
            stride,
            off: 0,
            len,
        }
    }

    #[inline]
    pub const fn into_par(self) -> ParFlatRawIter {
        ParFlatRawIter(self)
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Iterator for FlatRawIter {
    type Item = SendSyncPtr<u8>;

    // `inline` can actually result in better optimization in terms of speed.
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.ll == self.lr {
            (self.ll, self.lr) = if self.li < self.ri {
                // Safety: Owners guarantee validity.
                let next = unsafe { (self.fn_iter)(self.this.as_nonnull(), self.li) };
                (next.cur, next.end)
            } else {
                (self.rl, self.rr)
            };
            if self.ll == self.lr {
                return None;
            }
            self.li += 1;
        }

        let res = Some(self.ll);
        // Safety: Owners guarantee validity.
        self.ll = unsafe { self.ll.add(self.stride) };
        if self.li > self.ri {
            self.rl = self.ll;
        }
        self.len -= 1;
        res
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl ExactSizeIterator for FlatRawIter {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl DoubleEndedIterator for FlatRawIter {
    // `inline` can actually result in better optimization in terms of speed.
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.rl == self.rr {
            (self.rl, self.rr) = if self.li < self.ri {
                // Safety: Owners guarantee validity.
                let next = unsafe { (self.fn_iter)(self.this.as_nonnull(), self.ri - 1) };
                (next.cur, next.end)
            } else {
                (self.ll, self.lr)
            };
            if self.rl == self.rr {
                return None;
            }
            self.ri -= 1;
        }

        // Safety: Owners guarantee validity.
        self.rr = unsafe { self.rr.sub(self.stride) };
        if self.li > self.ri {
            self.lr = self.rr;
        }
        self.len -= 1;
        Some(self.rr)
    }
}

/// Parallel [FlatRawIter].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct ParFlatRawIter(FlatRawIter);

impl ParFlatRawIter {
    pub const fn into_seq(self) -> FlatRawIter {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Deref for ParFlatRawIter {
    type Target = FlatRawIter;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ParFlatRawIter {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// [FlatRawIter] with concrete type and lifetime.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct FlatIter<'a, T: 'a> {
    inner: FlatRawIter,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> FlatIter<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub fn new(v: &impl AsFlatRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub const unsafe fn from_raw(raw: FlatRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub const fn into_par(self) -> ParFlatIter<'a, T> {
        let raw = self.inner.into_par();
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { ParFlatIter::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> Iterator for FlatIter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ptr| unsafe { ptr.cast().as_ref() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for FlatIter<'a, T> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'a, T> DoubleEndedIterator for FlatIter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|ptr| unsafe { ptr.cast().as_ref() })
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct FlatIterMut<'a, T: 'a> {
    inner: FlatRawIter,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> FlatIterMut<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub fn new(v: &mut impl AsFlatRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub unsafe fn from_raw(raw: FlatRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn into_par(self) -> ParFlatIterMut<'a, T> {
        let raw = self.inner.into_par();
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { ParFlatIterMut::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, T> Iterator for FlatIterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|ptr| unsafe { ptr.cast().as_mut() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for FlatIterMut<'a, T> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'a, T> DoubleEndedIterator for FlatIterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|ptr| unsafe { ptr.cast().as_mut() })
    }
}

/// [ParFlatRawIter] with concrete type and lifetime.
/// This is parallel version of [FlatIter].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ParFlatIter<'a, T: 'a> {
    pub(crate) inner: ParFlatRawIter,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> ParFlatIter<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub fn new(v: &impl AsFlatRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.par_iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub const unsafe fn from_raw(raw: ParFlatRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    pub const fn into_seq(self) -> FlatIter<'a, T> {
        let raw = self.inner.into_seq();
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { FlatIter::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// [`ParFlatRawIter`] with concrete type and lifetime.
/// This is parallel version of [`FlatIterMut`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ParFlatIterMut<'a, T: 'a> {
    pub(crate) inner: ParFlatRawIter,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> ParFlatIterMut<'a, T> {
    /// Borrows container and returns its iterator.
    ///
    /// # Safety
    ///
    /// Given container must contain type `T` data.
    pub fn new(v: &mut impl AsFlatRawIter) -> Self {
        // We're borrowing container, so lifetime is tied up.
        unsafe { Self::from_raw(v.par_iter()) }
    }

    /// # Safety
    ///
    /// Undefined behavior if any of the conditions described below are not met.
    /// - Given raw iterator must yield pointers to type `T`.
    /// - Lifetime defined by clients must be sufficient about the raw iterator.
    pub unsafe fn from_raw(raw: ParFlatRawIter) -> Self {
        Self {
            inner: raw,
            _marker: PhantomData,
        }
    }

    pub fn into_seq(self) -> FlatIterMut<'a, T> {
        let raw = self.inner.into_seq();
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { FlatIterMut::from_raw(raw) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RawGetter {
    /// Pointer to the container.
    this: SendSyncPtr<u8>,

    /// Number of items.
    len: usize,

    /// Random access getter.
    fn_get: unsafe fn(this: NonNull<u8>, index: usize) -> NonNull<u8>,

    /// Sequential access iterator.
    fn_iter: unsafe fn(this: NonNull<u8>) -> FlatRawIter,
}

impl RawGetter {
    /// # Safety
    ///
    /// Pointer must be valid while this is alive.
    pub const unsafe fn new(
        this: NonNull<u8>,
        len: usize,
        fn_get: unsafe fn(this: NonNull<u8>, index: usize) -> NonNull<u8>,
    ) -> Self {
        Self {
            this: SendSyncPtr::new(this),
            len,
            fn_get,
            fn_iter: |_| unimplemented!(),
        }
    }

    pub const fn with_iter(mut self, fn_iter: unsafe fn(this: NonNull<u8>) -> FlatRawIter) -> Self {
        self.fn_iter = fn_iter;
        self
    }

    pub fn get(&self, index: usize) -> Option<NonNull<u8>> {
        if index < self.len {
            unsafe { Some(self.get_unchecked(index)) }
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// Undefined behavior if `index` is out of bound.
    pub unsafe fn get_unchecked(&self, index: usize) -> NonNull<u8> {
        // Safety: In addition to index, `self.this` must be a valid pointer,
        // which is guaranteed by owners.
        unsafe { (self.fn_get)(self.this.as_nonnull(), index) }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> FlatRawIter {
        // Safety: Owners guarantee validity.
        unsafe { (self.fn_iter)(self.this.as_nonnull()) }
    }
}

pub trait AsGetter {
    type Item;

    fn as_getter(&self) -> Getter<'_, Self::Item>;
    fn as_getter_mut(&mut self) -> GetterMut<'_, Self::Item>;
}

/// An accessor to an array.
/// Getter provides primitive methods like [`Self::get`] and [`Self::iter`].
/// `get()` is random access method so you can retrive an item at an index.
/// `iter()`, on the other hand, returns sequential access iterator.
/// The iterator can be way faster than access via `get()` thanks to inline
/// optimization.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Getter<'cont, T: 'cont> {
    raw: RawGetter,
    _marker: PhantomData<&'cont T>,
}

impl<'cont, T> Getter<'cont, T> {
    pub fn new(container: &'cont impl AsGetter<Item = T>) -> Self {
        container.as_getter()
    }

    /// Instead of creating from [`AsGetter`], you can create from [`RawGetter`].
    /// But, you must provide valid concrete type `T` and lifetime `'cont`.
    ///
    /// # Safety
    ///
    /// Undefined behavior if concrete type `T` is not valid or
    /// container pointer inside [`RawGetter`] is invalidated.
    pub unsafe fn from_raw(raw: RawGetter) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    pub fn into_raw(self) -> RawGetter {
        self.raw
    }

    pub fn len(&self) -> usize {
        self.raw.len()
    }

    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            // Safety: We checked the length.
            unsafe { Some(self.get_unchecked(index)) }
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// Undefined behavior if `index` is out of bound.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        let ptr = self.raw.get_unchecked(index).cast();
        ptr.as_ref()
    }

    pub fn iter(&self) -> FlatIter<'cont, T> {
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { FlatIter::from_raw(self.raw.iter()) }
    }

    #[inline]
    pub fn par_iter(&self) -> ParFlatIter<'cont, T> {
        self.iter().into_par()
    }
}

impl<'cont, T> IntoIterator for Getter<'cont, T> {
    type Item = &'cont T;
    type IntoIter = FlatIter<'cont, T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::iter(&self)
    }
}

impl<'cont, T: Send + Sync> IntoParallelIterator for Getter<'cont, T> {
    type Item = &'cont T;
    type Iter = ParFlatIter<'cont, T>;

    fn into_par_iter(self) -> Self::Iter {
        Self::par_iter(&self)
    }
}

/// An accessor to an array.  
/// Getter provides primitive methods like [`get_mut`][0] and [`iter_mut`][1].
///
/// - [get_mut][0] is random access method so you can retrive an item at an index.
/// - [iter_mut][1], on the other hand, returns sequential access iterator.
///   The iterator can be faster than access via [get_mut][0] thanks to inline
///   optimization. But it strongly relies on build options.
///
/// [0]: Self::get_mut
/// [1]: Self::iter_mut
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct GetterMut<'cont, T: 'cont> {
    raw: RawGetter,
    _marker: PhantomData<&'cont mut T>,
}

impl<'cont, T> GetterMut<'cont, T> {
    pub fn new(container: &'cont mut impl AsGetter<Item = T>) -> Self {
        container.as_getter_mut()
    }

    /// Instead of creating from [AsGetter], you can create from [RawGetter].
    /// But, you must provide valid concrete type `T` and lifetime `'cont`.
    ///
    /// # Safety
    ///
    /// Undefined behavior if concrete type `T` is not valid or
    /// container pointer inside [RawGetter] is invalidated.
    pub unsafe fn from_raw(raw: RawGetter) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    pub fn into_raw(self) -> RawGetter {
        self.raw
    }

    pub fn len(&self) -> usize {
        self.raw.len()
    }

    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            // Safety: We checked the length.
            unsafe { Some(self.get_unchecked(index)) }
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// Undefined behavior if `index` is out of bound.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        let ptr = self.raw.get_unchecked(index).cast();
        ptr.as_ref()
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len() {
            // Safety: `index` is in bounds.
            unsafe { Some(self.get_unchecked_mut(index)) }
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// Undefined behavior if `index` is out of bound.
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        let mut ptr = self.raw.get_unchecked(index).cast();
        ptr.as_mut()
    }

    pub fn iter(&self) -> FlatIter<'cont, T> {
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { FlatIter::from_raw(self.raw.iter()) }
    }

    pub fn iter_mut(&mut self) -> FlatIterMut<'cont, T> {
        // Safety: By owners, type `T` matches and lifetime `a is sufficient.
        unsafe { FlatIterMut::from_raw(self.raw.iter()) }
    }

    #[inline]
    pub fn par_iter(&self) -> ParFlatIter<'cont, T> {
        self.iter().into_par()
    }

    #[inline]
    pub fn par_iter_mut(&mut self) -> ParFlatIterMut<'cont, T> {
        self.iter_mut().into_par()
    }
}

impl<'cont, T> IntoIterator for GetterMut<'cont, T> {
    type Item = &'cont mut T;
    type IntoIter = FlatIterMut<'cont, T>;

    fn into_iter(mut self) -> Self::IntoIter {
        Self::iter_mut(&mut self)
    }
}

impl<'cont, T: Send + Sync> IntoParallelIterator for GetterMut<'cont, T> {
    type Item = &'cont mut T;
    type Iter = ParFlatIterMut<'cont, T>;

    fn into_par_iter(mut self) -> Self::Iter {
        Self::par_iter_mut(&mut self)
    }
}
