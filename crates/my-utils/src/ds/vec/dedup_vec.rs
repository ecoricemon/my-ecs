use std::{fmt, hash};

/// A trait for [`DedupVec`].
///
/// This trait provides common interfaces for `DedupVec`.
pub trait AsDedupVec {
    /// Vector item type.
    type Item;

    /// Vector type.
    type Container;

    /// Iterator yielding reference to `Item`.
    type Iter<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;

    /// Creates a new empty vector.
    fn new() -> Self;

    /// Returns the number of items.
    fn len(&self) -> usize;

    /// Returns true if the vector is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns true if the vector contains the given value.
    fn contains(&self, value: &Self::Item) -> bool;

    /// Appends the given value to the end of the vector.
    fn push(&mut self, value: Self::Item);

    /// Removes an item that is equal to the given value from the vector.
    fn remove(&mut self, value: &Self::Item) -> Option<Self::Item>;

    /// Extends the vector with the given iterator.
    fn extend(&mut self, iter: impl IntoIterator<Item = Self::Item>);

    /// Returns an iterator visiting all items in the vector.
    fn iter(&self) -> Self::Iter<'_>;
}

// ON = true means deduplication is activated.
//
// In this case, we keep the vector deduplicated whenever insertion or removal occurs.
impl<T> AsDedupVec for DedupVec<T, true>
where
    T: Ord,
{
    type Item = T;
    type Container = Vec<T>;
    type Iter<'a>
        = core::slice::Iter<'a, T>
    where
        Self: 'a;

    /// Creates a new empty vector.
    ///
    /// The vector automatically sorts and deduplicates items because `ON = true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<i32, true>::new();
    /// ```
    fn new() -> Self {
        DedupVec { inner: Vec::new() }
    }

    /// Returns the number of items.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.push(0);
    /// assert_eq!(v.len(), 1);
    /// ```
    fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the vector contains the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.push(0);
    /// assert!(v.contains(&0));
    /// ```
    fn contains(&self, value: &Self::Item) -> bool {
        self.inner.binary_search(value).is_ok()
    }

    /// Appends the given value to the end of the vector.
    ///
    /// The vector automatically sorts and deduplicates items because `ON = true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.push(0);
    /// v.push(0);
    /// v.push(2);
    /// v.push(1);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 1, 2]);
    /// ```
    fn push(&mut self, value: Self::Item) {
        if let Err(i) = self.inner.binary_search(&value) {
            self.inner.insert(i, value);
        }
    }

    /// Removes an item that is equal to the given value from the vector.
    ///
    /// The vector automatically sorts and deduplicates items because `ON = true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.push(0);
    /// v.push(2);
    /// v.push(1);
    /// v.remove(&1);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 2]);
    /// ```
    fn remove(&mut self, value: &Self::Item) -> Option<Self::Item> {
        if let Ok(i) = self.inner.binary_search(value) {
            Some(self.inner.remove(i))
        } else {
            None
        }
    }

    /// Extends the vector with the given iterator.
    ///
    /// The vector automatically sorts and deduplicates items because `ON = true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.extend([0, 2, 1]);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 1, 2]);
    /// ```
    fn extend(&mut self, iter: impl IntoIterator<Item = Self::Item>) {
        self.inner.extend(iter);
        self.inner.sort_unstable();
        self.inner.dedup();
    }

    /// Returns an iterator visiting all items in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, true>::new();
    /// v.push(0);
    /// v.push(1);
    /// for x in v.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    fn iter(&self) -> Self::Iter<'_> {
        self.inner.iter()
    }
}

// ON = false means deduplication is not activated.
//
// In release mode, we don't check for duplicates at all. Clients are responsible for keeping the
// deduplicated state.
#[cfg(not(debug_assertions))]
impl<T> AsDedupVec for DedupVec<T, false>
where
    T: hash::Hash + Eq + Clone,
{
    type Item = T;
    type Container = Vec<T>;
    type Iter<'a>
        = core::slice::Iter<'a, T>
    where
        Self: 'a;

    fn new() -> Self {
        Self { inner: Vec::new() }
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn contains(&self, value: &Self::Item) -> bool {
        self.inner.iter().any(|v| v == value)
    }

    fn push(&mut self, value: Self::Item) {
        self.inner.push(value);
    }

    fn remove(&mut self, value: &Self::Item) -> Option<Self::Item> {
        if let Some((i, _)) = self.inner.iter().enumerate().find(|(_, x)| *x == value) {
            Some(self.inner.swap_remove(i))
        } else {
            None
        }
    }

    fn extend(&mut self, iter: impl IntoIterator<Item = Self::Item>) {
        self.inner.extend(iter);
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.inner.iter()
    }
}

// ON = false means deduplication is not activated.
//
// However, in debug mode, this panics if the container gets duplicate items.
#[cfg(debug_assertions)]
impl<T> AsDedupVec for DedupVec<T, false>
where
    T: hash::Hash + Eq + Default + Clone,
{
    type Item = T;
    type Container = crate::ds::list::SetValueList<T, crate::FxBuildHasher>;
    type Iter<'a>
        = crate::ds::list::Values<'a, T, crate::FxBuildHasher>
    where
        Self: 'a;

    /// Creates a new empty vector.
    ///
    /// The vector doesn't preserve deduplicated status, but it panics when you insert a duplicate
    /// item in debug mode because `ON = false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<i32, false>::new();
    /// ```
    fn new() -> Self {
        Self {
            inner: crate::ds::list::SetValueList::default(),
        }
    }

    /// Returns the number of items.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.push(0);
    /// assert_eq!(v.len(), 1);
    /// ```
    fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the vector contains the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.push(0);
    /// assert!(v.contains(&0));
    /// ```
    fn contains(&self, value: &Self::Item) -> bool {
        self.inner.contains_key(value)
    }

    /// Appends the given value to the end of the vector.
    ///
    /// The vector doesn't preserve deduplicated status, but it panics when you insert a duplicate
    /// item in debug mode because `ON = false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.push(0);
    /// v.push(2);
    /// v.push(1);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 2, 1]);
    /// ```
    fn push(&mut self, value: Self::Item) {
        assert!(!self.contains(&value), "duplicate item detected",);

        self.inner.push_back(value);
    }

    /// Removes an item that is equal to the given value from the vector.
    ///
    /// The vector doesn't preserve deduplicated status, but it panics when you insert a duplicate
    /// item in debug mode because `ON = false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.push(0);
    /// v.push(1);
    /// v.push(2);
    /// v.remove(&1);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 2]);
    /// ```
    fn remove(&mut self, value: &Self::Item) -> Option<Self::Item> {
        self.inner.remove(value)
    }

    /// Extends the vector with the given iterator.
    ///
    /// The vector doesn't preserve deduplicated status, but it panics when you insert a duplicate
    /// item in debug mode because `ON = false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.extend([0, 2, 1]);
    /// let dedup = v.iter().cloned().collect::<Vec<_>>();
    /// assert_eq!(dedup, [0, 2, 1]);
    /// ```
    fn extend(&mut self, iter: impl IntoIterator<Item = Self::Item>) {
        for value in iter {
            self.push(value);
        }
    }

    /// Returns an iterator visiting all items in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{AsDedupVec, DedupVec};
    ///
    /// let mut v = DedupVec::<_, false>::new();
    /// v.push(0);
    /// v.push(1);
    /// for x in v.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    fn iter(&self) -> Self::Iter<'_> {
        self.inner.values()
    }
}

/// Deduplicated vector.
///
/// - If ON is true, the vector keeps a *sorted* and *deduplicated* status. It sorts and performs
///   binary searches whenever you insert or remove items. In this case, [`Vec`] is used as the data
///   container.
///
/// - If ON is false, on the other hand, the vector acts differently according to build mode.
///   * *debug mode* : The vector panics when duplication is detected.
///     [`SetValueList`](crate::ds::SetValueList) is used as the data container in this case. The
///     container keeps insertion order.
///   * *release mode* : The vector does nothing to keep deduplicated status. Clients must maintain
///     the status in their code. In this case, [`Vec`] is used as the data container.
///
/// # How to determine `ON`
///
/// If sorting is not a burden and you are going to insert or remove items in any order, set ON to
/// `true`. The vector will always keep deduplicated status.
///
/// If you can guarantee deduplicated status yourself, set ON to `false`. The vector will warn you
/// if the guarantee is broken in debug mode. In release mode, there are no additional operations,
/// avoiding a performance penalty.
#[repr(transparent)]
pub struct DedupVec<T, const ON: bool = true>
where
    Self: AsDedupVec,
{
    inner: <Self as AsDedupVec>::Container,
}

impl<T, const ON: bool> fmt::Debug for DedupVec<T, ON>
where
    Self: AsDedupVec,
    <Self as AsDedupVec>::Container: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DedupVec({:?})", self.inner)
    }
}

impl<T> From<DedupVec<T, true>> for Vec<T>
where
    T: Ord,
{
    fn from(value: DedupVec<T, true>) -> Self {
        value.inner
    }
}

#[cfg(not(debug_assertions))]
impl<T> From<DedupVec<T, false>> for Vec<T>
where
    T: hash::Hash + Eq + Clone,
{
    fn from(value: DedupVec<T, false>) -> Self {
        value.inner
    }
}

#[cfg(debug_assertions)]
impl<T> From<DedupVec<T, false>> for Vec<T>
where
    T: hash::Hash + Eq + Default + Clone,
{
    fn from(value: DedupVec<T, false>) -> Self {
        value.inner.into()
    }
}
