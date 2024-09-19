use crate::ds::prelude::*;
use crate::ecs::{
    ent::{
        component::{Component, ComponentKey, Components},
        entity::{EntityIndex, EntityTag},
    },
    sched::par,
};
use rayon::iter::{
    plumbing::{Consumer, Producer, ProducerCallback, UnindexedConsumer},
    IndexedParallelIterator, IntoParallelIterator, ParallelIterator,
};
use std::{
    any,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    rc::Rc,
    sync::atomic::AtomicI32,
};

/// A filter to select [`Component`] array.
/// You should fill out this form of filter.
///
/// - `Target` is what `Component` you want.
///   You will receive arrays of this `Target`.
///
/// - `All` is a tuple of `Component`s to select entities that have
///   all the `Component`s.
///   It's something like *AND* condition.
///   But if `All` is empty, then any entities won't be rejected.
///
/// - `Any` is a tuple of `Component`s to select entities that have
///   any of the `Component`s.
///   It's something like *OR* condition.
///   But if `Any` is empty, then any entities won't be rejected.
///
/// - `None` is a tuple of `Component`s not to select entities that have
///   any of these `Component`s.
///   It's something like *NOR* condition.
///   Buf if `None` is empty, then any entities won't be rejected.
pub trait Filter: 'static {
    type Target: Component;
    type All: Components;
    type Any: Components;
    type None: Components;

    fn ids() -> [Box<[ComponentKey]>; 3] {
        let all = <Self::All as Components>::keys().into_iter();
        let any = <Self::Any as Components>::keys().into_iter();
        let none = <Self::None as Components>::keys().into_iter();
        [all.collect(), any.collect(), none.collect()]
    }

    fn key() -> FilterKey {
        FilterKey::of::<Self>()
    }

    fn info<S>(info_stor: &mut S) -> Rc<FilterInfo>
    where
        S: StoreFilterInfo,
    {
        let key = Self::key();
        if let Some(info) = info_stor.get(&key) {
            info
        } else {
            let [all, any, none] = Self::ids();
            let info = Rc::new(FilterInfo {
                name: any::type_name::<Self>(),
                target: ComponentKey::of::<Self::Target>(),
                all,
                any,
                none,
            });
            info_stor.insert(key, &info);
            info
        }
    }
}

/// Disjoint filters mean that two filters' targets are not the same one.
/// Table below shows the disjoint conditions.
///
/// | Filter | Target | All   | None     | Any   |
/// | :---:  | :---:  | :---: | :---:    | :---: |
/// | FA     | T      | A, B  | C, D     | E, F  |
/// | FB     | U      | ..    | ..       | ..    | // Case 1
/// | FB     | T      | ..    | A, ..    | ..    | // Case 2
/// | FB     | T      | ..    | B, ..    | ..    | // Case 2
/// | FB     | T      | C, .. | ..       | ..    | // Case 3
/// | FB     | T      | D, .. | ..       | ..    | // Case 3
/// | FB     | T      | ..    | ..       | C     | // Case 4
/// | FB     | T      | ..    | ..       | D     | // Case 4
/// | FB     | T      | ..    | ..       | C, D  | // Case 4
/// | FB     | T      | ..    | E, F, .. | ..    | // Case 5
pub fn is_disjoint(a: &FilterInfo, b: &FilterInfo) -> bool {
    let a_target = a.target();
    let (a_all, a_any, a_none) = (a.all(), a.any(), a.none());
    let b_target = b.target();
    let (b_all, b_any, b_none) = (b.all(), b.any(), b.none());

    // Case 1. Different targets.
    if a_target != b_target {
        return true;
    }

    // Case 2. One of `FA's All` belongs to `FB's None`.
    if a_all.iter().any(|a| b_none.contains(a)) {
        return true;
    }

    // Case 3. One of `FA's None` belongs to `FB's All`.
    if a_none.iter().any(|a| b_all.contains(a)) {
        return true;
    }

    // Case 4. `FB's Any` is a subset of `FA's None`.
    if !b_any.is_empty() && b_any.iter().all(|b| a_none.contains(b)) {
        return true;
    }

    // Case 5. `FA's Any` is a subset of `FB's None`.
    if !a_any.is_empty() && a_any.iter().all(|a| b_none.contains(a)) {
        return true;
    }

    false
}

pub trait StoreFilterInfo {
    fn get(&self, key: &FilterKey) -> Option<Rc<FilterInfo>>;
    fn insert(&mut self, key: FilterKey, info: &Rc<FilterInfo>);
}

/// [`TypeId`] of a [`Filter`].
pub type FilterKey = ATypeId<FilterKey_>;
pub struct FilterKey_;

/// A Type that implemnts [`Filter`] can generate [`FilterInfo`],
/// which is a [`TypeId`] package of associated types of the `Filter`.
#[derive(Debug, Clone)]
pub struct FilterInfo {
    name: &'static str,
    target: ComponentKey,
    all: Box<[ComponentKey]>,
    any: Box<[ComponentKey]>,
    none: Box<[ComponentKey]>,
}

impl FilterInfo {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn target(&self) -> &ComponentKey {
        &self.target
    }

    pub fn all(&self) -> &[ComponentKey] {
        &self.all
    }

    pub fn any(&self) -> &[ComponentKey] {
        &self.any
    }

    pub fn none(&self) -> &[ComponentKey] {
        &self.none
    }

    pub fn filter<F>(&self, mut contains: F) -> bool
    where
        F: FnMut(&ComponentKey) -> bool,
    {
        // empty iter.all() -> returns true.
        // empty iter.any() -> returns false.

        contains(self.target())
            && self.all().iter().all(&mut contains)
            && !self.none().iter().any(&mut contains)
            && if self.any().is_empty() {
                true
            } else {
                self.any().iter().any(contains)
            }
    }
}

/// Filtered component arryas by a [Filter].  
/// This struct contains borrowed [Filter::Target] arrays.
/// But, this struct doesn't bring lifetime constraint into inside the struct.
/// although it borrows component arrays.
/// Instead, borrowed data are encapsulated by [Borrowed],
/// which is a run-time borrow checker.
/// In other words, component arrays must be borrowed and released everytime.
//
// This struct is intended to be used as a cache without lifetime.
// Cache is a data storage which lives as long as system data.
// But system data will live indefinitely,
// so removing lifetime helps to keep things simple.
#[derive(Debug)]
pub struct RawFiltered {
    /// [EntityTag] searched by the filter.
    //
    // TODO: Each system owns [RawFiltered], so etags and col_idxs will be duplicated between systems.
    etags: Vec<EntityTag>,

    /// Column(Component) index searched by the filter.
    //
    // TODO: Each system owns [RawFiltered], so etags and col_idxs will be duplicated between systems.
    col_idxs: Vec<usize>,

    /// Temporary buffer for the query result.
    /// Content will be replaced for every query, but we can reuse the capacity.
    /// Notice that this doesn't actually own [Borrowed] because this is just a temporary buffer.
    /// Real user, system, owns it and will drop it after using it.
    //
    // See `request::BufferCleaner` for more details.
    query_res: Vec<Borrowed<RawGetter, AtomicI32>>,
}

impl RawFiltered {
    pub(crate) const fn new(etags: Vec<EntityTag>, col_idxs: Vec<usize>) -> Self {
        Self {
            etags,
            col_idxs,
            query_res: Vec::new(),
        }
    }

    pub(crate) fn take(
        &mut self,
    ) -> (
        &Vec<EntityTag>,
        &Vec<usize>,
        &mut Vec<Borrowed<RawGetter, AtomicI32>>,
    ) {
        (&self.etags, &self.col_idxs, &mut self.query_res)
    }

    // By putting `etag` and `ci` in together, `Self::etags` and `Self::col_idxs` have the same length.
    pub(crate) fn add(&mut self, etag: EntityTag, ci: usize) {
        self.etags.push(etag);
        self.col_idxs.push(ci);
    }

    /// Retrieve an iterator that traverses over entity and column index pair.
    pub(crate) fn iter_index_pair<'a>(
        etags: &'a [EntityTag],
        col_idxs: &'a [usize],
    ) -> impl Iterator<Item = (EntityIndex, usize)> + 'a {
        // Self::add() guarantees that etags and col_idxs have the same length.
        etags
            .iter()
            .map(|etag| etag.index())
            .zip(col_idxs.iter().cloned())
    }

    pub(crate) fn clear(&mut self) {
        self.query_res.clear();
    }

    fn entity_tags(&self) -> &Vec<EntityTag> {
        &self.etags
    }

    fn query_res(&self) -> &Vec<Borrowed<RawGetter, AtomicI32>> {
        &self.query_res
    }
}

/// Shared references to [Filter::Target] componenet arrays from multiple entities.  
/// You can get an iterator traversing over each component array via [Self::iter].
/// A component array belongs to a specific entity.
#[derive(Debug)]
pub struct Filtered<'cont, Comp: 'cont> {
    /// A data structure holding borrowed component arrays and their entity tags.
    raw: &'cont mut RawFiltered,

    /// Holds component type.
    _marker: PhantomData<Comp>,
}

impl<'cont, Comp> Filtered<'cont, Comp> {
    /// Creates [Filtered] from mutable reference to a [RawFiltered].
    /// [RawFiltered] is not a container, but it's borrowing container's data,
    /// and holding them inside [Borrowed]s.
    /// So we can think lifetime to the '&mut [RawFiltered]' is as if container's.
    pub(crate) fn new(raw: &'cont mut RawFiltered) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    pub fn iter(&self) -> FilteredIter<'cont, Comp> {
        FilteredIter::new(self)
    }

    pub fn par_iter(&self) -> ParFilteredIter<'cont, Comp> {
        self.iter().into_par()
    }
}

impl<'cont, Comp> Deref for Filtered<'cont, Comp> {
    type Target = RawFiltered;

    fn deref(&self) -> &Self::Target {
        self.raw
    }
}

/// Mutable references to filtered component arrays from multiple entities.  
/// You can get an iterator traversing over each component array
/// via [Self::iter] or [Self::iter_mut].
/// A component array belongs to a specific entity.
//
// [Filtered] has mutable reference to a [RawFiltered] in it.
// So we can make use of it and expose mutable methods to clients here.
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredMut<'cont, Comp>(Filtered<'cont, Comp>);

impl<'cont, Comp> FilteredMut<'cont, Comp> {
    pub(crate) fn new(filtered: &'cont mut RawFiltered) -> Self {
        Self(Filtered::new(filtered))
    }

    pub fn iter(&self) -> FilteredIter<'cont, Comp> {
        FilteredIter::new(&self.0)
    }

    pub fn iter_mut(&mut self) -> FilteredIterMut<'cont, Comp> {
        FilteredIterMut::new(self.iter())
    }
}

#[derive(Debug, Clone)]
pub struct FilteredIter<'cont, Comp: 'cont> {
    getter_cur: SendSyncPtr<Borrowed<RawGetter, AtomicI32>>,

    getter_end: SendSyncPtr<Borrowed<RawGetter, AtomicI32>>,

    etag_cur: SendSyncPtr<EntityTag>,

    etag_end: SendSyncPtr<EntityTag>,

    _marker: PhantomData<&'cont Comp>,
}

impl<'cont, Comp> FilteredIter<'cont, Comp> {
    // Borrows `Filtered`.
    fn new(raw: &Filtered<Comp>) -> Self {
        // Safety: `Filtered` guarantees we're good to access those vecs.
        unsafe {
            let getter_range = raw.query_res().as_ptr_range();
            let getter_cur = NonNull::new_unchecked(getter_range.start.cast_mut());
            let getter_end = NonNull::new_unchecked(getter_range.end.cast_mut());

            let etag_range = raw.entity_tags().as_ptr_range();
            let etag_cur = NonNull::new_unchecked(etag_range.start.cast_mut());
            let etag_end = NonNull::new_unchecked(etag_range.end.cast_mut());

            Self {
                getter_cur: SendSyncPtr::new(getter_cur),
                getter_end: SendSyncPtr::new(getter_end),
                etag_cur: SendSyncPtr::new(etag_cur),
                etag_end: SendSyncPtr::new(etag_end),
                _marker: PhantomData,
            }
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        let end = self.getter_end.as_ptr();
        let cur = self.getter_cur.as_ptr();
        unsafe { end.offset_from(cur) as usize }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn into_par(self) -> ParFilteredIter<'cont, Comp> {
        ParFilteredIter(self)
    }

    unsafe fn create_item(
        getter: SendSyncPtr<Borrowed<RawGetter, AtomicI32>>,
        etag: SendSyncPtr<EntityTag>,
    ) -> TaggedGetter<'cont, Comp> {
        let raw = **getter.as_ref();
        let getter = Getter::from_raw(raw);
        let etag = NonNullExt::from_nonnull(etag.as_nonnull());
        let etag = ManagedConstPtr::new(etag);
        TaggedGetter { getter, etag }
    }
}

impl<'cont, Comp> Iterator for FilteredIter<'cont, Comp> {
    type Item = TaggedGetter<'cont, Comp>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.getter_cur < self.getter_end {
            let getter = self.getter_cur;
            let etag = self.etag_cur;
            unsafe {
                self.getter_cur = self.getter_cur.add(1);
                self.etag_cur = self.etag_cur.add(1);
                Some(Self::create_item(getter, etag))
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'cont, Comp> ExactSizeIterator for FilteredIter<'cont, Comp> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'cont, Comp> DoubleEndedIterator for FilteredIter<'cont, Comp> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.getter_cur < self.getter_end {
            unsafe {
                self.getter_end = self.getter_cur.sub(1);
                self.etag_end = self.etag_cur.sub(1);
                Some(Self::create_item(self.getter_end, self.etag_end))
            }
        } else {
            None
        }
    }
}

/// Parallel [`FilteredIter`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ParFilteredIter<'cont, Comp: 'cont>(FilteredIter<'cont, Comp>);

impl<'cont, Comp> ParFilteredIter<'cont, Comp> {
    pub const fn into_seq(self) -> FilteredIter<'cont, Comp> {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'cont, Comp> Deref for ParFilteredIter<'cont, Comp> {
    type Target = FilteredIter<'cont, Comp>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'cont, Comp> DerefMut for ParFilteredIter<'cont, Comp> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'cont, Comp: Send + Sync> ParallelIterator for ParFilteredIter<'cont, Comp> {
    type Item = TaggedGetter<'cont, Comp>;

    #[inline]
    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        par::bridge(self, consumer)
    }
}

impl<'cont, Comp: Send + Sync> IndexedParallelIterator for ParFilteredIter<'cont, Comp> {
    #[inline]
    fn len(&self) -> usize {
        Self::len(self)
    }

    #[inline]
    fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
        par::bridge(self, consumer)
    }

    #[inline]
    fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
        callback.callback(self)
    }
}

impl<'cont, Comp: Send + Sync> Producer for ParFilteredIter<'cont, Comp> {
    type Item = TaggedGetter<'cont, Comp>;
    type IntoIter = FilteredIter<'cont, Comp>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.into_seq()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let l_getter_cur = self.getter_cur;
        let l_getter_end = unsafe { self.getter_cur.add(index) };
        let r_getter_cur = l_getter_end;
        let r_getter_end = self.getter_end;

        let l_etag_cur = self.etag_cur;
        let l_etag_end = unsafe { self.etag_cur.add(index) };
        let r_etag_cur = l_etag_end;
        let r_etag_end = self.etag_end;

        let l = FilteredIter {
            getter_cur: l_getter_cur,
            getter_end: l_getter_end,
            etag_cur: l_etag_cur,
            etag_end: l_etag_end,
            _marker: PhantomData,
        };
        let r = FilteredIter {
            getter_cur: r_getter_cur,
            getter_end: r_getter_end,
            etag_cur: r_etag_cur,
            etag_end: r_etag_end,
            _marker: PhantomData,
        };
        (l.into_par(), r.into_par())
    }
}

// Mutable iterator is not clonable.
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredIterMut<'cont, Comp: 'cont>(FilteredIter<'cont, Comp>);

impl<'cont, Comp> FilteredIterMut<'cont, Comp> {
    const fn new(inner: FilteredIter<'cont, Comp>) -> Self {
        Self(inner)
    }
}

impl<'cont, Comp> Iterator for FilteredIterMut<'cont, Comp> {
    type Item = TaggedGetterMut<'cont, Comp>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|TaggedGetter { getter, etag }| {
            TaggedGetterMut {
                // Safety: `GetterMut` is made from `Getter`,
                // which proves it's `RawGetter` and type are valid.
                getter: unsafe { GetterMut::from_raw(getter.into_raw()) },
                etag,
            }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'cont, Comp> ExactSizeIterator for FilteredIterMut<'cont, Comp> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'cont, Comp> DoubleEndedIterator for FilteredIterMut<'cont, Comp> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|TaggedGetter { getter, etag }| {
            TaggedGetterMut {
                // Safety: `GetterMut` is made from `Getter`,
                // which proves it's `RawGetter` and type are valid.
                getter: unsafe { GetterMut::from_raw(getter.into_raw()) },
                etag,
            }
        })
    }
}

/// Component getter with entity tag.
///
/// * Component getter  
///   A component getter corresponds to a component array.
///   You can get each component inside component array via getter.
///   See [`Getter`] for more details.
///
/// * Entity tag  
///   Many entities may contain the same component type.
///   So, it's needed to know what entity this component belongs to.
///   Entity tag has entity identification such as entity name.
#[derive(Debug, Clone)]
pub struct TaggedGetter<'cont, Comp: 'cont> {
    getter: Getter<'cont, Comp>,
    etag: ManagedConstPtr<EntityTag>,
}

impl<'cont, Comp> TaggedGetter<'cont, Comp> {
    pub fn entity_index(&self) -> EntityIndex {
        self.etag.index()
    }

    pub fn entity_name(&self) -> &str {
        self.etag.name()
    }

    pub fn component_keys(&self) -> &[ComponentKey] {
        self.etag.comp_keys()
    }

    pub fn component_names(&self) -> &[&'static str] {
        self.etag.comp_names()
    }
}

impl<'cont, Comp> Deref for TaggedGetter<'cont, Comp> {
    type Target = Getter<'cont, Comp>;

    fn deref(&self) -> &Self::Target {
        &self.getter
    }
}

impl<'cont, Comp> IntoIterator for TaggedGetter<'cont, Comp> {
    type Item = &'cont Comp;
    type IntoIter = FlatIter<'cont, Comp>;

    fn into_iter(self) -> Self::IntoIter {
        self.getter.into_iter()
    }
}

impl<'cont, Comp: Send + Sync> IntoParallelIterator for TaggedGetter<'cont, Comp> {
    type Item = &'cont Comp;
    type Iter = ParFlatIter<'cont, Comp>;

    fn into_par_iter(self) -> Self::Iter {
        self.getter.into_par_iter()
    }
}

/// Component getter with entity tag.
///
/// * Component getter  
///   A component getter corresponds to a component array.
///   You can get each component inside component array via getter.
///   See [`GetterMut`] for more details.
///
/// * Entity tag  
///   Many entities may contain the same component type.
///   So, it's needed to know what entity this component belongs to.
///   Entity tag has entity identification such as entity name.
#[derive(Debug)]
pub struct TaggedGetterMut<'cont, Comp: 'cont> {
    getter: GetterMut<'cont, Comp>,
    etag: ManagedConstPtr<EntityTag>,
}

impl<'cont, Comp> TaggedGetterMut<'cont, Comp> {
    pub fn entity_index(&self) -> EntityIndex {
        self.etag.index()
    }

    pub fn entity_name(&self) -> &str {
        self.etag.name()
    }

    pub fn component_keys(&self) -> &[ComponentKey] {
        self.etag.comp_keys()
    }

    pub fn component_names(&self) -> &[&'static str] {
        self.etag.comp_names()
    }
}

impl<'cont, Comp> Deref for TaggedGetterMut<'cont, Comp> {
    type Target = GetterMut<'cont, Comp>;

    fn deref(&self) -> &Self::Target {
        &self.getter
    }
}

impl<'cont, Comp> DerefMut for TaggedGetterMut<'cont, Comp> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.getter
    }
}

impl<'cont, Comp> IntoIterator for TaggedGetterMut<'cont, Comp> {
    type Item = &'cont mut Comp;
    type IntoIter = FlatIterMut<'cont, Comp>;

    fn into_iter(self) -> Self::IntoIter {
        self.getter.into_iter()
    }
}

impl<'cont, Comp: Send + Sync> IntoParallelIterator for TaggedGetterMut<'cont, Comp> {
    type Item = &'cont mut Comp;
    type Iter = ParFlatIterMut<'cont, Comp>;

    fn into_par_iter(self) -> Self::Iter {
        self.getter.into_par_iter()
    }
}
