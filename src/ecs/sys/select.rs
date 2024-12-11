use crate::ds::prelude::*;
use crate::ecs::ent::{
    component::{Component, ComponentKey, Components},
    entity::{EntityIndex, EntityName, EntityTag},
};
use crate::{impl_into_iterator_for_parallel, impl_parallel_iterator, impl_unindexed_producer};
use rayon::iter::{plumbing::Producer, IntoParallelIterator};
use std::{
    any,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
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
pub trait Select: 'static {
    type Target: Component;
    type All: Components;
    type Any: Components;
    type None: Components;

    fn all_any_none() -> [Box<[ComponentKey]>; 3] {
        let all: Box<[ComponentKey]> = Self::All::keys().as_ref().into();
        let any: Box<[ComponentKey]> = Self::Any::keys().as_ref().into();
        let none: Box<[ComponentKey]> = Self::None::keys().as_ref().into();
        [all, any, none]
    }

    fn key() -> SelectKey {
        SelectKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<SelectInfo>
    where
        S: StoreSelectInfo + ?Sized,
    {
        let key = Self::key();

        if !stor.contains(&key) {
            let sinfo = Arc::new(Self::info());
            stor.insert(key, sinfo);
        }

        // Safety: Inserted right before.
        unsafe { stor.get(&key).unwrap_unchecked() }
    }

    fn info() -> SelectInfo {
        let [all, any, none] = Self::all_any_none();
        SelectInfo {
            name: any::type_name::<Self>(),
            target: ComponentKey::of::<Self::Target>(),
            all,
            any,
            none,
        }
    }
}

/// Disjoint selectors mean that two selectors' targets are not the same one.
/// Table below shows the disjoint conditions.
///
/// | Select | Target | All   | None     | Any   |
/// | :---:  | :---:  | :---: | :---:    | :---: |
/// | SA     | T      | A, B  | C, D     | E, F  |
/// | SB     | U      | ..    | ..       | ..    | // Case 1
/// | SB     | T      | ..    | A, ..    | ..    | // Case 2
/// | SB     | T      | ..    | B, ..    | ..    | // Case 2
/// | SB     | T      | C, .. | ..       | ..    | // Case 3
/// | SB     | T      | D, .. | ..       | ..    | // Case 3
/// | SB     | T      | ..    | ..       | C     | // Case 4
/// | SB     | T      | ..    | ..       | D     | // Case 4
/// | SB     | T      | ..    | ..       | C, D  | // Case 4
/// | SB     | T      | ..    | E, F, .. | ..    | // Case 5
pub fn is_disjoint(a: &SelectInfo, b: &SelectInfo) -> bool {
    let a_target = a.target();
    let (a_all, a_any, a_none) = (a.all(), a.any(), a.none());
    let b_target = b.target();
    let (b_all, b_any, b_none) = (b.all(), b.any(), b.none());

    // Case 1. Different targets.
    if a_target != b_target {
        return true;
    }

    // Case 2. One of `SA's All` belongs to `SB's None`.
    if a_all.iter().any(|a| b_none.contains(a)) {
        return true;
    }

    // Case 3. One of `SA's None` belongs to `SB's All`.
    if a_none.iter().any(|a| b_all.contains(a)) {
        return true;
    }

    // Case 4. `SB's Any` is a subset of `SA's None`.
    if !b_any.is_empty() && b_any.iter().all(|b| a_none.contains(b)) {
        return true;
    }

    // Case 5. `SA's Any` is a subset of `SB's None`.
    if !a_any.is_empty() && a_any.iter().all(|a| b_none.contains(a)) {
        return true;
    }

    false
}

pub trait StoreSelectInfo {
    fn contains(&self, key: &SelectKey) -> bool;
    fn get(&self, key: &SelectKey) -> Option<&Arc<SelectInfo>>;
    fn insert(&mut self, key: SelectKey, info: Arc<SelectInfo>);
}

/// Unique identifier for a type implementing [`Select`].
pub type SelectKey = ATypeId<SelectKey_>;
pub struct SelectKey_;

/// Unique identifier for a type implementing [`Filter`].
pub type FilterKey = ATypeId<FilterKey_>;
pub struct FilterKey_;

#[derive(Debug, Clone)]
pub struct SelectInfo {
    name: &'static str,
    target: ComponentKey,
    all: Box<[ComponentKey]>,
    any: Box<[ComponentKey]>,
    none: Box<[ComponentKey]>,
}

impl SelectInfo {
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

/// Selected component arryas by a [`Select`].  
///
// This struct contains borrowed `Select::Target` arrays. But, this struct
// doesn't bring lifetime constraint into inside the struct although it
// borrows component arrays. Instead, borrowed data are encapsulated by
// `Borrowed`, which is a run-time borrow checker. In other words, component
// arrays must be borrowed and released everytime.
//
// This struct is intended to be used as a cache without lifetime.
// Cache is a data storage which lives as long as system data.
// But system data will live indefinitely,
// so removing lifetime helps to keep things simple.
#[derive(Debug)]
pub struct SelectedRaw {
    /// [EntityTag] searched by the filter.
    //
    // Each system owns `SelectedRaw`, so `etags` and `col_idxs` will be
    // duplicated between systems.
    etags: Vec<EntityTag>,

    /// Column(Component) index searched by the filter.
    //
    // Each system owns `SelectedRaw`, so `etags` and `col_idxs` will be
    // duplicated between systems.
    col_idxs: Vec<usize>,

    /// Temporary buffer for the query result.
    /// Content will be replaced for every query, but we can reuse the capacity.
    /// Notice that this doesn't actually own [Borrowed] because this is just a temporary buffer.
    /// Real user, system, owns it and will drop it after using it.
    //
    // See `request::BufferCleaner` for more details.
    query_res: Vec<Borrowed<RawGetter>>,
}

impl SelectedRaw {
    pub(crate) const fn new(etags: Vec<EntityTag>, col_idxs: Vec<usize>) -> Self {
        Self {
            etags,
            col_idxs,
            query_res: Vec::new(),
        }
    }

    pub(crate) fn take(&mut self) -> (&Vec<EntityTag>, &Vec<usize>, &mut Vec<Borrowed<RawGetter>>) {
        (&self.etags, &self.col_idxs, &mut self.query_res)
    }

    // `etags` and `col_idxs` always have the same length.
    pub(crate) fn add(&mut self, etag: EntityTag, ci: usize) {
        self.etags.push(etag);
        self.col_idxs.push(ci);
    }

    // `etags` and `col_idxs` always have the same length.
    pub(crate) fn remove(&mut self, ci: usize) -> Option<EntityTag> {
        if let Some((i, _)) = self.col_idxs.iter().enumerate().find(|(_, &x)| x == ci) {
            let old = self.etags.swap_remove(i);
            self.col_idxs.swap_remove(i);
            Some(old)
        } else {
            None
        }
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

    pub(crate) fn query_res(&self) -> &Vec<Borrowed<RawGetter>> {
        &self.query_res
    }

    fn entity_tags(&self) -> &Vec<EntityTag> {
        &self.etags
    }
}

/// Shared references to [`Select::Target`] componenet arrays from multiple
/// entities. You can get an iterator traversing over each component array via
/// [`iter`](Self::iter). A component array belongs to a specific entity.
#[derive(Debug)]
pub struct Selected<'cont, Comp: 'cont> {
    /// A struct holding borrowed component arrays and their entity tags.
    raw: &'cont mut SelectedRaw,

    /// Holds component type.
    _marker: PhantomData<Comp>,
}

impl<'cont, Comp: 'cont> Selected<'cont, Comp> {
    /// Creates [`Selected`] from a mutable reference to a [`SelectedRaw`].
    /// [`SelectedRaw`] is not a container, but it's borrowing container's data,
    /// and holding them inside [`Borrowed`]s. So we can think lifetime to the
    /// '&mut [`SelectedRaw`]' is as if container's.
    pub(crate) fn new(raw: &'cont mut SelectedRaw) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    pub fn iter(&self) -> SelectedIter<'cont, Comp> {
        SelectedIter::new(self)
    }

    pub fn par_iter(&self) -> ParSelectedIter<'cont, Comp> {
        ParSelectedIter(self.iter())
    }
}

impl<Comp> Deref for Selected<'_, Comp> {
    type Target = SelectedRaw;

    fn deref(&self) -> &Self::Target {
        self.raw
    }
}

/// Mutable references to [`Select::Target`] component arrays from multiple
/// entities.  You can get an iterator traversing over each component array via
/// [`iter`](Self::iter) or [`iter_mut`](Self::iter_mut). A component array
/// belongs to a specific entity.
//
// `Selected` has mutable reference to a `SelectedRaw` in it.
// So we can make use of it and expose mutable methods to clients here.
#[derive(Debug)]
#[repr(transparent)]
pub struct SelectedMut<'cont, Comp>(Selected<'cont, Comp>);

impl<'cont, Comp: 'cont> SelectedMut<'cont, Comp> {
    pub(crate) fn new(filtered: &'cont mut SelectedRaw) -> Self {
        Self(Selected::new(filtered))
    }

    pub fn iter(&self) -> SelectedIter<'cont, Comp> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> SelectedIterMut<'cont, Comp> {
        SelectedIterMut(self.iter())
    }

    pub fn par_iter(&self) -> ParSelectedIter<'cont, Comp> {
        self.0.par_iter()
    }

    pub fn par_iter_mut(&mut self) -> ParSelectedIterMut<'cont, Comp> {
        ParSelectedIterMut(self.iter_mut())
    }
}

#[derive(Debug, Clone)]
pub struct SelectedIter<'cont, Comp> {
    getter_cur: SendSyncPtr<Borrowed<RawGetter>>,

    getter_end: SendSyncPtr<Borrowed<RawGetter>>,

    etag_cur: SendSyncPtr<EntityTag>,

    etag_end: SendSyncPtr<EntityTag>,

    _marker: PhantomData<&'cont Comp>,
}

impl<'cont, Comp: 'cont> SelectedIter<'cont, Comp> {
    // Borrows `Selected`.
    fn new(raw: &Selected<'cont, Comp>) -> Self {
        // Safety: `Selected` guarantees we're good to access those vecs.
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
    fn split_at(self, index: usize) -> (Self, Self) {
        let l_getter_cur = self.getter_cur;
        let l_getter_end = unsafe { self.getter_cur.add(index) };
        let r_getter_cur = l_getter_end;
        let r_getter_end = self.getter_end;

        let l_etag_cur = self.etag_cur;
        let l_etag_end = unsafe { self.etag_cur.add(index) };
        let r_etag_cur = l_etag_end;
        let r_etag_end = self.etag_end;

        let l = SelectedIter {
            getter_cur: l_getter_cur,
            getter_end: l_getter_end,
            etag_cur: l_etag_cur,
            etag_end: l_etag_end,
            _marker: PhantomData,
        };
        let r = SelectedIter {
            getter_cur: r_getter_cur,
            getter_end: r_getter_end,
            etag_cur: r_etag_cur,
            etag_end: r_etag_end,
            _marker: PhantomData,
        };
        (l, r)
    }

    unsafe fn create_item(
        getter: SendSyncPtr<Borrowed<RawGetter>>,
        etag: SendSyncPtr<EntityTag>,
    ) -> TaggedGetter<'cont, Comp> {
        let raw = **getter.as_ref();
        let getter = Getter::from_raw(raw);
        let etag = NonNullExt::from_nonnull(etag.as_nonnull());
        let etag = ManagedConstPtr::new(etag);
        TaggedGetter { getter, etag }
    }
}

impl<'cont, Comp: 'cont> Iterator for SelectedIter<'cont, Comp> {
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

impl<'cont, Comp: 'cont> ExactSizeIterator for SelectedIter<'cont, Comp> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'cont, Comp: 'cont> DoubleEndedIterator for SelectedIter<'cont, Comp> {
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

/// Parallel [`SelectedIter`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ParSelectedIter<'cont, Comp>(pub SelectedIter<'cont, Comp>);

impl<'cont, Comp: 'cont> ParSelectedIter<'cont, Comp> {
    #[inline]
    pub const fn into_seq(self) -> SelectedIter<'cont, Comp> {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'cont, Comp: Send + Sync + 'cont> Producer for ParSelectedIter<'cont, Comp> {
    type Item = TaggedGetter<'cont, Comp>;
    type IntoIter = SelectedIter<'cont, Comp>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.into_seq()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let (l, r) = SelectedIter::split_at(self.0, index);
        (ParSelectedIter(l), ParSelectedIter(r))
    }
}

impl_into_iterator_for_parallel!(
    "lifetimes" = 'cont; "bounds" = Comp: {'cont};
    "for" = ParSelectedIter; "to" = SelectedIter<'cont, Comp>;
    "item" = TaggedGetter<'cont, Comp>;
);
impl_parallel_iterator!(
    "lifetimes" = 'cont; "bounds" = Comp: {Send + Sync + 'cont};
    "for" = ParSelectedIter; "item" = TaggedGetter<'cont, Comp>;
);
impl_unindexed_producer!(
    "lifetimes" = 'cont; "bounds" = Comp: {Send + Sync + 'cont};
    "for" = ParSelectedIter; "item" = TaggedGetter<'cont, Comp>;
);

// Mutable iterator is not clonable.
#[derive(Debug)]
#[repr(transparent)]
pub struct SelectedIterMut<'cont, Comp>(pub SelectedIter<'cont, Comp>);

impl<'cont, Comp: 'cont> SelectedIterMut<'cont, Comp> {
    #[inline]
    pub const fn into_seq(self) -> SelectedIter<'cont, Comp> {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let (l, r) = SelectedIter::split_at(self.0, index);
        (Self(l), Self(r))
    }
}

impl<'cont, Comp> Iterator for SelectedIterMut<'cont, Comp> {
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

impl<'cont, Comp: 'cont> ExactSizeIterator for SelectedIterMut<'cont, Comp> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'cont, Comp: 'cont> DoubleEndedIterator for SelectedIterMut<'cont, Comp> {
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

/// Parallel [`SelectedIterMut`].
//
// `Iterator` and `ParallelIterator` have the same signature methods,
// So clients have to write fully-qualified syntax to specify methods.
// This new type helps clients avoid it.
#[derive(Debug)]
#[repr(transparent)]
pub struct ParSelectedIterMut<'cont, Comp>(pub SelectedIterMut<'cont, Comp>);

impl<'cont, Comp: 'cont> ParSelectedIterMut<'cont, Comp> {
    #[inline]
    pub const fn into_seq(self) -> SelectedIterMut<'cont, Comp> {
        self.0
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'cont, Comp: Send + Sync> Producer for ParSelectedIterMut<'cont, Comp> {
    type Item = TaggedGetterMut<'cont, Comp>;
    type IntoIter = SelectedIterMut<'cont, Comp>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.into_seq()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let (l, r) = SelectedIterMut::split_at(self.0, index);
        (ParSelectedIterMut(l), ParSelectedIterMut(r))
    }
}

impl_into_iterator_for_parallel!(
    "lifetimes" = 'cont; "bounds" = Comp: {'cont};
    "for" = ParSelectedIterMut; "to" = SelectedIterMut<'cont, Comp>;
    "item" = TaggedGetterMut<'cont, Comp>;
);
impl_parallel_iterator!(
    "lifetimes" = 'cont; "bounds" = Comp: {Send + Sync + 'cont};
    "for" = ParSelectedIterMut; "item" = TaggedGetterMut<'cont, Comp>;
);
impl_unindexed_producer!(
    "lifetimes" = 'cont; "bounds" = Comp: {Send + Sync + 'cont};
    "for" = ParSelectedIterMut; "item" = TaggedGetterMut<'cont, Comp>;
);

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

impl<Comp> TaggedGetter<'_, Comp> {
    pub fn entity_index(&self) -> EntityIndex {
        self.etag.index()
    }

    pub fn entity_name(&self) -> Option<&EntityName> {
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

impl<Comp> TaggedGetterMut<'_, Comp> {
    pub fn entity_index(&self) -> EntityIndex {
        self.etag.index()
    }

    pub fn entity_name(&self) -> Option<&EntityName> {
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

impl<Comp> DerefMut for TaggedGetterMut<'_, Comp> {
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
