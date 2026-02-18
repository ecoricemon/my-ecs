//! Provides [`ContainEntity`] implementations.
//!
//! Currently, there are two options.
//!
//! - [`SparseSet`] based on [`AnyVec`], which stores data serially. It's good for traversing items,
//!   but requires copy when the vector needs to extend its capacity.
//!
//! - [`ChunkSparseSet`] based on [`ChunkAnyVec`], which stores data in chunks. Chunk is a fixed
//!   sized memory, and the vector appends a chunk when it needs more capacity. Therefore,
//!   `ChunkSparseSet` is good for frequent insertion or removal, but not good as mush as
//!   `SparseSet` in terms of traversing items.

use crate::{
    ecs::ent::entity::{AddEntity, BorrowComponent, ContainEntity, RegisterComponent},
    FxBuildHasher,
};
use my_utils::ds::{
    AnyVec, AsFlatRawIter, BorrowError, BorrowResult, ChunkAnyVec, FlatRawIter, Holder, OptVec,
    RawGetter, TypeInfo,
};
use std::{any::TypeId, collections::HashMap, fmt::Debug, hash::BuildHasher, mem, ptr::NonNull};

/// Two-dimensional storage containing heterogeneous data types based on [`ChunkAnyVec`].
///
/// Unlike `SparseSet`, this struct stores data in chunks. Chunk is a fixed sized memory, and it's
/// appended when extra capacity is needed. This chunk based capacity control removes data copy that
/// is seen from normal vector, but note that it brings inefficiency in terms of iteration.
///
/// See [`SparseSet`] for more details.
#[derive(Debug)]
pub struct ChunkSparseSet<S = FxBuildHasher> {
    sparse: OptVec<usize, S>,
    deref: Vec<usize>,
    cols: Vec<ChunkColumn>,
    map: HashMap<TypeId, usize, S>,
}

impl ChunkSparseSet {
    /// Creates a new empty [`ChunkSparseSet`] with [`FxBuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// let mut cont = ChunkSparseSet::new();
    /// ```
    pub fn new() -> Self {
        Self {
            sparse: OptVec::new(),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::with_hasher(FxBuildHasher::default()),
        }
    }
}

impl<S> ChunkSparseSet<S> {
    #[allow(unused)]
    const CHUNK_SIZE: usize = ChunkColumn::CHUNK_SIZE;
    #[allow(unused)]
    const MIN_CHUNK_LEN: usize = ChunkColumn::MIN_CHUNK_LEN;

    /// Creates a new empty [`ChunkSparseSet`] with the given hasher.
    pub fn with_hasher<F: FnMut() -> S>(mut hasher: F) -> Self {
        Self {
            sparse: OptVec::with_hasher(hasher()),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::with_hasher(hasher()),
        }
    }
}

impl<S> ContainEntity for ChunkSparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn create_twin(&self) -> Box<dyn ContainEntity> {
        // Creates new `Holder`s for the same types.
        let cols = self
            .cols
            .iter()
            .map(|col| unsafe { col.create_twin() })
            .collect::<Vec<_>>();

        // We can reuse mapping information.
        let map = self.map.clone();

        // Makes empty instance.
        let this = Self {
            sparse: OptVec::default(),
            deref: Vec::new(),
            cols,
            map,
        };
        Box::new(this)
    }

    fn get_item_mut(&mut self, ci: usize, ri: usize) -> Option<NonNull<u8>> {
        let index = *self.sparse.get(ri)?;
        let col = self.cols.get_mut(ci)?;
        unsafe { col.get_raw(index) }
    }

    fn len(&self) -> usize {
        // All columns must have the same length.
        self.cols
            .first()
            .map(|col| unsafe { col.len() })
            .unwrap_or_default()
    }

    fn capacity(&self) -> usize {
        // All columns must have the same length.
        self.cols
            .first()
            .map(|col| unsafe { col.capacity() })
            .unwrap_or_default()
    }

    fn reserve(&mut self, additional: usize) {
        for col in self.cols.iter_mut() {
            unsafe { col.reserve(additional) }
        }
    }

    fn shrink_to_fit(&mut self) {
        for col in self.cols.iter_mut() {
            unsafe { col.shrink_to_fit() }
        }
    }

    unsafe fn resize_column(&mut self, ci: usize, new_len: usize, val_ptr: NonNull<u8>) {
        self.cols[ci].resize_raw(new_len, val_ptr)
    }
}

impl<S> RegisterComponent for ChunkSparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    /// Adds a new column and returns column index.
    fn add_column(&mut self, tinfo: TypeInfo) -> Option<usize> {
        let ty = tinfo.ty;
        if self.len() > 0 || self.get_column_index(&ty).is_some() {
            return None;
        }

        let col = ChunkColumn::new(tinfo);
        self.cols.push(col);

        let ci = self.cols.len() - 1;
        self.map.insert(ty, ci);
        Some(ci)
    }

    fn remove_column(&mut self, ci: usize) -> Option<TypeInfo> {
        if self.cols.get(ci)?.borrow_count() > 0 {
            return None;
        }

        let old = self.cols.remove(ci);

        // Re-mapping
        for i in ci..self.cols.len() {
            // Safety: Index checked.
            let col = unsafe { self.cols.get_unchecked(i) };
            let ty = unsafe { col.item_type_info().ty };
            *self.map.get_mut(&ty).unwrap() = i;
        }

        // If empty, initialize self completely.
        if self.cols.is_empty() {
            mem::take(self);
        }

        let tinfo = unsafe { *old.item_type_info() };
        Some(tinfo)
    }

    fn get_column_index(&self, ty: &TypeId) -> Option<usize> {
        self.map.get(ty).cloned()
    }

    fn get_column_info(&self, ci: usize) -> Option<&TypeInfo> {
        self.cols.get(ci).map(|col| unsafe { col.item_type_info() })
    }

    fn num_columns(&self) -> usize {
        self.cols.len()
    }

    fn contains_column(&self, ty: &TypeId) -> bool {
        self.map.contains_key(ty)
    }
}

impl<S> BorrowComponent for ChunkSparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn borrow_column(&self, ci: usize) -> BorrowResult<RawGetter> {
        #[cfg(feature = "check")]
        let this_len = self.len();

        if let Some(col) = self.cols.get(ci) {
            let borrowed = col.borrow();

            // Validates length.
            #[cfg(feature = "check")]
            {
                if let Ok(borrowed) = borrowed.as_ref() {
                    assert_eq!(
                        this_len,
                        borrowed.len(),
                        "borrowed column must have the same length as entity container's"
                    );
                }
            }

            borrowed
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    fn borrow_column_mut(&mut self, ci: usize) -> BorrowResult<RawGetter> {
        #[cfg(feature = "check")]
        let this_len = self.len();

        if let Some(col) = self.cols.get_mut(ci) {
            let borrowed = col.borrow_mut();

            // Validates length.
            #[cfg(feature = "check")]
            {
                if let Ok(borrowed) = borrowed.as_ref() {
                    assert_eq!(
                        this_len,
                        borrowed.len(),
                        "borrowed column must have the same length as entity container's"
                    );
                }
            }

            borrowed
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    unsafe fn get_column(&self, ci: usize) -> Option<NonNull<u8>> {
        self.cols.get(ci).map(|col| col.ptr_vec().cast())
    }
}

impl<S> AddEntity for ChunkSparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn to_value_index(&self, ri: usize) -> Option<usize> {
        self.sparse.get(ri).cloned()
    }

    fn begin_add_row(&mut self) {}

    unsafe fn add_value(&mut self, ci: usize, val_ptr: NonNull<u8>) {
        // No panic for now.
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.push_raw(val_ptr);
        }
    }

    unsafe fn end_add_row(&mut self) -> usize {
        let vi = self.deref.len();
        let ri = self.sparse.add(vi);
        self.deref.push(ri);
        ri
    }

    fn value_ptr_by_value_index(&self, ci: usize, vi: usize) -> Option<NonNull<u8>> {
        let col = self.cols.get(ci)?;
        unsafe { col.get_raw(vi) }
    }

    fn remove_row(&mut self, ri: usize) -> bool {
        if let Some(vi) = self.to_value_index(ri) {
            self.remove_row_by_value_index(vi);
            true
        } else {
            false
        }
    }

    fn remove_row_by_value_index(&mut self, vi: usize) {
        unsafe {
            self.begin_remove_row_by_value_index(vi);
            for ci in 0..self.num_columns() {
                self.drop_value_by_value_index(ci, vi);
            }
            self.end_remove_row_by_value_index(vi);
        }
    }

    unsafe fn begin_remove_row_by_value_index(&mut self, vi: usize) {
        assert!(vi < self.len());
    }

    unsafe fn remove_value_by_value_index(&mut self, ci: usize, vi: usize, buf: NonNull<u8>) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_raw(vi, buf.as_ptr());
        }
    }

    unsafe fn drop_value_by_value_index(&mut self, ci: usize, vi: usize) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_drop(vi);
        }
    }

    unsafe fn forget_value_by_value_index(&mut self, ci: usize, vi: usize) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_forget(vi);
        }
    }

    unsafe fn end_remove_row_by_value_index(&mut self, vi: usize) {
        let ri = self.deref.swap_remove(vi);
        let _vi = self.sparse.take(ri);
        debug_assert_eq!(_vi, Some(vi));
        if vi < self.deref.len() {
            let moved_key = self.deref[vi];
            *self.sparse.get_mut(moved_key).unwrap() = vi;
        }
    }
}

impl<S> Default for ChunkSparseSet<S>
where
    S: Default,
{
    fn default() -> Self {
        Self {
            sparse: OptVec::default(),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::default(),
        }
    }
}

/// Two-dimensional storage containing heterogeneous data types based on [`AnyVec`].
///
/// This struct is composed of "Sparse" and "Dense" layers. Sparse layer is literally sparse, so it
/// can contain vacant slots in it, while dense layer doesn't. Dense layer contains real items and
/// the items can be accessed through the sparse layer. Each dense is identified by its item's
/// [`TypeId`]. But you are encouraged to access each dense by its index, not `TypeId` for the
/// performance.
///
/// We call each dense layer a column, and all columns have the same length. So it looks like a 2D
/// matrix as shown below.
///
/// ```text
/// Index  Sparse  Dense  Dense
///                  A      B
///   0      0 _____ .      .
///   1      2 _   _ .      .
///   2      x  \_/_ .      .
///   3      1 __/   
///
/// , where '.' is item and 'x' is vacant slot.
/// ```
#[derive(Debug)]
pub struct SparseSet<S = FxBuildHasher> {
    sparse: OptVec<usize, S>,
    deref: Vec<usize>,
    cols: Vec<Column>,
    map: HashMap<TypeId, usize, S>,
}

impl SparseSet {
    /// Creates a new empty [`SparseSet`] with [`FxBuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// let mut cont = SparseSet::new();
    /// ```
    pub fn new() -> Self {
        Self {
            sparse: OptVec::new(),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::with_hasher(FxBuildHasher::default()),
        }
    }
}

impl<S> SparseSet<S> {
    /// Creates a new empty [`SparseSet`] with the given hasher.
    pub fn with_hasher<F: FnMut() -> S>(mut hasher: F) -> Self {
        Self {
            sparse: OptVec::with_hasher(hasher()),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::with_hasher(hasher()),
        }
    }
}

impl<S> ContainEntity for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn create_twin(&self) -> Box<dyn ContainEntity> {
        // Creates new `Holder`s for the same types.
        let cols = self
            .cols
            .iter()
            .map(|col| unsafe { col.create_twin() })
            .collect::<Vec<_>>();

        // We can reuse mapping information.
        let map = self.map.clone();

        // Makes empty instance.
        let this = Self {
            sparse: OptVec::default(),
            deref: Vec::new(),
            cols,
            map,
        };
        Box::new(this)
    }

    fn get_item_mut(&mut self, ci: usize, ri: usize) -> Option<NonNull<u8>> {
        let index = *self.sparse.get(ri)?;
        let col = self.cols.get_mut(ci)?;
        unsafe { col.get_raw(index) }
    }

    fn len(&self) -> usize {
        // All columns must have the same length.
        self.cols
            .first()
            .map(|col| unsafe { col.len() })
            .unwrap_or_default()
    }

    fn capacity(&self) -> usize {
        // All columns must have the same length.
        self.cols
            .first()
            .map(|col| unsafe { col.capacity() })
            .unwrap_or_default()
    }

    fn reserve(&mut self, additional: usize) {
        for col in self.cols.iter_mut() {
            unsafe { col.reserve(additional) }
        }
    }

    fn shrink_to_fit(&mut self) {
        for col in self.cols.iter_mut() {
            unsafe { col.shrink_to_fit() }
        }
    }

    unsafe fn resize_column(&mut self, ci: usize, new_len: usize, val_ptr: NonNull<u8>) {
        self.cols[ci].resize_raw(new_len, val_ptr)
    }
}

impl<S> RegisterComponent for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn add_column(&mut self, tinfo: TypeInfo) -> Option<usize> {
        let ty = tinfo.ty;
        if self.len() > 0 || self.get_column_index(&ty).is_some() {
            return None;
        }

        let col = Column::new(tinfo);
        self.cols.push(col);

        let ci = self.cols.len() - 1;
        self.map.insert(ty, ci);
        Some(ci)
    }

    fn remove_column(&mut self, ci: usize) -> Option<TypeInfo> {
        if self.cols.get(ci)?.borrow_count() > 0 {
            return None;
        }

        let old = self.cols.remove(ci);

        // Re-mapping
        for i in ci..self.cols.len() {
            // Safety: Index checked.
            let col = unsafe { self.cols.get_unchecked(i) };
            let ty = unsafe { col.item_type_info().ty };
            *self.map.get_mut(&ty).unwrap() = i;
        }

        // If empty, initialize self completely.
        if self.cols.is_empty() {
            mem::take(self);
        }

        let tinfo = unsafe { *old.item_type_info() };
        Some(tinfo)
    }

    fn get_column_index(&self, ty: &TypeId) -> Option<usize> {
        self.map.get(ty).cloned()
    }

    fn get_column_info(&self, ci: usize) -> Option<&TypeInfo> {
        self.cols.get(ci).map(|col| unsafe { col.item_type_info() })
    }

    fn num_columns(&self) -> usize {
        self.cols.len()
    }

    fn contains_column(&self, ty: &TypeId) -> bool {
        self.map.contains_key(ty)
    }
}

impl<S> BorrowComponent for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn borrow_column(&self, ci: usize) -> BorrowResult<RawGetter> {
        #[cfg(feature = "check")]
        let this_len = self.len();

        if let Some(col) = self.cols.get(ci) {
            let borrowed = col.borrow();

            // Validates length.
            #[cfg(feature = "check")]
            {
                if let Ok(borrowed) = borrowed.as_ref() {
                    assert_eq!(
                        this_len,
                        borrowed.len(),
                        "borrowed column must have the same length as entity container's"
                    );
                }
            }

            borrowed
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    fn borrow_column_mut(&mut self, ci: usize) -> BorrowResult<RawGetter> {
        #[cfg(feature = "check")]
        let this_len = self.len();

        if let Some(col) = self.cols.get(ci) {
            let borrowed = col.borrow_mut();

            // Validates length.
            #[cfg(feature = "check")]
            {
                if let Ok(borrowed) = borrowed.as_ref() {
                    assert_eq!(
                        this_len,
                        borrowed.len(),
                        "borrowed column must have the same length as entity container's"
                    );
                }
            }

            borrowed
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    unsafe fn get_column(&self, ci: usize) -> Option<NonNull<u8>> {
        self.cols.get(ci).map(|col| col.ptr_vec().cast())
    }
}

impl<S> AddEntity for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn to_value_index(&self, ri: usize) -> Option<usize> {
        self.sparse.get(ri).cloned()
    }

    fn begin_add_row(&mut self) {}

    unsafe fn add_value(&mut self, ci: usize, val_ptr: NonNull<u8>) {
        // No panic for now.
        unsafe {
            let col = self.cols.get_unchecked(ci);
            col.push_raw(val_ptr);
        }
    }

    unsafe fn end_add_row(&mut self) -> usize {
        let vi = self.deref.len();
        let ri = self.sparse.add(vi);
        self.deref.push(ri);
        ri
    }

    fn value_ptr_by_value_index(&self, ci: usize, vi: usize) -> Option<NonNull<u8>> {
        let col = self.cols.get(ci)?;
        unsafe { col.get_raw(vi) }
    }

    fn remove_row(&mut self, ri: usize) -> bool {
        if let Some(vi) = self.to_value_index(ri) {
            self.remove_row_by_value_index(vi);
            true
        } else {
            false
        }
    }

    fn remove_row_by_value_index(&mut self, vi: usize) {
        unsafe {
            self.begin_remove_row_by_value_index(vi);
            for ci in 0..self.num_columns() {
                self.drop_value_by_value_index(ci, vi);
            }
            self.end_remove_row_by_value_index(vi);
        }
    }

    unsafe fn begin_remove_row_by_value_index(&mut self, vi: usize) {
        assert!(vi < self.len());
    }

    unsafe fn remove_value_by_value_index(&mut self, ci: usize, vi: usize, buf: NonNull<u8>) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_raw(vi, buf.as_ptr());
        }
    }

    unsafe fn drop_value_by_value_index(&mut self, ci: usize, vi: usize) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_drop(vi);
        }
    }

    unsafe fn forget_value_by_value_index(&mut self, ci: usize, vi: usize) {
        unsafe {
            let col = self.cols.get_unchecked_mut(ci);
            col.swap_remove_forget(vi);
        }
    }

    unsafe fn end_remove_row_by_value_index(&mut self, vi: usize) {
        let ri = self.deref.swap_remove(vi);
        let _vi = self.sparse.take(ri);
        debug_assert_eq!(_vi, Some(vi));
        if vi < self.deref.len() {
            let moved_key = self.deref[vi];
            *self.sparse.get_mut(moved_key).unwrap() = vi;
        }
    }
}

impl<S> Default for SparseSet<S>
where
    S: Default,
{
    fn default() -> Self {
        Self {
            sparse: OptVec::default(),
            deref: Vec::new(),
            cols: Vec::new(),
            map: HashMap::default(),
        }
    }
}

/// A column containing [`ChunkAnyVec`] which is a chunked vector.
///
/// # Safety
///
/// See safety section in [Column].
#[derive(Debug)]
pub struct ChunkColumn {
    holder: Holder<ChunkAnyVec, RawGetter, RawGetter>,
}

impl ChunkColumn {
    const CHUNK_SIZE: usize = 4 * 1024;
    const MIN_CHUNK_LEN: usize = 8;

    #[inline]
    fn new(tinfo: TypeInfo) -> Self {
        let chunk_cap = Self::calc_chunk_cap(tinfo.size);
        let vec = ChunkAnyVec::new(tinfo, chunk_cap);
        let holder = unsafe { Holder::new(vec, fn_imm, fn_mut) };
        return Self { holder };

        // === Holder's access functions ===

        fn fn_imm(ptr: NonNull<ChunkAnyVec>) -> RawGetter {
            let vec = unsafe { ptr.as_ref() };
            let len = vec.len();

            let erased_ptr = ptr.cast::<u8>();
            let getter = unsafe { RawGetter::new(erased_ptr, len, fn_get) };
            getter.with_iter(fn_iter)
        }

        fn fn_mut(ptr: NonNull<ChunkAnyVec>) -> RawGetter {
            fn_imm(ptr)
        }

        unsafe fn fn_get(this: NonNull<u8>, index: usize) -> NonNull<u8> {
            unsafe { this.cast::<ChunkAnyVec>().as_ref().get_raw_unchecked(index) }
        }

        unsafe fn fn_iter(this: NonNull<u8>) -> FlatRawIter {
            unsafe { this.cast::<ChunkAnyVec>().as_ref().iter() }
        }
    }

    #[inline]
    fn borrow_count(&self) -> u32 {
        self.holder.borrow_count()
    }

    #[inline]
    fn borrow(&self) -> BorrowResult<RawGetter> {
        self.holder.borrow()
    }

    #[inline]
    fn borrow_mut(&self) -> BorrowResult<RawGetter> {
        self.holder.borrow_mut()
    }

    #[inline]
    unsafe fn create_twin(&self) -> Self {
        let tinfo = *self.item_type_info();
        let chunk_cap = Self::calc_chunk_cap(tinfo.size);
        let new_vec = ChunkAnyVec::new(tinfo, chunk_cap);
        let holder = Holder::new(new_vec, self.holder.fn_imm, self.holder.fn_mut);
        Self { holder }
    }

    #[inline]
    unsafe fn len(&self) -> usize {
        self.ptr_vec().as_ref().len()
    }

    #[inline]
    unsafe fn capacity(&self) -> usize {
        self.ptr_vec().as_ref().capacity()
    }

    #[inline]
    unsafe fn reserve(&self, additional: usize) {
        self.ptr_vec().as_mut().reserve(additional);
    }

    #[inline]
    unsafe fn shrink_to_fit(&self) {
        self.ptr_vec().as_mut().shrink_to_fit();
    }

    #[inline]
    unsafe fn resize_raw(&self, new_len: usize, val_ptr: NonNull<u8>) {
        // Panics if it's not clone
        self.ptr_vec().as_mut().resize_raw(new_len, val_ptr);
    }

    #[inline]
    unsafe fn item_type_info(&self) -> &TypeInfo {
        self.ptr_vec().as_ref().type_info()
    }

    #[inline]
    unsafe fn get_raw(&self, index: usize) -> Option<NonNull<u8>> {
        self.ptr_vec().as_ref().get_raw(index)
    }

    #[inline]
    unsafe fn push_raw(&self, val_ptr: NonNull<u8>) {
        self.ptr_vec().as_mut().push_raw(val_ptr);
    }

    #[inline]
    unsafe fn swap_remove_raw(&self, index: usize, buf: *mut u8) {
        self.ptr_vec().as_mut().swap_remove_raw(index, buf);
    }

    #[inline]
    unsafe fn swap_remove_drop(&self, index: usize) {
        self.ptr_vec().as_mut().swap_remove_drop(index);
    }

    #[inline]
    unsafe fn swap_remove_forget(&self, index: usize) {
        self.ptr_vec().as_mut().swap_remove_forget(index);
    }

    #[inline]
    unsafe fn ptr_vec(&self) -> NonNull<ChunkAnyVec> {
        self.holder.ptr_inner()
    }

    #[inline]
    fn calc_chunk_cap(item_size: usize) -> usize {
        Self::CHUNK_SIZE
            .checked_div(item_size)
            .map(|n| n.next_power_of_two().max(Self::MIN_CHUNK_LEN))
            .unwrap_or(0 /* has no effect */)
    }
}

/// A column containing [`AnyVec`].
///
/// # Safety
///
/// `Column` works based on a pointer to an inner vector. Because clients can freely get the pointer
/// through [`RawGetter`], so clients must carefully convert them into references or access the
/// `Column`.
#[derive(Debug)]
struct Column {
    holder: Holder<AnyVec, RawGetter, RawGetter>,
}

impl Column {
    #[inline]
    fn new(tinfo: TypeInfo) -> Self {
        let vec = AnyVec::new(tinfo);
        let holder = unsafe { Holder::new(vec, fn_imm, fn_mut) };
        return Self { holder };

        // === Holder's access functions ===

        // Holder's immutable access function.
        fn fn_imm(ptr: NonNull<AnyVec>) -> RawGetter {
            let vec = unsafe { ptr.as_ref() };
            let len = vec.len();

            let erased_ptr = ptr.cast::<u8>();
            let getter = unsafe { RawGetter::new(erased_ptr, len, fn_get) };
            getter.with_iter(fn_iter)
        }

        // Holder's mutable access function.
        fn fn_mut(ptr: NonNull<AnyVec>) -> RawGetter {
            fn_imm(ptr)
        }

        unsafe fn fn_get(this: NonNull<u8>, index: usize) -> NonNull<u8> {
            unsafe { this.cast::<AnyVec>().as_ref().get_raw_unchecked(index) }
        }

        unsafe fn fn_iter(this: NonNull<u8>) -> FlatRawIter {
            let this = unsafe { this.cast::<AnyVec>().as_ref() };
            this.flat_raw_iter()
        }
    }

    #[inline]
    fn borrow_count(&self) -> u32 {
        self.holder.borrow_count()
    }

    #[inline]
    fn borrow(&self) -> BorrowResult<RawGetter> {
        self.holder.borrow()
    }

    #[inline]
    fn borrow_mut(&self) -> BorrowResult<RawGetter> {
        self.holder.borrow_mut()
    }

    #[inline]
    unsafe fn create_twin(&self) -> Self {
        let tinfo = *self.item_type_info();
        let new_vec = AnyVec::new(tinfo);
        let holder = Holder::new(new_vec, self.holder.fn_imm, self.holder.fn_mut);
        Self { holder }
    }

    #[inline]
    unsafe fn len(&self) -> usize {
        self.ptr_vec().as_ref().len()
    }

    #[inline]
    unsafe fn capacity(&self) -> usize {
        self.ptr_vec().as_ref().capacity()
    }

    #[inline]
    unsafe fn reserve(&self, additional: usize) {
        self.ptr_vec().as_mut().reserve(additional);
    }

    #[inline]
    unsafe fn shrink_to_fit(&self) {
        self.ptr_vec().as_mut().shrink_to_fit();
    }

    #[inline]
    unsafe fn resize_raw(&self, new_len: usize, val_ptr: NonNull<u8>) {
        // Panics if it's not clone
        self.ptr_vec().as_mut().resize_raw(new_len, val_ptr);
    }

    #[inline]
    unsafe fn item_type_info(&self) -> &TypeInfo {
        self.ptr_vec().as_ref().type_info()
    }

    #[inline]
    unsafe fn get_raw(&self, index: usize) -> Option<NonNull<u8>> {
        self.ptr_vec().as_ref().get_raw(index)
    }

    #[inline]
    unsafe fn push_raw(&self, val_ptr: NonNull<u8>) {
        self.ptr_vec().as_mut().push_raw(val_ptr);
    }

    #[inline]
    unsafe fn swap_remove_raw(&self, index: usize, buf: *mut u8) {
        self.ptr_vec().as_mut().swap_remove_raw(index, buf);
    }

    #[inline]
    unsafe fn swap_remove_drop(&self, index: usize) {
        self.ptr_vec().as_mut().swap_remove_drop(index);
    }

    #[inline]
    unsafe fn swap_remove_forget(&self, index: usize) {
        self.ptr_vec().as_mut().swap_remove_forget(index);
    }

    #[inline]
    unsafe fn ptr_vec(&self) -> NonNull<AnyVec> {
        self.holder.ptr_inner()
    }
}

#[cfg(test)]
mod tests {
    use crate as my_ecs;
    use crate::prelude::*;
    use std::sync::Arc;

    #[test]
    fn test_move_entity_to_entity_container() {
        inner(SparseSet::new());
        inner(ChunkSparseSet::new());

        fn inner<T: ContainEntity>(mut cont: T) {
            #![allow(unused)]

            #[derive(Entity)]
            struct Ea {
                ca: Ca,
                cb: Cb,
            }
            #[derive(Component)]
            struct Ca(i32);
            #[derive(Component)]
            struct Cb(Arc<String>);

            Ea::register_to(&mut cont);

            // Tests `Entity::move_to`.
            let b = Arc::new("0".to_owned());

            let ri_0 = Ea {
                ca: Ca(0),
                cb: Cb(Arc::clone(&b)),
            }
            .move_to(&mut cont);
            assert_eq!(Arc::strong_count(&b), 2);
            assert_eq!(cont.len(), 1);

            let ri_1 = Ea {
                ca: Ca(1),
                cb: Cb(Arc::clone(&b)),
            }
            .move_to(&mut cont);
            assert_eq!(Arc::strong_count(&b), 3);
            assert_eq!(cont.len(), 2);

            // Correctly moved? checks it by removing.
            cont.remove_row(ri_0);
            assert_eq!(Arc::strong_count(&b), 2);
            cont.remove_row(ri_1);
            assert_eq!(Arc::strong_count(&b), 1);
        }
    }

    #[test]
    fn test_reserve_entity_container() {
        fn inner<T: ContainEntity>(mut cont: T) {
            #![allow(unused)]

            #[derive(Entity)]
            struct Ea {
                ca: Ca,
            }
            #[derive(Component)]
            struct Ca(i32);

            Ea::register_to(&mut cont);

            assert_eq!(cont.capacity(), 0);
            assert_eq!(cont.len(), 0);

            let reserve_size = ChunkSparseSet::<()>::CHUNK_SIZE + 1;
            cont.reserve(reserve_size);

            assert!(cont.capacity() >= reserve_size);
            assert_eq!(cont.len(), 0);
        }
    }
}
