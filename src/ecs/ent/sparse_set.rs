use super::entity::{AddEntity, BorrowComponent, ContainEntity, RegisterComponent};
use crate::ds::prelude::*;
use std::{
    any::TypeId, cmp, collections::HashMap, fmt::Debug, hash::BuildHasher, mem, ptr::NonNull,
};

/// Two dimensional storage containing heterogeneous types of data.
/// This structure is composed of "Sparse" and "Dense" layers.
/// Sparse layer is literally sparse, so it has vacant slots in it, while dense layer doesn't.
/// Dense layer has items and they can be accessed through the sparse layer.
/// Each dense is identified by its item's [`TypeId`].
/// But you are encouraged to access each dense by its index, not TypeId for the performance.
///
/// We call each dense layer a column, and all columns have the same length.
/// So it looks like a 2D matrix.
#[derive(Debug)]
pub struct SparseSet<S> {
    sparse: OptVec<usize, S>,
    deref: Vec<usize>,
    cols: Vec<Holder<ChunkAnyVec, RawGetter, RawGetter>>,
    len: usize,
    map: HashMap<TypeId, usize, S>,
}

impl<S> SparseSet<S>
where
    S: Default,
{
    const CHUNK_SIZE: usize = 4 * 1024;
    const MIN_CHUNK_LEN: usize = 8;

    pub fn new() -> Self {
        Self {
            sparse: OptVec::new(),
            deref: Vec::new(),
            cols: Vec::new(),
            len: 0,
            map: HashMap::default(),
        }
    }
}

impl<S> ContainEntity for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn create_twin(&self) -> Box<dyn ContainEntity> {
        // Creates new Holders keeping same type information.
        let cols = self
            .cols
            .iter()
            .map(|col| {
                let (fn_imm, fn_mut) = (col.get_fn_imm(), col.get_fn_mut());
                let col = col.get().unwrap();
                let value = ChunkAnyVec::new(*col.type_info(), col.chunk_len());
                Holder::new(value, fn_imm, fn_mut)
            })
            .collect::<Vec<_>>();

        // We can reuse mapping information.
        let map = self.map.clone();

        // Makes empty instance.
        let this = Self {
            sparse: OptVec::new(),
            deref: Vec::new(),
            cols,
            len: 0,
            map,
        };
        Box::new(this)
    }

    fn len(&self) -> usize {
        self.len
    }

    /// # Panics
    ///
    /// Panics if other threads borrowed any column.
    fn get_item_mut(&mut self, ci: usize, ri: usize) -> Option<NonNull<u8>> {
        let key = ri;

        let index = *self.sparse.get(key)?;
        let col = self.cols.get_mut(ci)?;
        let col = col.get_mut().unwrap();
        col.get_raw(index)
    }
}

impl<S> RegisterComponent for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    /// Adds a new column and returns column index.
    fn add_column(&mut self, tinfo: TypeInfo) -> Option<usize> {
        let ty = tinfo.ty;
        if self.len() > 0 || self.get_column_index(&ty).is_some() {
            return None;
        }

        // Holder's immutable access function.
        fn fn_imm(col: &ChunkAnyVec) -> RawGetter {
            // Safety: Infallible.
            let this = unsafe { NonNull::new_unchecked((col as *const _ as *const u8).cast_mut()) };
            let len = col.len();
            unsafe fn fn_get(this: NonNull<u8>, index: usize) -> NonNull<u8> {
                this.cast::<ChunkAnyVec>().as_ref().get_raw_unchecked(index)
            }
            unsafe fn fn_iter(this: NonNull<u8>) -> FlatRawIter {
                this.cast::<ChunkAnyVec>().as_ref().iter()
            }
            // Safety: The pointer is valid.
            let getter = unsafe { RawGetter::new(this, len, fn_get) };
            getter.with_iter(fn_iter)
        }

        // Holder's mutable access function.
        fn fn_mut(col: &mut ChunkAnyVec) -> RawGetter {
            fn_imm(col)
        }

        // Adds column wrapped with Holder.
        let chunk_len = if tinfo.size != 0 {
            cmp::max(
                (Self::CHUNK_SIZE / tinfo.size).next_power_of_two(),
                Self::MIN_CHUNK_LEN,
            )
        } else {
            0 // Has no effect
        };
        let value = ChunkAnyVec::new(tinfo, chunk_len);
        let holder = Holder::new(value, fn_imm, fn_mut);
        self.cols.push(holder);

        let ci = self.cols.len() - 1;
        self.map.insert(ty, ci);
        Some(ci)
    }

    fn remove_column(&mut self, ci: usize) -> Option<TypeInfo> {
        if ci >= self.get_column_num() || self.cols[ci].borrow_count() != 0 {
            return None;
        }

        let old = self.cols.remove(ci);

        // Does re-mapping.
        for i in ci..self.cols.len() {
            let col = self.cols[i].get().unwrap();
            let ty = col.type_id();
            *self.map.get_mut(&ty).unwrap() = i;
        }

        // If empty, initialize self completely.
        if self.cols.is_empty() {
            mem::take(self);
        }

        let old = old.get().unwrap();
        let tinfo = old.type_info();
        Some(*tinfo)
    }

    fn get_column_index(&self, ty: &TypeId) -> Option<usize> {
        self.map.get(ty).cloned()
    }

    fn get_column_info(&self, ci: usize) -> Option<&TypeInfo> {
        self.cols.get(ci).map(|col| {
            let col = col.get().unwrap();
            col.type_info()
        })
    }

    fn get_column_num(&self) -> usize {
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
        self.cols.get(ci).map(|col| {
            let ptr = col.get_unchecked() as *const _ as *const u8;
            NonNull::new_unchecked(ptr.cast_mut())
        })
    }
}

impl<S> AddEntity for SparseSet<S>
where
    S: BuildHasher + Default + Clone + 'static,
{
    fn begin_add_row(&mut self) {}

    unsafe fn add_value(&mut self, ci: usize, val_ptr: NonNull<u8>) {
        // Panics if holder has beend borrowed in the past.
        let holder = self.cols.get_unchecked_mut(ci);
        let mut col = holder.get_mut().unwrap_unchecked();
        col.push_raw(val_ptr);
    }

    unsafe fn end_add_row(&mut self) -> usize {
        self.len += 1;
        let len = self.deref.len() + 1;
        let key = self.sparse.add(len - 1);
        self.deref.push(key);
        key
    }

    fn remove_row(&mut self, ri: usize) -> bool {
        let key = ri;

        if let Some(index) = self.sparse.take(key) {
            self.remove_row_by_value_index(index);
            true
        } else {
            false
        }
    }

    fn remove_row_by_value_index(&mut self, vi: usize) {
        for col in self.cols.iter_mut() {
            let mut col = col.get_mut().unwrap();
            col.swap_remove_drop(vi);
        }

        self.deref.swap_remove(vi);

        self.len -= 1;

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
        Self::new()
    }
}
