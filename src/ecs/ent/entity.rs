use super::component::ComponentKey;
use crate::{ds::prelude::*, util::prelude::*};
use std::{any::TypeId, fmt, ptr::NonNull, slice, sync::Arc};

pub trait Entity: Send + 'static {
    /// Returns entity key of the entity type.
    fn entity_key() -> EntityKey {
        EntityKey::Type(EntityTypeId::of::<Self>())
    }

    /// Moves the entity to an entity container.
    ///
    /// # How to move
    ///
    /// Use [`AddEntity::begin_add_row`], [`AddEntity::add_value`], and
    /// [`AddEntity::end_add_row`] and forget self.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::hash::RandomState;
    ///
    /// #[derive(Entity)]
    /// struct Ea {
    ///     ca: Ca,
    /// }
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// cont.add_column(tinfo!(Ca));
    ///
    /// let e = Ea { ca: Ca };
    /// e.move_to(&mut cont);
    /// assert_eq!(cont.len(), 1);
    /// ```
    fn move_to<T: AddEntity + ?Sized>(self, cont: &mut T) -> usize;
}

/// A trait for collecting heterogeneous component types.
///
/// In this trait, each component type is gathered in each component column and
/// all columns have the same length like 2d matrix.
///
/// When it comes to in & out types, this trait has intentionally raw pointer
/// parameters not to use generic for object safety. So that you can hold
/// various sorts of entity container in a single variable.
///
/// # Index system
///
/// There are three index systems for this trait.
///
/// The first one is 'column index' which is for pointing a certain component
/// column. When you add or remove component column from an entity container,
/// you will get or need this column index. Column indices begins with 0 and
/// increases by 1 as you put in a component column.
///
/// The second and third index systems are related to pointing a certain entity
/// in an entity container. In other words, you need one of those index systems
/// when you need access to a single entity.
///
/// Second one is 'row index' which is a kind of outer index for each entity.
/// You will get this row index when you put your entity in an entity container.
/// Also you can remove an entity using the row index. Row indices may not be in
/// order and not consequent.
///
/// The last one is 'value index' which is inner index for each entity. In
/// contrast to former one, value indices are in order and consequent like
/// indices on a slice. Plus, all component columns follows the same value
/// indices in an entity container.
///
/// Take a look at example below.
///
/// ```text
///              column index      0        1
/// --------------------------------------------
/// | row index | value index | comp_a | comp_b |
/// |     0     |      0      |    .   |    .   |
/// |     4     |      1      |    .   |    .   |
/// |     2     |      2      |    .   |    .   |
/// ```
///
/// # Examples
///
/// ```
/// # use my_ecs::prelude::*;
/// use std::{hash::RandomState, ptr::NonNull};
///
/// #[derive(Entity)]
/// struct Entity {
///     a: Ca,
///     b: Cb,
/// }
/// #[derive(Component)]
/// struct Ca(i32);
/// #[derive(Component)]
/// struct Cb(i32);
///
/// let mut cont: SparseSet<RandomState> = SparseSet::new();
///
/// // Adds component columns.
/// let ci_a = cont.add_column(tinfo!(Ca)).unwrap();
/// let ci_b = cont.add_column(tinfo!(Cb)).unwrap();
///
/// // Adds component values for the entity.
/// cont.begin_add_row();
/// let ri = unsafe {
///     let ptr = NonNull::new(&mut Ca(4) as *mut Ca as *mut u8).unwrap();
///     cont.add_value(ci_a, ptr);
///     let ptr = NonNull::new(&mut Cb(2) as *mut Cb as *mut u8).unwrap();
///     cont.add_value(ci_b, ptr);
///     cont.end_add_row()
/// };
/// assert_eq!(cont.len(), 1);
///
/// // Borrows component columns and test them if they are as we expected.
/// let col_a = cont.borrow_column(ci_a).unwrap();
/// let col_b = cont.borrow_column(ci_b).unwrap();
/// unsafe {
///     let ptr = col_a.get(0).unwrap();
///     assert_eq!(*ptr.as_ref(), 4);
///     let ptr = col_b.get(0).unwrap();
///     assert_eq!(*ptr.as_ref(), 2);
/// }
///
/// // Removes the entity we just put.
/// let is_removed = cont.remove_row(ri);
/// assert!(is_removed);
/// assert_eq!(cont.len(), 0);
/// ```
//
// Must object safe.
#[allow(clippy::len_without_is_empty)]
pub trait ContainEntity: RegisterComponent + BorrowComponent + AddEntity {
    /// Creates a new entity container that has the same component types without
    /// component values.
    ///
    /// In other words, the copied container doesn't have any entities in it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, ptr::NonNull, any::TypeId};
    ///
    /// #[derive(Entity)]
    /// struct Entity {
    ///     a: Ca,
    /// }
    /// #[derive(Component)]
    /// struct Ca(i32);
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// let ci = cont.add_column(tinfo!(Ca)).unwrap();
    ///
    /// // Adds component values for an entity.
    /// cont.begin_add_row();
    /// unsafe {
    ///     let ptr = NonNull::new(&mut Ca(0) as *mut Ca as *mut u8).unwrap();
    ///     cont.add_value(ci, ptr);
    ///     cont.end_add_row();
    /// }
    /// assert_eq!(cont.len(), 1);
    ///
    /// let twin = cont.create_twin();
    /// assert_eq!(twin.len(), 0);
    /// assert!(twin.contains_column(&TypeId::of::<Ca>()));
    /// ```
    fn create_twin(&self) -> Box<dyn ContainEntity>;

    /// Retrieves an entity for the given component column index and row index
    /// from the entity container.
    ///
    /// If one of two indices is out of bounds, returns `None`.
    fn get_item_mut(&mut self, ci: usize, ri: usize) -> Option<NonNull<u8>>;

    /// Returns number of entities in the entity container.
    ///
    /// # Examples
    ///
    /// See [`ContainEntity`] document.
    fn len(&self) -> usize;
}

/// A trait for adding or removing component types from an entity container.
///
/// See [`ContainEntity`] for more information.
//
// Must object safe.
pub trait RegisterComponent {
    /// Adds a component column to the entity container.
    ///
    /// If addition is successful, returns column index for the component. But
    /// the entity container cannot add new entity when it already contains
    /// entities within it or the same component was added. In that case,
    /// returns `None`.
    ///
    /// You can get [`TypeInfo`] from any static types using [`tinfo`] macro.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    ///
    /// cont.add_column(tinfo!(Ca));
    /// assert!(cont.contains_column(&TypeId::of::<Ca>()));
    ///
    /// // Duplicated component columns are not allowed.
    /// let ret = cont.add_column(tinfo!(Ca));
    /// assert!(ret.is_none());
    /// ```
    fn add_column(&mut self, tinfo: TypeInfo) -> Option<usize>;

    /// Removes the component column from the entity container.
    ///
    /// If removal is successful, returns [`TypeInfo`] of the removed component
    /// column. But if the entity container doesn't have component column for
    /// the given column index, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    ///
    /// let col_idx = cont.add_column(tinfo!(Ca)).unwrap();
    /// assert!(cont.contains_column(&TypeId::of::<Ca>()));
    ///
    /// let tinfo = cont.remove_column(col_idx);
    /// assert_eq!(tinfo, Some(tinfo!(Ca)));
    /// assert!(!cont.contains_column(&TypeId::of::<Ca>()));
    /// ```
    fn remove_column(&mut self, ci: usize) -> Option<TypeInfo>;

    /// Retrieves column index for the given component type.
    ///
    /// If there is not the component column in the entity container, returns
    /// `None`
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    /// #[derive(Component)]
    /// struct Cb;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    ///
    /// let col_idx = cont.add_column(tinfo!(Ca)).unwrap();
    /// assert_eq!(cont.get_column_index(&TypeId::of::<Ca>()).unwrap(), col_idx);
    ///
    /// assert!(cont.get_column_index(&TypeId::of::<Cb>()).is_none());
    /// ```
    fn get_column_index(&self, ty: &TypeId) -> Option<usize>;

    /// Retrieves [`TypeInfo`] of the component for the given column index.
    ///
    /// If there is not the component column in the entity container, returns
    /// `None`
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::hash::RandomState;
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    ///
    /// let col_idx = cont.add_column(tinfo!(Ca)).unwrap();
    /// let tinfo = cont.get_column_info(col_idx);
    /// assert_eq!(tinfo, Some(&tinfo!(Ca)));
    /// ```
    fn get_column_info(&self, ci: usize) -> Option<&TypeInfo>;

    /// Retrieves number of component columns in the entity container.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::hash::RandomState;
    ///
    /// #[derive(Component)]
    /// struct Ca;
    /// #[derive(Component)]
    /// struct Cb;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// assert_eq!(cont.get_column_num(), 0);
    ///
    /// cont.add_column(tinfo!(Ca));
    /// assert_eq!(cont.get_column_num(), 1);
    ///
    /// cont.add_column(tinfo!(Cb));
    /// assert_eq!(cont.get_column_num(), 2);
    /// ```
    fn get_column_num(&self) -> usize;

    /// Returns true if the entity container contains given component type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// assert!(!cont.contains_column(&TypeId::of::<Ca>()));
    ///
    /// cont.add_column(tinfo!(Ca));
    /// assert!(cont.contains_column(&TypeId::of::<Ca>()));
    /// ```
    fn contains_column(&self, ty: &TypeId) -> bool {
        self.get_column_index(ty).is_some()
    }
}

/// A trait for borrowing a component column from an entity container.
///
/// See [`ContainEntity`] for more information.
//
// Must object safe.
pub trait BorrowComponent {
    /// Borrows component column for the given column index.
    ///
    /// If borrow is successful, returns [`RawGetter`] of the component column.
    /// Otherwise, returns [`BorrowError`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// cont.add_column(tinfo!(Ca));
    ///
    /// let col_idx = cont.get_column_index(&TypeId::of::<Ca>()).unwrap();
    /// let getter = cont.borrow_column(col_idx).unwrap();
    /// ```
    fn borrow_column(&self, ci: usize) -> BorrowResult<RawGetter>;

    /// Borrows component column mutably for the given column index.
    ///
    /// If borrow is successful, returns [`RawGetter`] of the component column.
    /// Otherwise, returns [`BorrowError`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    /// use std::{hash::RandomState, any::TypeId};
    ///
    /// #[derive(Component)]
    /// struct Ca;
    ///
    /// let mut cont: SparseSet<RandomState> = SparseSet::new();
    /// cont.add_column(tinfo!(Ca));
    ///
    /// let col_idx = cont.get_column_index(&TypeId::of::<Ca>()).unwrap();
    /// let getter = cont.borrow_column_mut(col_idx).unwrap();
    /// ```
    fn borrow_column_mut(&mut self, ci: usize) -> BorrowResult<RawGetter>;

    /// Retrives component column pointer for the given column index.
    ///
    /// If there is not the component column in the entity container, returns
    /// `None`
    ///
    /// # Safety
    ///
    /// Undefine behavior if exclusive borrow happend before.
    unsafe fn get_column(&self, ci: usize) -> Option<NonNull<u8>>;
}

/// A trait for adding or removing component values from an entity container.
///
/// See [`ContainEntity`] for more information.
//
// Must object safe.
pub trait AddEntity {
    /// Starts inserting component values of an entity to the entity container.
    ///
    /// This method must be followed by [`AddEntity::add_value`] and
    /// [`AddEntity::end_add_row`].
    ///
    /// See [`AddEntity::add_value`] if you need examples.
    ///
    /// # Panics
    ///
    /// May panic if any component columns were borrowed and not returned. But
    /// implementations must guarantee that one of [`AddEntity::begin_add_row`],
    /// [`AddEntity::add_value`], and [`AddEntity::end_add_row`] panics if
    /// borrowed component column is detected.
    ///
    /// # Examples
    ///
    /// See [`ContainEntity`] document.
    fn begin_add_row(&mut self);

    /// Inserts a component value of an entity in the entity container.
    ///
    /// This method creates a bitwise copy of the value, so that caller must not
    /// access the value in any ways including its drop procedure after calling
    /// this method. Plus, caller must call this method between
    /// [`AddEntity::begin_add_row`] and [`AddEntity::end_add_row`] for all
    /// components.
    ///
    /// # Panics
    ///
    /// May panic if any component columns were borrowed and not returned. But
    /// implementations must guarantee that one of [`AddEntity::begin_add_row`],
    /// [`AddEntity::add_value`], and [`AddEntity::end_add_row`] panics if
    /// borrowed component column is detected.
    ///
    /// # Safety
    ///
    /// Caller must guarantee things below.
    /// - Column index `ci` is not out of bounds.
    /// - Value pointer `val_ptr` is valid for the component column type.
    /// - Value must not be accessed after calling this method even `drop()`.
    ///
    /// # Examples
    ///
    /// See [`ContainEntity`] document.
    unsafe fn add_value(&mut self, ci: usize, val_ptr: NonNull<u8>);

    /// Finishes inserting component values of an entity in the entity
    /// container.
    ///
    /// Thie method returns row index to the just inserted entity. Plus, this
    /// method must follow calling to [`AddEntity::begin_add_row`] and
    /// [`AddEntity::add_value`].
    ///
    /// See [`AddEntity::add_value`] if you need examples.
    ///
    /// # Panics
    ///
    /// May panic if any component columns were borrowed and not returned. But
    /// implementations must guarantee that one of [`AddEntity::begin_add_row`],
    /// [`AddEntity::add_value`], and [`AddEntity::end_add_row`] panics if
    /// borrowed component column is detected.
    ///
    /// # Safety
    ///
    /// Caller must have called [`AddEntity::begin_add_row`] once and
    /// [`AddEntity::add_value`] number of component columns times before
    /// calling to this method for just one entity.
    ///
    /// # Examples
    ///
    /// See [`ContainEntity`] document.
    unsafe fn end_add_row(&mut self) -> usize;

    /// Removes an entity for the given row index from the entity container.
    ///
    /// If removal is successful, returns true. Otherwise, for instance index
    /// is out of bounds, returns false.
    ///
    /// # Examples
    ///
    /// See [`ContainEntity`] document.
    fn remove_row(&mut self, ri: usize) -> bool;

    /// Removes an entity for the given value index from the entity container.
    ///
    /// # Panics
    ///
    /// Panics if the value index is out of bounds.
    fn remove_row_by_value_index(&mut self, vi: usize);
}

/// A specific entity identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EntityId {
    /// Entity container index.
    ei: EntityIndex,

    /// Item index.
    itemi: usize,
}

impl EntityId {
    pub const fn new(ei: EntityIndex, itemi: usize) -> Self {
        Self { ei, itemi }
    }

    pub const fn container_index(&self) -> EntityIndex {
        self.ei
    }

    pub const fn item_index(&self) -> usize {
        self.itemi
    }
}

/// Key for the map [`EntityStorage`] in order to get value [`EntityContainer`].
/// `EntityStorage` provides some access ways shown below.
/// - Index: Entity container index and generation when the container is generated.
/// - Name: Unique name for the entity. Each entity must have its name.
/// - Type: If the entity is declared statically, it has its own type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EntityKey {
    /// Unique name for the entity.
    /// All entities have their name.
    Name(EntityName),

    /// Entity container index.
    /// Registered entities to [`EntityStorage`] have their indices to the dictionary.
    Index(EntityIndex),

    /// Type id of the entity.
    /// Statically defined entities have their type ids.
    Type(EntityTypeId),
}

impl_from_for_enum!(EntityKey, Name, EntityName);
impl_from_for_enum!(EntityKey, Index, EntityIndex);
impl_from_for_enum!(EntityKey, Type, EntityTypeId);

impl EntityKey {
    pub fn name(&self) -> &EntityName {
        if let Self::Name(name) = self {
            name
        } else {
            panic!("{:?} is not Name", self);
        }
    }

    pub fn index(&self) -> &EntityIndex {
        if let Self::Index(index) = self {
            index
        } else {
            panic!("{:?} is not Name", self);
        }
    }

    pub fn ty(&self) -> &EntityTypeId {
        if let Self::Type(ty) = self {
            ty
        } else {
            panic!("{:?} is not Type", self);
        }
    }
}

/// [`Arc<str>`] of entity.
/// An entity must have its unique name.
#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[repr(transparent)]
pub struct EntityName(Arc<str>);

impl EntityName {
    pub const fn new(name: Arc<str>) -> Self {
        Self(name)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for EntityName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// [`GenIndex`] of entity container.
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
#[repr(transparent)]
pub struct EntityIndex(GenIndex<u32, u32>);

impl EntityIndex {
    pub const fn new(index: GenIndex<u32, u32>) -> Self {
        Self(index)
    }

    pub fn generation(&self) -> u32 {
        *self.0.get_generation()
    }

    pub fn index(&self) -> usize {
        *self.0.get_index() as usize
    }
}

impl fmt::Display for EntityIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// [`TypeId`] of an entity.
pub type EntityTypeId = ATypeId<EntityTypeId_>;
pub struct EntityTypeId_;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum EntityKeyKind {
    /// Corresponds to [`EntityKey::Name`].
    Name,
    /// Corresponds to [`EntityKey::Index`].
    Index,
    /// Corresponds to [`EntityKey::Type`].
    Type,
}

impl From<&EntityKey> for EntityKeyKind {
    fn from(value: &EntityKey) -> Self {
        match value {
            EntityKey::Name(..) => EntityKeyKind::Name,
            EntityKey::Index(..) => EntityKeyKind::Index,
            EntityKey::Type(..) => EntityKeyKind::Type,
        }
    }
}

/// A piece of information about an entity such as entity index, name, and its components.
#[derive(Debug, Eq)]
pub struct EntityTag {
    /// Corresponds to [`EntityKey::Index`].
    index: EntityIndex,

    /// Corresponds to [`EntityKey::Name`].
    name: EntityName,

    /// Component keys that belong to the entity.
    comp_keys: ManagedConstPtr<ComponentKey>,

    /// Corresponds to [`EntityContainer::comp_names`].
    comp_names: ManagedConstPtr<&'static str>,

    /// Length of [`Self::comp_keys`] slice and [`Self::comp_names`] slice.
    comp_len: usize,
}

impl EntityTag {
    /// Creates a tag including pointers to the given arguments.
    /// So caller must guarantee validity for those pointers.
    ///
    /// # Safety
    ///
    /// Undefined behavior if `name`, `comp_keys` or `comp_names` are invalidated.
    /// For example, it's undfeind if one of them is dropped or aliased
    /// as mutable reference while the tag lives.
    pub unsafe fn new(
        index: EntityIndex,
        name: EntityName,
        comp_keys: &[ComponentKey],
        comp_names: &[&'static str],
    ) -> Self {
        debug_assert_eq!(comp_keys.len(), comp_names.len());

        let comp_len = comp_keys.len();
        let comp_keys = NonNull::new_unchecked(comp_keys.as_ptr().cast_mut());
        let comp_keys = NonNullExt::from_nonnull(comp_keys);
        let comp_keys = ManagedConstPtr::new(comp_keys);
        let comp_names = NonNull::new_unchecked(comp_names.as_ptr().cast_mut());
        let comp_names = NonNullExt::from_nonnull(comp_names);
        let comp_names = ManagedConstPtr::new(comp_names);

        Self {
            index,
            name,
            comp_keys,
            comp_names,
            comp_len,
        }
    }

    pub fn index(&self) -> EntityIndex {
        self.index
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn comp_keys(&self) -> &[ComponentKey] {
        let ptr = self.comp_keys.as_ptr();

        // Safety: Caller who called `Self::new()` guarantees validity of the pointers.
        unsafe { slice::from_raw_parts(ptr, self.comp_len) }
    }

    pub fn comp_names(&self) -> &[&'static str] {
        let ptr = self.comp_names.as_ptr();

        // Safety: Caller who called `Self::new()` guarantees validity of the pointers.
        unsafe { slice::from_raw_parts(ptr, self.comp_len) }
    }
}

impl PartialEq for EntityTag {
    fn eq(&self, other: &Self) -> bool {
        self.index() == other.index()
    }
}
