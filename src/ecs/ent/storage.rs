use super::{
    component::{Component, ComponentKey},
    entity::{
        ContainEntity, Entity, EntityId, EntityIndex, EntityKey, EntityKeyKind, EntityKeyRef,
        EntityName, EntityTypeId,
    },
};
use crate::ecs::EcsError;
use crate::{debug_format, ds::prelude::*};
use std::{
    any::TypeId,
    collections::HashMap,
    fmt,
    hash::BuildHasher,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
};

pub trait AsEntityReg {
    fn as_entity_descriptor() -> EntityReg;
}

/// A storage where you can find both entity and component data and static
/// information about them such as names, types, and their relationships.
///
/// Each container is basically identified by its component keys. In other
/// words, unique combination of components is the key of an entity container.
/// So you cannot register two entities that has the same components. Entity
/// containers are also identified by their indices they get when they are
/// registered to this storage. It's recommended accessing using entity index
/// instead of component keys if possible because it would be faster.
///
/// Optionally, entity name or type may be able to be used as an identification,
/// but it's not guaranteed because it must be provided by clients. If not so,
/// searching an entity container via entity name or type fails. See
/// [`EntityKeyRef`].
//
// TODO: Write this on ent module doc as well.
// Why entities of the same component combination are not allowed?
// - If it's allowed, something like below is possible.
//   EntA: (CompA, CompB), EntB: (CompA), EntC: (CompA)
// - Imagine clients are removing `CompB` from some items in EntA's container.
//   In that case, they must be moved into `EntB` or `EntC`, but we cannot
//   specify which container they should go.
#[derive(Debug)]
pub(crate) struct EntityStorage<S> {
    /// A map holding entity containers and relationships to components.
    ///
    /// Key: Index or slice of [`ComponentKey`]s
    map: GroupMap<Arc<[ComponentKey]>, EntityContainer, ComponentKey, TypeInfo, S>,

    /// Optional mapping from [`EntityName`] to [`EntityIndex`].
    name_to_index: HashMap<EntityName, EntityIndex, S>,

    /// Optional mapping from [`EntityTypeId`] to [`EntityIndex`].
    type_to_index: HashMap<EntityTypeId, EntityIndex, S>,

    /// Generation of each entity container. The generation is when the
    /// container is registered to this storage.
    ent_gens: Vec<u32>,

    /// Generation that will be assigned to the next registered entity
    /// container.
    gen: u32,
}

impl<S> EntityStorage<S>
where
    S: Default,
{
    pub(crate) fn new() -> Self {
        Self {
            map: GroupMap::new(),
            name_to_index: HashMap::default(),
            type_to_index: HashMap::default(),
            ent_gens: Vec::new(),
            gen: 1,
        }
    }
}

impl<S> EntityStorage<S>
where
    S: BuildHasher + Default,
{
    /// Turns `ekey` into another type of it according to `to`.
    pub(crate) fn convert_entity_key<'r, K>(&self, key: K, to: EntityKeyKind) -> Option<EntityKey>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into(), to);

        // === Internal helper functions ===

        fn inner<S>(
            this: &EntityStorage<S>,
            key: EntityKeyRef<'_>,
            to: EntityKeyKind,
        ) -> Option<EntityKey>
        where
            S: BuildHasher + Default,
        {
            let ei = this.entity_index(key)?;
            let res = match to {
                EntityKeyKind::Name => {
                    // Safety: Infallible.
                    let name = unsafe { this.map.get_group(ei).unwrap_unchecked().0.name()? };
                    EntityKey::Name(name.clone())
                }
                EntityKeyKind::Index => {
                    let ei = EntityIndex::new(GenIndex::new(
                        ei as u32,
                        // Safety: Infallible.
                        unsafe { *this.ent_gens.get_unchecked(ei) },
                    ));
                    EntityKey::Index(ei)
                }
                EntityKeyKind::Ckeys => {
                    // Safety: Infallible.
                    let ckeys = unsafe { this.map.get_group_key(ei).unwrap_unchecked() };
                    EntityKey::Ckeys(Arc::clone(ckeys))
                }
            };
            Some(res)
        }
    }

    pub(crate) fn get_component_keys<'r, K>(&self, key: K) -> Option<&Arc<[ComponentKey]>>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into());

        // === Internal helper functions ===

        fn inner<'this, S>(
            this: &'this EntityStorage<S>,
            key: EntityKeyRef<'_>,
        ) -> Option<&'this Arc<[ComponentKey]>>
        where
            S: BuildHasher + Default,
        {
            let ei = this.entity_index(key)?;
            // Safety: Infallible.
            let ckeys = unsafe { this.map.get_group_key(ei).unwrap_unchecked() };
            Some(ckeys)
        }
    }

    pub(crate) fn get_entity_container<'r, K>(&self, key: K) -> Option<&EntityContainer>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into());

        // === Internal helper functions ===

        fn inner<'this, S>(
            this: &'this EntityStorage<S>,
            key: EntityKeyRef<'_>,
        ) -> Option<&'this EntityContainer>
        where
            S: BuildHasher + Default,
        {
            let ei = this.entity_index(key)?;
            // Safety: Infallible.
            let cont = unsafe { this.map.get_group(ei).unwrap_unchecked().0 };
            Some(cont)
        }
    }

    pub(crate) fn get_entity_container_mut<'r, K>(&mut self, key: K) -> Option<&mut EntityContainer>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into());

        // === Internal helper functions ===

        fn inner<'this, S>(
            this: &'this mut EntityStorage<S>,
            key: EntityKeyRef<'_>,
        ) -> Option<&'this mut EntityContainer>
        where
            S: BuildHasher + Default,
        {
            let ei = this.entity_index(key)?;
            // Safety: Infallible.
            let cont = unsafe { this.map.get_group_mut(ei).unwrap_unchecked().0 };
            Some(cont)
        }
    }

    pub(crate) fn iter_entity_container(
        &self,
    ) -> impl Iterator<Item = (&Arc<[ComponentKey]>, EntityIndex, &EntityContainer)> {
        self.map.iter_group().map(|(ckeys, index, cont)| {
            (
                ckeys,
                EntityIndex::new(GenIndex::new(index as u32, self.ent_gens[index])),
                cont,
            )
        })
    }

    /// Registers new entity and its components information and returns entity
    /// container index. If you want to change entity information, you must
    /// remove if first. See [`Self::unregister_entity`]. Also, this method
    /// doesn't overwrite component information.
    pub(crate) fn register(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        if desc.is_empty() {
            let reason = debug_format!(
                "failed to register an entity: `{:?}` has no components",
                desc.cont.name
            );
            return Err(EcsError::InvalidEntity(reason, ()));
        }

        let ename = desc.cont.name.clone();
        let ety = desc.cont.ty().cloned();
        let index = match self.map.add_group(desc) {
            Ok(index) => index,
            Err(desc) => {
                let (_cont, _) = self.map.get_group2(&desc.group_key).unwrap();
                let reason = debug_format!(
                    "failed to register an entity: two entities `{:?}` and `{:?}` are the same",
                    ename,
                    _cont.name()
                );
                return Err(EcsError::InvalidEntity(reason, ()));
            }
        };
        let ei = EntityIndex::new(GenIndex::new(index as u32, self.gen));
        self.gen += 1;

        // Adds mapping.
        if let Some(name) = ename {
            self.name_to_index.insert(name, ei);
        }
        if let Some(ty) = ety {
            self.type_to_index.insert(ty, ei);
        }

        // Writes current generation on the slot.
        while self.ent_gens.len() <= index {
            self.ent_gens.push(0);
        }
        self.ent_gens[index] = ei.generation();

        Ok(ei)
    }

    /// Unregister entity and tries to unregister corresponding components as well.
    /// But components that are linked to another entity won't be unregistered.
    pub(crate) fn unregister<'r, K>(
        &mut self,
        key: K,
    ) -> Option<(Arc<[ComponentKey]>, EntityContainer)>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into());

        // === Internal helper functions ===

        fn inner<S>(
            this: &mut EntityStorage<S>,
            key: EntityKeyRef<'_>,
        ) -> Option<(Arc<[ComponentKey]>, EntityContainer)>
        where
            S: BuildHasher + Default,
        {
            let index = this.entity_index(key)?;
            let ckeys_cont = this.map.remove_group(index);
            debug_assert!(ckeys_cont.is_some());

            // Removes mapping.
            if let Some((_ckeys, cont)) = ckeys_cont.as_ref() {
                if let Some(name) = cont.name() {
                    this.name_to_index.remove(name);
                }
                if let Some(ty) = cont.ty() {
                    this.type_to_index.remove(ty);
                }
            }

            // In contrast to `register_entity()`, we don't need to reset generation in the slot
            // because we know that it doesn't exist.

            ckeys_cont
        }
    }

    pub(crate) fn entity_index<'r, K>(&self, key: K) -> Option<usize>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        return inner(self, key.into());

        // === Internal helper functions ===

        fn inner<S>(this: &EntityStorage<S>, key: EntityKeyRef<'_>) -> Option<usize>
        where
            S: BuildHasher + Default,
        {
            match key {
                EntityKeyRef::Name(name) => {
                    let ei = this.name_to_index.get(name)?;
                    this.is_valid_index(ei).then_some(ei.index())
                }
                EntityKeyRef::Index(ei) => this.is_valid_index(ei).then_some(ei.index()),
                EntityKeyRef::Type(ty) => {
                    let ei = this.type_to_index.get(ty)?;
                    this.is_valid_index(ei).then_some(ei.index())
                }
                EntityKeyRef::Ckeys(ckeys) => this.map.get_group_index(ckeys),
            }
        }
    }

    /// # Safety
    ///
    /// Undefine behavior if exclusive borrow happend before.
    //
    // Allows dead_code for test.
    #[allow(dead_code)]
    pub(crate) unsafe fn get_ptr(&self, ei: usize) -> Option<NonNull<dyn ContainEntity>> {
        let ptr = self.map.get_group(ei)?.0.cont.as_ref() as *const dyn ContainEntity;
        NonNull::new(ptr.cast_mut())
    }

    fn is_valid_index(&self, ei: &EntityIndex) -> bool {
        self.map.contains_group(ei.index()) && ei.generation() == self.ent_gens[ei.index()]
    }
}

impl<S> Default for EntityStorage<S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

/// A registration descriptor of an entity for [`EntityStorage`].
#[derive(Debug)]
pub struct EntityReg {
    cont: EntityContainer,
    key_info: Vec<(ComponentKey, TypeInfo)>,
}

impl EntityReg {
    pub fn new(
        name: Option<EntityName>,
        ty: Option<EntityTypeId>,
        cont: Box<dyn ContainEntity>,
    ) -> Self {
        Self {
            cont: EntityContainer::new(name, ty, cont),
            key_info: Vec::new(),
        }
    }

    pub fn add_component_of<C: Component>(&mut self) {
        self.add_component(C::type_info());
    }

    pub fn add_component(&mut self, tinfo: TypeInfo) {
        self.key_info.push((ComponentKey::from(&tinfo), tinfo));
    }

    fn is_empty(&self) -> bool {
        self.key_info.is_empty()
    }

    fn finish(self) -> GroupDesc<Arc<[ComponentKey]>, EntityContainer, ComponentKey, TypeInfo> {
        let Self {
            mut cont,
            mut key_info,
        } = self;

        // Sorts.
        let old_len = key_info.len();
        key_info.sort_unstable_by_key(|(key, _)| *key);
        key_info.dedup_by_key(|(key, _)| *key);
        assert_eq!(
            key_info.len(),
            old_len,
            "entity cannot have duplicated components"
        );

        // Completes container.
        let mut cnames = Vec::new();
        let mut ckeys = Vec::new();
        for (ckey, tinfo) in key_info.iter() {
            cont.cont.add_column(*tinfo);
            cnames.push(tinfo.name);
            ckeys.push(*ckey);
        }
        cont.ckeys = ckeys.into();
        cont.cnames = cnames.into();

        GroupDesc {
            group_key: Arc::clone(&cont.ckeys),
            group_value: cont,
            items: key_info,
        }
    }
}

impl DescribeGroup<Arc<[ComponentKey]>, EntityContainer, ComponentKey, TypeInfo> for EntityReg {
    fn into_group_and_items(
        self,
    ) -> GroupDesc<Arc<[ComponentKey]>, EntityContainer, ComponentKey, TypeInfo> {
        self.finish()
    }
}

/// A struct including entity information and its container.
/// The container holds component data without concrete type information.
pub struct EntityContainer {
    /// Optionally provided name of an entity contianer.
    name: Option<EntityName>,

    /// Optional type of the entity.
    /// Statically declared entities have this property.
    ty: Option<EntityTypeId>,

    /// Container that including components for the entity.
    cont: Box<dyn ContainEntity>,

    /// Pointer to the `dyn ContainEntity`.
    cont_ptr: SimpleHolder<NonNull<dyn ContainEntity>>,

    /// Sorted component keys.
    ///
    /// Note that this is sorted, so that index may be different with colum
    /// index used in [`Self::cont`].
    ckeys: Arc<[ComponentKey]>,

    /// Included component names.
    cnames: Box<[&'static str]>,
}

impl fmt::Debug for EntityContainer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EntityContainer")
            .field("name", &self.name)
            .field("ty", &self.ty)
            .field("cont_ptr", &self.cont_ptr)
            .field("ckeys", &self.ckeys)
            .field("cnames", &self.cnames)
            .finish_non_exhaustive()
    }
}

impl EntityContainer {
    pub(crate) fn new(
        name: Option<EntityName>,
        ty: Option<EntityTypeId>,
        mut cont: Box<dyn ContainEntity>,
    ) -> Self {
        // Safety: Infallible
        let ptr = unsafe { NonNull::new_unchecked(&mut *cont as *mut _) };

        // Removes remaining columns.
        for ci in (0..cont.num_columns()).rev() {
            let old_tinfo = cont.remove_column(ci);
            debug_assert!(old_tinfo.is_some());
        }

        Self {
            name,
            ty,
            cont,
            cont_ptr: SimpleHolder::new(ptr),
            ckeys: [].into(),
            cnames: [].into(),
        }
    }

    pub(crate) fn name(&self) -> Option<&EntityName> {
        self.name.as_ref()
    }

    pub(crate) fn ty(&self) -> Option<&EntityTypeId> {
        self.ty.as_ref()
    }

    pub(crate) fn component_keys(&self) -> &Arc<[ComponentKey]> {
        &self.ckeys
    }

    pub(crate) fn component_names(&self) -> &[&'static str] {
        &self.cnames
    }

    pub(crate) fn borrow(&self) -> BorrowResult<NonNull<dyn ContainEntity>> {
        self.cont_ptr.borrow()
    }

    pub(crate) fn borrow_mut(&mut self) -> BorrowResult<NonNull<dyn ContainEntity>> {
        self.cont_ptr.borrow_mut()
    }

    pub(crate) fn borrow_column_of<C: Component>(&self) -> BorrowResult<Getter<'_, C>> {
        let ci = self
            .get_column_index(&TypeId::of::<C>())
            .ok_or(BorrowError::NotFound)?;

        // Safety:
        // - We got `ci` from valid concrete type `C`.
        // - `Getter` is bounded container's lifetime `'cont`.
        let borrowed = unsafe {
            // Borrows the target column.
            let borrowed = self.borrow_column(ci).unwrap_unchecked();

            // Converts `RawGetter` into `Getter`.
            borrowed.map(|raw_getter| Getter::<'_, C>::from_raw(raw_getter))
        };
        Ok(borrowed)
    }

    pub(crate) fn borrow_column_of_mut<C: Component>(&mut self) -> BorrowResult<GetterMut<'_, C>> {
        let ci = self
            .get_column_index(&TypeId::of::<C>())
            .ok_or(BorrowError::NotFound)?;

        // Safety:
        // - We got `ci` from valid concrete type `C`.
        // - `GetterMut` is bounded container's lifetime `'cont`.
        let borrowed = unsafe {
            // Borrows the target column.
            let borrowed = self.borrow_column_mut(ci).unwrap_unchecked();

            // Converts `RawGetter` into `GetterMut`.
            borrowed.map(|raw_getter| GetterMut::<'_, C>::from_raw(raw_getter))
        };
        Ok(borrowed)
    }
}

impl Deref for EntityContainer {
    type Target = dyn ContainEntity;

    fn deref(&self) -> &Self::Target {
        &*self.cont
    }
}

impl DerefMut for EntityContainer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.cont
    }
}

#[derive(Debug)]
pub struct TypedEntityContainer<'buf, E> {
    ei: EntityIndex,
    ptr: NonNull<dyn ContainEntity>,
    _marker: PhantomData<&'buf mut E>,
}

impl<E: Entity> TypedEntityContainer<'_, E> {
    /// # Safety
    ///
    /// Given pointer must be valid.
    pub(crate) unsafe fn new(ei: EntityIndex, ptr: NonNull<dyn ContainEntity>) -> Self {
        Self {
            ei,
            ptr,
            _marker: PhantomData,
        }
    }

    /// Returns number of items.
    pub fn len(&self) -> usize {
        self.as_ref().len()
    }

    /// Returns `true` if the entity container is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns capacity if the entity container supports gauging capacity.
    /// Otherwise, returns number of items, which is equal to
    /// [`TypedEntityContainer::len`].
    pub fn capacity(&self) -> usize {
        self.as_ref().capacity()
    }

    /// Reserves extra `additional` capacity if the entity container supports to
    /// do so. Otherwise, nothing takes place.
    pub fn reserve(&mut self, additional: usize) {
        self.as_mut().reserve(additional);
    }

    pub fn shrink_to_fit(&mut self) {
        self.as_mut().shrink_to_fit();
    }

    /// Resizes the entity container to the new length by cloning the given
    /// value.
    ///
    /// Resizing occurs column by column.
    ///
    /// # Panics
    ///
    /// Panics if any components of the entity are not [`Clone`].
    pub fn resize(&mut self, new_len: usize, value: E) {
        for ci in 0..E::num_components() {
            // Safety: All columns are resized.
            unsafe {
                self.as_mut()
                    .resize_column(ci, new_len, value.component_ptr(ci));
            }
        }
    }

    /// Retrieves borrowed getter for a certain component column.
    ///
    /// If the component type doens't belong to the entity or the column was
    /// borrowed mutably in the past and not returned yet, returns None.
    pub fn get_column_of<C: Component>(&self) -> Option<Borrowed<Getter<'_, C>>> {
        let ci = self.as_ref().get_column_index(&TypeId::of::<C>())?;
        self.as_ref().borrow_column(ci).ok().map(|col| {
            // Safety: We got the column index from the type, so the type is correct.
            col.map(|raw_getter| unsafe { Getter::from_raw(raw_getter) })
        })
    }

    /// Retrives borrwoed mutable getter for a certain component column.
    ///
    /// If the component type doens't belong to the entity or the column was
    /// borrowed in the past and not returned yet, returns None.
    pub fn get_column_mut_of<C: Component>(&mut self) -> Option<Borrowed<GetterMut<'_, C>>> {
        let ci = self.as_ref().get_column_index(&TypeId::of::<C>())?;
        self.as_mut().borrow_column_mut(ci).ok().map(|col| {
            // Safety: We got the column index from the type, so the type is correct.
            col.map(|raw_getter| unsafe { GetterMut::from_raw(raw_getter) })
        })
    }

    /// Returns a struct holding shared references to components that belong
    /// to an entity for the given entity id.
    ///
    /// If it failed to find an enitty using the given entity id, returns
    /// `None`. See [`TypedEntityContainer::get_by_value_index`] for more
    /// details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// #[derive(Entity)]
    /// struct Ea {
    ///     ca: Ca,
    /// }
    /// #[derive(Component, Debug)]
    /// struct Ca(i32);
    ///
    /// fn system(mut ew: EntWrite<Ea>) {
    ///     let eid = ew.add(Ea { ca: Ca(0) });
    ///     println!("{:?}", ew.get(&eid).unwrap());
    /// }
    /// ```
    pub fn get(&self, eid: &EntityId) -> Option<E::Ref<'_>> {
        if eid.container_index() == self.ei {
            let vi = self.as_ref().to_value_index(eid.row_index())?;
            Some(self.get_by_value_index(vi))
        } else {
            None
        }
    }

    /// Returns a struct holding mutable references to components that belong
    /// to an entity for the given entity id.
    ///
    /// If it failed to find an enitty using the given entity id, returns
    /// `None`. See [`TypedEntityContainer::get_mut_by_value_index`] for more
    /// details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// #[derive(Entity)]
    /// struct Ea {
    ///     ca: Ca,
    /// }
    /// #[derive(Component, Debug)]
    /// struct Ca(i32);
    ///
    /// fn system(mut ew: EntWrite<Ea>) {
    ///     let eid = ew.add(Ea { ca: Ca(0) });
    ///     let ea = ew.get_mut(&eid).unwrap();
    ///     *ea.ca = Ca(42);
    ///     println!("{:?}", ew.get(&eid).unwrap());
    /// }
    /// ```
    pub fn get_mut(&mut self, eid: &EntityId) -> Option<E::Mut<'_>> {
        if eid.container_index() == self.ei {
            let vi = self.as_ref().to_value_index(eid.row_index())?;
            Some(self.get_mut_by_value_index(vi))
        } else {
            None
        }
    }

    /// Returns a struct holding shared references to components that belong
    /// to an entity for the given value index.
    ///
    /// Note, however, that entity is not stored as it is. It is split up into
    /// its components then stored in each component container. That means
    /// collecting those references like this function is inefficient because it
    /// requires random access to memory.
    ///
    /// # Panics
    ///
    /// Panics if the given value index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// #[derive(Entity)]
    /// struct Ea {
    ///     ca: Ca,
    /// }
    /// #[derive(Component, Debug)]
    /// struct Ca(i32);
    ///
    /// fn system(ew: EntWrite<Ea>) {
    ///     for vi in 0..ew.len() {
    ///         println!("{:?}", ew.get_by_value_index(vi));
    ///     }
    /// }
    /// ```
    pub fn get_by_value_index(&self, vi: usize) -> E::Ref<'_> {
        // Panics here.
        E::get_ref_from(self.as_ref(), vi)
    }

    /// Returns a struct holding mutable references to components that belong
    /// to an entity for the given value index.
    ///
    /// Note, however, that entity is not stored as it is. It is split up into
    /// its components then stored in each component container. That means
    /// collecting those references like this function is inefficient because it
    /// requires random access to memory.
    ///
    /// # Panics
    ///
    /// Panics if the given value index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use my_ecs::prelude::*;
    ///
    /// #[derive(Entity)]
    /// struct Ea {
    ///     ca: Ca,
    /// }
    /// #[derive(Component, Debug)]
    /// struct Ca(i32);
    ///
    /// fn system(mut ew: EntWrite<Ea>) {
    ///     for vi in 0..ew.len() {
    ///         let ea = ew.get_mut_by_value_index(vi);
    ///         *ea.ca = Ca(42);
    ///         println!("{:?}", ea);
    ///     }
    /// }
    /// ```
    pub fn get_mut_by_value_index(&mut self, vi: usize) -> E::Mut<'_> {
        // Panics here.
        E::get_mut_from(self.as_mut(), vi)
    }

    /// Inserts an entity to the entity container then returns entity id of the
    /// inserted entity.
    ///
    /// It's encouraged to use combination of [`TypedEntityContainer::resize`]
    /// and [`TypedEntityContainer::get_column_mut_of`] when you need to add
    /// lots of entites at once. It's more cache-friendly so it would be faster
    /// than calling to this method many times.
    pub fn add(&mut self, entity: E) -> EntityId {
        let ri = entity.move_to(self.as_mut());
        EntityId::new(self.ei, ri)
    }

    /// * `vi` - Value index. See [`ContainEntity`] document.
    ///
    /// # Panics
    ///
    /// Panics if the given value index is out of bounds.
    pub fn remove_by_value_index(&mut self, vi: usize) -> E {
        E::take_from(self.as_mut(), vi)
    }

    /// * `vi` - Value index. See [`ContainEntity`] document.
    ///
    /// # Panics
    ///
    /// Panics if the given value index is out of bounds.
    pub fn drop_by_value_index(&mut self, vi: usize) {
        self.as_mut().remove_row_by_value_index(vi);
    }

    fn as_ref(&self) -> &dyn ContainEntity {
        // Safety: Warning in the constructor.
        unsafe { self.ptr.as_ref() }
    }

    fn as_mut(&mut self) -> &mut dyn ContainEntity {
        // Safety: Warning in the constructor.
        unsafe { self.ptr.as_mut() }
    }
}
