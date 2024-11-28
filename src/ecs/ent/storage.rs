use super::{
    component::{Component, ComponentKey},
    entity::{
        ContainEntity, Entity, EntityIndex, EntityKey, EntityKeyKind, EntityName, EntityTypeId,
    },
    sparse_set::SparseSet,
};
use crate::ds::prelude::*;
use crate::ecs::EcsError;
use std::{
    any::TypeId,
    collections::HashMap,
    fmt,
    hash::BuildHasher,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

pub trait AsEntityReg {
    fn as_entity_descriptor() -> EntityReg;
}

/// Storage where you can find static entity and component information such as
/// names, types, and their relationships. Plus this storage has component data
/// for each entity in [`EntityContainer`].
///
/// Each container is basically identified by its component keys. In other
/// words, unique combination of components is the key of a container. So you
/// cannot register two entities that has the same components. But it is not
/// concise to search a container by its component keys, so entity must provide
/// unique name as well.
///
/// You can get or remove entries from their indices or keys. Using indices may
/// be faster than using keys in most cases.
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
    /// Data.
    data: GroupMap<Vec<ComponentKey>, EntityContainer, ComponentKey, TypeInfo, S>,

    /// Name -> index of the [`EntityContainer`] in the [`Self::data`].
    /// Each `EntityContainer` has its corresponding index.
    name_to_index: HashMap<EntityName, EntityIndex, S>,

    /// Type -> index of the [`EntityContainer`] in the [`Self::data`].
    /// This is optional, only statically declared entity has its type.
    type_to_index: HashMap<EntityTypeId, EntityIndex, S>,

    /// Generation of each entity container.
    /// The generation is when the container is registered to the dictionary.
    ent_gens: Vec<u32>,

    /// Current generation.
    gen: u32,
}

impl<S> EntityStorage<S>
where
    S: Default,
{
    pub(crate) fn new() -> Self {
        Self {
            data: GroupMap::new(),
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
    pub(crate) fn convert_entity_key(
        &self,
        ekey: &EntityKey,
        to: EntityKeyKind,
    ) -> Option<EntityKey> {
        let ei = self.entity_index(ekey)?;
        let res = match to {
            EntityKeyKind::Name => {
                // Safety: Infallible.
                let name = unsafe { self.data.get_group(ei).unwrap_unchecked().0.name() };
                EntityKey::Name(name.clone())
            }
            EntityKeyKind::Index => {
                let ei = EntityIndex::new(GenIndex::new(
                    ei as u32,
                    // Safety: Infallible.
                    unsafe { *self.ent_gens.get_unchecked(ei) },
                ));
                EntityKey::Index(ei)
            }
            EntityKeyKind::Type => {
                // Safety: Infallible.
                let ty = unsafe { self.data.get_group(ei).unwrap_unchecked().0.ty()? };
                EntityKey::Type(*ty)
            }
        };
        Some(res)
    }

    pub(crate) fn get_component_keys(&self, ekey: &EntityKey) -> Option<&Vec<ComponentKey>> {
        let ei = self.entity_index(ekey)?;
        // Safety: Infallible.
        let ckeys = unsafe { self.data.get_group_key(ei).unwrap_unchecked() };
        Some(ckeys)
    }

    pub(crate) fn get_entity_container(&self, ekey: &EntityKey) -> Option<&EntityContainer> {
        let ei = self.entity_index(ekey)?;
        // Safety: Infallible.
        let cont = unsafe { self.data.get_group(ei).unwrap_unchecked().0 };
        Some(cont)
    }

    pub(crate) fn get_entity_container_mut(
        &mut self,
        ekey: &EntityKey,
    ) -> Option<&mut EntityContainer> {
        let ei = self.entity_index(ekey)?;
        // Safety: Infallible.
        let cont = unsafe { self.data.get_group_mut(ei).unwrap_unchecked().0 };
        Some(cont)
    }

    pub(crate) fn iter_entity_container(
        &self,
    ) -> impl Iterator<Item = (&Vec<ComponentKey>, EntityIndex, &EntityContainer)> {
        self.data.iter_group().map(|(ckeys, index, cont)| {
            (
                ckeys,
                EntityIndex::new(GenIndex::new(index as u32, self.ent_gens[index])),
                cont,
            )
        })
    }

    /// Borrows entity container without checking generation.
    ///
    /// # Safety
    ///
    /// Undefined behavior if the index is out of bound.
    pub(crate) unsafe fn borrow_unchecked_mut(
        &mut self,
        ei: usize,
    ) -> BorrowResult<NonNull<dyn ContainEntity>> {
        self.data
            .get_group_mut(ei)
            .unwrap_unchecked()
            .0
            .borrow_mut()
    }

    /// Registers new entity and its components information and returns entity
    /// container index. If you want to change entity information, you must
    /// remove if first. See [`Self::unregister_entity`]. Also, this method
    /// doesn't overwrite component information.
    pub(crate) fn register(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        if desc.comps.is_empty() {
            let reason = crate::debug_format!("`{}` doesn't have any components", desc.cont.name);
            return Err(EcsError::InvalidEntity(reason, ()));
        }

        let name = desc.cont.name.clone();
        let ent_ty = desc.cont.ty().cloned();
        let index = match self.data.add_group(desc) {
            Ok(index) => index,
            Err(desc) => {
                let (_cont, _) = self.data.get_group2(&desc.group_key).unwrap();
                let reason = crate::debug_format!(
                    "`{name}` and `{}` have the same components, which is not allowed",
                    _cont.name()
                );
                return Err(EcsError::InvalidEntity(reason, ()));
            }
        };
        let ei = EntityIndex::new(GenIndex::new(index as u32, self.gen));
        self.gen += 1;

        // Adds mapping.
        self.name_to_index.insert(name, ei);
        if let Some(ty) = ent_ty {
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
    pub(crate) fn unregister(
        &mut self,
        ekey: &EntityKey,
    ) -> Option<(Vec<ComponentKey>, EntityContainer)> {
        let index = self.entity_index(ekey)?;
        let ckeys_cont = self.data.remove_group(index);
        debug_assert!(ckeys_cont.is_some());

        // Removes mapping.
        if let Some((_ckeys, cont)) = ckeys_cont.as_ref() {
            self.name_to_index.remove(cont.name());
            if let Some(ty) = cont.ty() {
                self.type_to_index.remove(ty);
            }
        }

        // In contrast to `register_entity()`, we don't need to reset generation in the slot
        // because we know that it doesn't exist.

        ckeys_cont
    }

    pub(crate) fn entity_index(&self, ekey: &EntityKey) -> Option<usize> {
        match ekey {
            EntityKey::Index(ei) => self.is_valid_index(ei).then_some(ei.index()),
            EntityKey::Name(name) => {
                let ei = self.name_to_index.get(name)?;
                self.is_valid_index(ei).then_some(ei.index())
            }
            EntityKey::Type(ty) => {
                let ei = self.type_to_index.get(ty)?;
                self.is_valid_index(ei).then_some(ei.index())
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
        let ptr = self.data.get_group(ei)?.0.cont.as_ref() as *const dyn ContainEntity;
        NonNull::new(ptr.cast_mut())
    }

    fn is_valid_index(&self, ei: &EntityIndex) -> bool {
        self.data.contains_group(ei.index()) && ei.generation() == self.ent_gens[ei.index()]
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
    comps: Vec<(ComponentKey, TypeInfo)>,
}

impl EntityReg {
    /// You can pass your own empty component container `cont`, otherwise [`SparseSet`] is used.
    pub fn new(name: EntityName, ty: Option<EntityTypeId>, cont: Box<dyn ContainEntity>) -> Self {
        Self {
            cont: EntityContainer::new(name, ty, cont, Vec::new()),
            comps: Vec::new(),
        }
    }

    pub fn new_with_default_container<S>(name: EntityName, ty: Option<EntityTypeId>) -> Self
    where
        S: BuildHasher + Default + Clone + 'static,
    {
        Self::new(name, ty, Box::new(SparseSet::<S>::new()))
    }

    pub fn add_component(&mut self, tinfo: TypeInfo) {
        if !self.cont.cont.contains_column(&tinfo.ty) {
            self.cont.cont.add_column(tinfo);
        }
        self.comps.push((ComponentKey::from(&tinfo), tinfo));
        self.cont.comp_names.push(tinfo.name);
    }
}

impl DescribeGroup<Vec<ComponentKey>, EntityContainer, ComponentKey, TypeInfo> for EntityReg {
    fn into_group_and_items(
        self,
    ) -> GroupDesc<Vec<ComponentKey>, EntityContainer, ComponentKey, TypeInfo> {
        let Self { cont, comps } = self;

        let group_key = comps.iter().map(|(ty, _)| *ty).collect::<Vec<_>>();

        GroupDesc {
            group_key,
            group_value: cont,
            items: comps,
        }
    }
}

/// A structure including entity information and its container.
/// The container holds component data without concrete type information.
pub struct EntityContainer {
    /// Unique name of the entity, which will be used as a key to find this container.
    /// See [`EntityKey::Name`].
    name: EntityName,

    /// Optional type of the entity.
    /// Statically declared entities have this property.
    ty: Option<EntityTypeId>,

    /// Container that including components for the entity.
    cont: Box<dyn ContainEntity>,

    /// Pointer to the `dyn ContainEntity`.
    cont_ptr: SimpleHolder<NonNull<dyn ContainEntity>>,

    /// Included component names just for users.
    comp_names: Vec<&'static str>,
}

impl fmt::Debug for EntityContainer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EntityContainer")
            .field("name", &self.name)
            .field("ty", &self.ty)
            .field("cont_ptr", &self.cont_ptr)
            .field("comp_names", &self.comp_names)
            .finish_non_exhaustive()
    }
}

impl EntityContainer {
    pub(crate) fn new(
        name: EntityName,
        ty: Option<EntityTypeId>,
        mut cont: Box<dyn ContainEntity>,
        comp_names: Vec<&'static str>,
    ) -> Self {
        // Safety: Infallible
        let ptr = unsafe { NonNull::new_unchecked(&mut *cont as *mut _) };

        Self {
            name,
            ty,
            cont,
            cont_ptr: SimpleHolder::new(ptr),
            comp_names,
        }
    }

    pub fn name(&self) -> &EntityName {
        &self.name
    }

    pub fn ty(&self) -> Option<&EntityTypeId> {
        self.ty.as_ref()
    }

    pub fn comp_names(&self) -> &Vec<&'static str> {
        &self.comp_names
    }

    pub fn borrow(&self) -> BorrowResult<NonNull<dyn ContainEntity>> {
        self.cont_ptr.borrow()
    }

    pub fn borrow_mut(&mut self) -> BorrowResult<NonNull<dyn ContainEntity>> {
        self.cont_ptr.borrow_mut()
    }

    pub fn borrow_column_of<C: Component>(&self) -> BorrowResult<Getter<'_, C>> {
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

    pub fn borrow_column_of_mut<C: Component>(&mut self) -> BorrowResult<GetterMut<'_, C>> {
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
#[repr(transparent)]
pub struct TypedEntityContainer<'buf, E> {
    ptr: NonNull<dyn ContainEntity>,
    _marker: PhantomData<&'buf mut E>,
}

impl<'buf, E: Entity> TypedEntityContainer<'buf, E> {
    /// # Safety
    ///
    /// Given pointer must be valid.
    pub(crate) unsafe fn new(ptr: NonNull<dyn ContainEntity>) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }

    /// Returns number of items.
    pub fn len(&self) -> usize {
        self.as_ref().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get_component_mut<C: Component>(&mut self) -> Option<Borrowed<GetterMut<C>>> {
        let ci = self.as_ref().get_column_index(&TypeId::of::<C>())?;
        if let Ok(borrowed) = self.as_ref().borrow_column(ci) {
            // Safety: We got the column index from the type, so the type is correct.
            Some(borrowed.map(|raw_getter| unsafe { GetterMut::from_raw(raw_getter) }))
        } else {
            None
        }
    }

    pub fn add_entity(&mut self, value: E) {
        value.move_to(self.as_mut());
    }

    /// * `vi` - Value index. See [`ContainEntity`].
    pub fn remove_row_by_value_index(&mut self, vi: usize) {
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
