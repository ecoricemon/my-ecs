use super::{
    cache::{CacheStorage, RefreshCacheStorage},
    ent::{
        entity::{Entity, EntityId, EntityIndex, EntityKey},
        storage::{AsEntityReg, EntityContainer, EntityReg, EntityStorage},
    },
    resource::{Resource, ResourceDesc, ResourceKey, ResourceStorage},
    sched::ctrl::Scheduler,
    sys::{
        storage::{SystemDesc, SystemStorage},
        system::{
            InsertPos, NonZeroTick, PrivateSystem, System, SystemData, SystemFlags, SystemId,
        },
    },
    worker::Work,
    EcsError,
};
use crate::util::prelude::*;
use std::{
    any::Any,
    fmt::Debug,
    hash::{BuildHasher, RandomState},
    marker::PhantomData,
    mem,
    ptr::NonNull,
};

pub trait EcsEntry {
    fn add_system<Sys>(&mut self, desc: SystemDesc<Sys>) -> Result<SystemId, EcsError>
    where
        Sys: System;

    fn unregister_system(&mut self, gi: usize, sid: SystemId) -> Option<SystemData>;

    /// Activates the system. If the system is already active, nothing takes place.
    fn activate_system(
        &mut self,
        target: SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError>;

    fn inactivate_system(&mut self, gi: usize, sid: SystemId) -> Result<(), EcsError>;

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError>;

    fn register_entity_of<T: AsEntityReg>(&mut self) -> Result<EntityIndex, EcsError>;

    fn unregister_entity<Q: Into<EntityKey>>(
        &mut self,
        ekey: Q,
    ) -> Result<EntityContainer, EcsError>;

    fn add_entity<E>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError>
    where
        E: Entity;

    /// Registers the resource.
    /// If the registration failed, nothing takes place and returns received value.
    /// In other words, the old resouce data won't be dropped.
    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), ResourceDesc>;

    fn unregister_resource(&mut self, rkey: ResourceKey) -> Result<Option<Box<dyn Any>>, EcsError>;
}

#[rustfmt::skip]
#[allow(clippy::type_complexity)]
#[derive(Debug)]
struct EcsVTable {
    register_system_inner:
        unsafe fn(NonNull<u8>, SystemData, u16, bool, bool)
        -> Result<SystemId, EcsError>,

    unregister_system_inner: 
        unsafe fn(NonNull<u8>, usize, &SystemId) -> Option<SystemData>,

    activate_system_inner:
        unsafe fn(NonNull<u8>, &SystemId, InsertPos, NonZeroTick) 
        -> Result<(), EcsError>,

    inactivate_system_inner: 
        unsafe fn(NonNull<u8>, usize, &SystemId) -> Result<(), EcsError>,

    register_entity_inner: 
        unsafe fn(NonNull<u8>, EntityReg) -> Result<EntityIndex, EcsError>,

    unregister_entity_inner:
        unsafe fn(NonNull<u8>, EntityKey) -> Result<EntityContainer, EcsError>,

    register_resource_inner:
        unsafe fn(NonNull<u8>, ResourceDesc) -> Result<(), ResourceDesc>,
    
    unregister_resource_inner:
        unsafe fn(NonNull<u8>, ResourceKey) 
        -> Result<Option<Box<dyn Any>>, EcsError>,
    
    get_entity_container_mut: 
        unsafe fn(NonNull<u8>, &EntityKey) -> Option<&mut EntityContainer>,
}

impl EcsVTable {
    fn new<W, S, const N: usize>() -> Self
    where
        W: Work + 'static,
        S: BuildHasher + Default + 'static,
    {
        unsafe fn register_system_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            sdata: SystemData,
            group_index: u16,
            volatile: bool,
            private: bool,
        ) -> Result<SystemId, EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.register_system_inner(sdata, group_index, volatile, private)
        }

        unsafe fn unregister_system_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            gi: usize,
            sid: &SystemId,
        ) -> Option<SystemData>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.unregister_system_inner(gi, sid)
        }

        unsafe fn activate_system_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            target: &SystemId,
            at: InsertPos,
            live: NonZeroTick,
        ) -> Result<(), EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.activate_system_inner(target, at, live)
        }

        unsafe fn inactivate_system_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            gi: usize,
            sid: &SystemId,
        ) -> Result<(), EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.inactivate_system_inner(gi, sid)
        }

        unsafe fn register_entity_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            desc: EntityReg,
        ) -> Result<EntityIndex, EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.register_entity_inner(desc)
        }

        unsafe fn unregister_entity_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            ekey: EntityKey,
        ) -> Result<EntityContainer, EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.unregister_entity_inner(ekey)
        }

        unsafe fn register_resource_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            desc: ResourceDesc,
        ) -> Result<(), ResourceDesc>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.register_resource_inner(desc)
        }

        unsafe fn unregister_resource_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            rkey: ResourceKey,
        ) -> Result<Option<Box<dyn Any>>, EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.unregister_resource_inner(rkey)
        }

        unsafe fn get_entity_container_mut<'i, 'o, W, S, const N: usize>(
            this: NonNull<u8>,
            ekey: &'i EntityKey,
        ) -> Option<&'o mut EntityContainer>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &'o mut EcsApp<W, S, N> = this.cast().as_mut();
            this.get_entity_container_mut(ekey)
        }

        Self {
            register_system_inner: register_system_inner::<W, S, N>,
            unregister_system_inner: unregister_system_inner::<W, S, N>,
            activate_system_inner: activate_system_inner::<W, S, N>,
            inactivate_system_inner: inactivate_system_inner::<W, S, N>,
            register_entity_inner: register_entity_inner::<W, S, N>,
            unregister_entity_inner: unregister_entity_inner::<W, S, N>,
            register_resource_inner: register_resource_inner::<W, S, N>,
            unregister_resource_inner: unregister_resource_inner::<W, S, N>,
            get_entity_container_mut: get_entity_container_mut::<W, S, N>,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Ecs<'ecs> {
    this: NonNull<u8>,
    vtable: NonNull<EcsVTable>,
    _marker: PhantomData<&'ecs mut ()>,
}

impl<'ecs> Ecs<'ecs> {
    pub fn default<Wp, W, const N: usize>(pool: Wp, nums: [usize; N]) -> EcsApp<W, RandomState, N>
    where
        Wp: Into<Vec<W>>,
        W: Work + 'static,
    {
        Self::create(pool.into(), nums)
    }

    pub fn create<W, S, const N: usize>(workers: Vec<W>, nums: [usize; N]) -> EcsApp<W, S, N>
    where
        W: Work + 'static,
        S: BuildHasher + Default + 'static,
    {
        EcsApp::new(workers, nums)
    }

    fn new<W, S, const N: usize>(ecs: &'ecs mut EcsApp<W, S, N>) -> Self
    where
        W: Work + 'static,
        S: BuildHasher + Default + 'static,
    {
        unsafe {
            let this = NonNull::new_unchecked(ecs as *mut _ as *mut u8);
            let vtable = NonNull::new_unchecked(&mut ecs.vtable as *mut _);
            Self {
                this,
                vtable,
                _marker: PhantomData,
            }
        }
    }
}

impl<'ecs> EcsEntry for Ecs<'ecs> {
    fn add_system<S>(&mut self, desc: SystemDesc<S>) -> Result<SystemId, EcsError>
    where
        S: System,
    {
        let SystemDesc {
            sys,
            private,
            group_index,
            volatile,
            activation,
        } = desc;
        let sdata = match sys {
            Or::A(sys) => sys.into_data(),
            Or::B(sdata) => sdata,
        };

        // Registers.
        let res = unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_system_inner)(self.this, sdata, group_index, volatile, private)
        };

        // @@@ TODO: failed then unregister it.
        // Activates.
        if let Ok(sid) = res.as_ref() {
            if let Some((live, at)) = activation {
                let must_ok = self.activate_system(*sid, at, live);
                assert!(must_ok.is_ok());
            }
        }
        res
    }

    fn unregister_system(&mut self, gi: usize, sid: SystemId) -> Option<SystemData> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_system_inner)(self.this, gi, &sid)
        }
    }

    fn activate_system(
        &mut self,
        target: SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.activate_system_inner)(self.this, &target, at, live)
        }
    }

    fn inactivate_system(&mut self, gi: usize, sid: SystemId) -> Result<(), EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.inactivate_system_inner)(self.this, gi, &sid)
        }
    }

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_entity_inner)(self.this, desc)
        }
    }

    fn register_entity_of<T: AsEntityReg>(&mut self) -> Result<EntityIndex, EcsError> {
        self.register_entity(T::as_entity_descriptor())
    }

    fn unregister_entity<Q: Into<EntityKey>>(
        &mut self,
        ekey: Q,
    ) -> Result<EntityContainer, EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_entity_inner)(self.this, ekey.into())
        }
    }

    fn add_entity<E: Entity>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            if let Some(cont) = (vtable.get_entity_container_mut)(self.this, &EntityKey::from(ei)) {
                let itemi = value.move_to(&mut **cont);
                Ok(EntityId::new(ei, itemi))
            } else {
                let errmsg = debug_format!("{}", std::any::type_name::<E>());
                Err(EcsError::UnknownEntity(errmsg))
            }
        }
    }

    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), ResourceDesc> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_resource_inner)(self.this, desc)
        }
    }

    fn unregister_resource(&mut self, rkey: ResourceKey) -> Result<Option<Box<dyn Any>>, EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_resource_inner)(self.this, rkey)
        }
    }
}

/// * `W` - Worker type.
/// * `S` - Hasher.
/// * `N` - Number of groups.
//
// We know N > 0 due to the validation in `Multi`.
#[derive(Debug)]
pub struct EcsApp<W, S = std::hash::RandomState, const N: usize = 1> {
    /// System storage.
    sys_stor: SystemStorage<S, N>,

    /// Entity and component storage.
    /// The storage contains all kinds of entities and components.
    ent_stor: EntityStorage<S>,

    /// Resource storage.
    /// The storage contains pointers to resources.
    res_stor: ResourceStorage<S>,

    cache_stor: CacheStorage<S>,

    sched: Scheduler<W, S, N>,

    vtable: EcsVTable,
}

impl<W, S, const N: usize> EcsApp<W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    pub fn new(workers: Vec<W>, nums: [usize; N]) -> Self {
        Self {
            sys_stor: SystemStorage::new(),
            ent_stor: EntityStorage::new(),
            res_stor: ResourceStorage::new(),
            cache_stor: CacheStorage::new(),
            sched: Scheduler::new(workers, nums),
            vtable: EcsVTable::new::<W, S, N>(),
        }
    }

    pub fn set_workers(&mut self, workers: Vec<W>, nums: [usize; N]) -> Vec<W> {
        let old = mem::replace(&mut self.sched, Scheduler::new(workers, nums));
        old.take_workers()
    }

    pub fn collect_poisoned_systems(&mut self) -> Vec<(SystemData, Box<dyn Any + Send>)> {
        self.sys_stor.collect_poisoned()
    }

    #[must_use]
    pub fn run(&mut self) -> RunningEcs<'_, W, S, N> {
        RunningEcs::new(self)
    }

    fn register_system_inner(
        &mut self,
        mut sdata: SystemData,
        group_index: u16,
        volatile: bool,
        private: bool,
    ) -> Result<SystemId, EcsError> {
        validate_request::<W, S, N>(self, &sdata)?;
        complete_data::<W, S, N>(self, &mut sdata, group_index, private);
        let sid = sdata.id();
        self.cache_stor
            .update_by_system_reg(&sdata, &mut self.ent_stor, &mut self.res_stor);
        self.sys_stor.register(sdata, group_index, volatile);
        return Ok(sid);

        // === Internal helper functions ===

        fn validate_request<Wp, S, const N: usize>(
            this: &EcsApp<Wp, S, N>,
            sdata: &SystemData,
        ) -> Result<(), EcsError>
        where
            S: BuildHasher + Default + 'static,
        {
            // Validation procedure is as follows.
            // 1. Validates `Read`, `Write`, `ResRead`, `ResWrite`, and `EntWrite`.
            // 2. Validates if queried "Resources" and "Entities" exist.
            //    When it comes to "resource and entity queries",
            //    in contrast to "component queries",
            //    they must be known at the time of system registration.
            //    Why? assume that clients forgot to register
            //    required resource or entity.
            //    Then, we can't give them to systems.
            //    But about components, we can give empty iterator somehow.

            // 1. Validates request's `Read`, `Write`, `ResRead`, and `ResWrite`.
            // `EntWrite` will be validated soon.
            let rinfo = sdata.get_request_info();
            if let Err(errmsg) = rinfo.validate() {
                return Err(EcsError::InvalidRequest(errmsg));
            }

            // 2. Validates queried resources.
            for rkey in rinfo.resource_keys() {
                if !this.res_stor.contains(rkey) {
                    let errmsg = debug_format!("failed to find a resource `{:?}`", rkey);
                    return Err(EcsError::UnknownResource(errmsg));
                }
            }

            // 1. Validates request's `EntWrite`.
            // 2. Validates queried entities.
            let (_, r_qinfo) = rinfo.read();
            let (_, w_qinfo) = rinfo.write();
            let r_filters = r_qinfo.filters();
            let w_filters = w_qinfo.filters();
            let filters = r_filters.iter().chain(w_filters);
            for ekey in rinfo.entity_keys() {
                if let Some(cont) = this.ent_stor.get_entity_container(ekey) {
                    for (_, finfo) in filters.clone() {
                        if finfo.filter(|ckey| cont.contains_column(ckey)) {
                            let errmsg = debug_format!(
                                "entity query `{:?}` cannot be coexist with filter `{}` in `{}`, they conflict",
                                ekey,
                                finfo.name(),
                                rinfo.name(),
                            );
                            return Err(EcsError::InvalidRequest(errmsg));
                        }
                    }
                } else {
                    let errmsg = debug_format!("failed to find an entity `{:?}`", ekey);
                    return Err(EcsError::UnknownEntity(errmsg));
                }
            }

            Ok(())
        }

        fn complete_data<Wp, S, const N: usize>(
            this: &mut EcsApp<Wp, S, N>,
            sdata: &mut SystemData,
            group_index: u16,
            private: bool,
        ) where
            S: BuildHasher + Default + 'static,
        {
            // Completes system id.
            debug_assert!(sdata.id().is_dummy());
            {
                let sid = this
                    .sys_stor
                    .get_group_mut(group_index as usize)
                    .next_system_id();
                sdata.set_id(sid);
            }

            // Completes system flags.
            debug_assert!(sdata.flags().is_dedi_empty() && sdata.flags().is_private_empty());
            {
                let mut sflags = SystemFlags::empty();

                // Is dedicated system?
                let res_read = &sdata.get_request_info().res_read().1;
                let res_write = &sdata.get_request_info().res_write().1;
                if res_read
                    .rkeys()
                    .iter()
                    .chain(res_write.rkeys())
                    .any(|rkey| this.res_stor.is_dedicated2(rkey))
                {
                    sflags |= SystemFlags::DEDI_SET;
                } else {
                    sflags |= SystemFlags::DEDI_RESET;
                }

                // Is private system?
                if private {
                    sflags |= SystemFlags::PRIVATE_SET;
                } else {
                    sflags |= SystemFlags::PRIVATE_RESET;
                }

                sdata.union_flags(sflags);
            }
        }
    }

    fn unregister_system_inner(&mut self, gi: usize, sid: &SystemId) -> Option<SystemData> {
        self.cache_stor.update_by_system_unreg(sid);
        self.sys_stor.unregister(gi, sid)
    }

    fn activate_system_inner(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        mut live: NonZeroTick,
    ) -> Result<(), EcsError> {
        // It can be in the middle of scheduling,
        // which means there may be no chance to run target system in this time.
        // In that case, we need to add `live` by 1 to guarantee the total number of run.
        match at {
            InsertPos::Back => { /* target must be run in this time */ }
            InsertPos::Front => {
                if !self.sched.get_record_mut().is_empty() {
                    live = live.saturating_add(1);
                }
            }
            InsertPos::After(after) => {
                let sgroup = self.sys_stor.get_group_mut(after.group_index() as usize);
                if let Some(next) = sgroup.get_active_mut().peek_next(&after) {
                    if self.sched.get_record_mut().contains(&next.id()) {
                        live = live.saturating_add(1);
                    }
                }
            }
        }

        // Activates it.
        self.sys_stor.activate(target, at, live)
    }

    fn inactivate_system_inner(&mut self, gi: usize, sid: &SystemId) -> Result<(), EcsError> {
        self.sys_stor.inactivate(gi, sid)
    }

    fn register_entity_inner(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        // Registers entity.
        let ei = self.ent_stor.register(desc)?;
        self.cache_stor
            .update_by_entity_reg(ei, &mut self.ent_stor, &mut self.res_stor);

        // Makes wait queue for the entity.
        let cont = unsafe {
            self.ent_stor
                .get_entity_container(&EntityKey::from(ei))
                .unwrap_unchecked()
        };
        self.sched
            .get_wait_queues_mut()
            .initialize_entity_queue(ei.index(), cont.get_column_num());

        Ok(ei)
    }

    fn unregister_entity_inner(&mut self, ekey: EntityKey) -> Result<EntityContainer, EcsError> {
        self.cache_stor.update_by_entity_unreg(
            ekey.clone(),
            &mut self.ent_stor,
            &mut self.res_stor,
        );
        if let Some((_, cont)) = self.ent_stor.unregister(&ekey) {
            Ok(cont)
        } else {
            let errmsg = debug_format!("failed to find an entity `{:?}`", ekey);
            Err(EcsError::UnknownEntity(errmsg))
        }
    }

    fn register_resource_inner(&mut self, desc: ResourceDesc) -> Result<(), ResourceDesc> {
        let index = self.res_stor.register(desc)?;
        self.sched
            .get_wait_queues_mut()
            .initialize_resource_queue(index);
        Ok(())
    }

    fn unregister_resource_inner(
        &mut self,
        rkey: ResourceKey,
    ) -> Result<Option<Box<dyn Any>>, EcsError> {
        self.cache_stor.update_by_resource_unreg(rkey);
        match self.res_stor.unregister(&rkey) {
            Some(Or::A(owned)) => Ok(Some(owned)),
            Some(Or::B(_ptr)) => Ok(None),
            None => {
                let errmsg = debug_format!("failed to find an resource `{:?}`", rkey);
                Err(EcsError::UnknownResource(errmsg))
            }
        }
    }

    fn process_buffered_commands(&mut self) {
        // `raw` borrows `Self` mutably, so we cannot access `sched` in it.
        // So captures its address first.
        let sched_ptr: *const Scheduler<W, S, N> = &self.sched as *const _;
        let raw = Ecs::new(self);

        // TODO: Removes unsafefy. Should I flip call hierarchy.
        unsafe {
            let sched = sched_ptr.as_ref().unwrap_unchecked();
            sched.consume_commands(|cmd| {
                cmd.command(raw);
            });
        }
    }

    fn get_entity_container_mut(&mut self, ekey: &EntityKey) -> Option<&mut EntityContainer> {
        self.ent_stor.get_entity_container_mut(ekey)
    }
}

impl<W, S, const N: usize> Drop for EcsApp<W, S, N> {
    fn drop(&mut self) {
        // Cancels out all active systems.
        self.sys_stor.cancel_active();
    }
}

impl<W, S, const N: usize> EcsEntry for EcsApp<W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    fn add_system<Sys>(&mut self, desc: SystemDesc<Sys>) -> Result<SystemId, EcsError>
    where
        Sys: System,
    {
        Ecs::new(self).add_system(desc)
    }

    fn unregister_system(&mut self, gi: usize, sid: SystemId) -> Option<SystemData> {
        Ecs::new(self).unregister_system(gi, sid)
    }

    fn activate_system(
        &mut self,
        target: SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError> {
        Ecs::new(self).activate_system(target, at, live)
    }

    fn inactivate_system(&mut self, gi: usize, sid: SystemId) -> Result<(), EcsError> {
        Ecs::new(self).inactivate_system(gi, sid)
    }

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        Ecs::new(self).register_entity(desc)
    }

    fn register_entity_of<T: AsEntityReg>(&mut self) -> Result<EntityIndex, EcsError> {
        Ecs::new(self).register_entity_of::<T>()
    }

    fn unregister_entity<Q: Into<EntityKey>>(
        &mut self,
        ekey: Q,
    ) -> Result<EntityContainer, EcsError> {
        Ecs::new(self).unregister_entity(ekey)
    }

    fn add_entity<E: Entity>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError> {
        Ecs::new(self).add_entity(ei, value)
    }

    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), ResourceDesc> {
        Ecs::new(self).register_resource(desc)
    }

    fn unregister_resource(&mut self, rkey: ResourceKey) -> Result<Option<Box<dyn Any>>, EcsError> {
        Ecs::new(self).unregister_resource(rkey)
    }
}

impl<W, S, const N: usize> Resource for EcsApp<W, S, N> where EcsApp<W, S, N>: Send + 'static {}

#[repr(transparent)]
pub struct RunningEcs<'ecs, W, S, const N: usize> {
    ecs: &'ecs mut EcsApp<W, S, N>,
}

impl<'ecs, W, S, const N: usize> RunningEcs<'ecs, W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    fn new(ecs: &'ecs mut EcsApp<W, S, N>) -> Self {
        Self { ecs }
    }

    pub fn schedule_all(&mut self) -> &mut Self {
        // Executes.
        if self.has_active_system() {
            let sgroups = self.ecs.sys_stor.sgroups.items_mut();
            let mut cache = RefreshCacheStorage::new(
                &mut self.ecs.cache_stor,
                &mut self.ecs.ent_stor,
                &mut self.ecs.res_stor,
            );
            self.ecs.sched.execute_all(sgroups, &mut cache);
        }

        // Consumes buffered commands.
        self.ecs.process_buffered_commands();

        self
    }

    // @@@ TODO : Easy API
    pub fn wait_for_idle(&mut self) -> &mut Self {
        self.ecs.sched.wait_exhausted();
        self
    }

    // @@@ TODO : Easy API
    /// Determines whether ECS has run completely, so that it cannot do anything.
    ///
    /// What conditions are considered?
    /// - For sub workers,
    ///   - Are all sub workers closed?
    ///   - Or, are all sub workers idle & Isn't there any running future
    ///     task?
    /// - For main worker,
    ///   - Isn't there any active system?
    ///   - Isn't there any uncompleted command?
    pub fn is_completed(&self) -> bool {
        // For sub workers, they are closed?
        let is_sub_exhausted = self.ecs.sched.is_work_groups_exhausted();

        // For main worker, no active system?
        let no_active = self
            .ecs
            .sys_stor
            .sgroups
            .iter()
            .all(|sgroup| sgroup.len_active() == 0);

        // For main worker, no uncompleted command?
        let no_cmd = !self.ecs.sched.has_command();

        is_sub_exhausted && no_active && no_cmd
    }

    fn has_active_system(&self) -> bool {
        self.ecs
            .sys_stor
            .sgroups
            .iter()
            .any(|sgroup| sgroup.len_active() > 0)
    }
}
