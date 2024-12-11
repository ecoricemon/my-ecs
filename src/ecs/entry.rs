use super::{
    cache::{CacheStorage, RefreshCacheStorage},
    cmd::EntMoveStorage,
    ent::{
        entity::{Entity, EntityId, EntityIndex, EntityKeyRef},
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
    ops::Deref,
    ptr::NonNull,
    sync::{Arc, Mutex, MutexGuard},
};

pub trait EcsEntry {
    fn add_system<Sys>(&mut self, desc: SystemDesc<Sys>) -> Result<SystemId, EcsError<SystemData>>
    where
        Sys: System;

    fn unregister_system(&mut self, sid: SystemId) -> Result<(), EcsError>;

    /// Activates the system. If the system is already active, nothing takes place.
    fn activate_system(
        &mut self,
        target: SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError>;

    fn inactivate_system(&mut self, sid: SystemId) -> Result<(), EcsError>;

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError>;

    fn register_entity_of<T>(&mut self) -> Result<EntityIndex, EcsError>
    where
        T: AsEntityReg;

    fn unregister_entity<'r, K>(&mut self, ekey: K) -> Result<EntityContainer, EcsError>
    where
        K: Into<EntityKeyRef<'r>>;

    fn add_entity<E>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError<E>>
    where
        E: Entity;

    /// Registers the resource.
    /// If the registration failed, nothing takes place and returns received value.
    /// In other words, the old resouce data won't be dropped.
    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), EcsError<ResourceDesc>>;

    fn unregister_resource(&mut self, rkey: &ResourceKey)
        -> Result<Option<Box<dyn Any>>, EcsError>;
}

#[rustfmt::skip]
#[allow(clippy::type_complexity)]
#[derive(Debug)]
struct EcsVTable {
    register_system_inner:
        unsafe fn(NonNull<u8>, SystemData, u16, bool, bool)
        -> Result<SystemId, EcsError<SystemData>>,

    unregister_system_inner: 
        unsafe fn(NonNull<u8>, &SystemId) -> Result<(), EcsError>,

    activate_system_inner:
        unsafe fn(NonNull<u8>, &SystemId, InsertPos, NonZeroTick) 
        -> Result<(), EcsError>,

    inactivate_system_inner: 
        unsafe fn(NonNull<u8>, &SystemId) -> Result<(), EcsError>,

    register_entity_inner: 
        unsafe fn(NonNull<u8>, EntityReg) -> Result<EntityIndex, EcsError>,

    unregister_entity_inner:
        unsafe fn(NonNull<u8>, EntityKeyRef<'_>) -> Result<EntityContainer, EcsError>,

    register_resource_inner:
        unsafe fn(NonNull<u8>, ResourceDesc)
        -> Result<(), EcsError<ResourceDesc>>,
    
    unregister_resource_inner:
        unsafe fn(NonNull<u8>, &ResourceKey)
        -> Result<Option<Box<dyn Any>>, EcsError>,
    
    get_entity_container_mut: 
        unsafe fn(NonNull<u8>, EntityKeyRef<'_>) -> Option<&mut EntityContainer>,

    get_shared:
        unsafe fn(NonNull<u8>) -> NonNull<Shared>,
    
    schedule_all:
        unsafe fn(NonNull<u8>),
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
        ) -> Result<SystemId, EcsError<SystemData>>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.register_system_inner(sdata, group_index, volatile, private)
        }

        unsafe fn unregister_system_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            sid: &SystemId,
        ) -> Result<(), EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.unregister_system_inner(sid)
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
            sid: &SystemId,
        ) -> Result<(), EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.inactivate_system_inner(sid)
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
            ekey: EntityKeyRef<'_>,
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
        ) -> Result<(), EcsError<ResourceDesc>>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.register_resource_inner(desc)
        }

        unsafe fn unregister_resource_inner<W, S, const N: usize>(
            this: NonNull<u8>,
            rkey: &ResourceKey,
        ) -> Result<Option<Box<dyn Any>>, EcsError>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.unregister_resource_inner(rkey)
        }

        unsafe fn get_entity_container_mut<'o, W, S, const N: usize>(
            this: NonNull<u8>,
            ekey: EntityKeyRef<'_>,
        ) -> Option<&'o mut EntityContainer>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &'o mut EcsApp<W, S, N> = this.cast().as_mut();
            this.get_entity_container_mut(ekey)
        }

        unsafe fn get_shared<W, S, const N: usize>(this: NonNull<u8>) -> NonNull<Shared>
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            let shared = this.shared.as_ref();
            let ptr = (shared as *const Shared).cast_mut();
            NonNull::new_unchecked(ptr)
        }

        unsafe fn schedule_all<W, S, const N: usize>(this: NonNull<u8>)
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<W, S, N> = this.cast().as_mut();
            this.run().schedule_all();
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
            get_shared: get_shared::<W, S, N>,
            schedule_all: schedule_all::<W, S, N>,
        }
    }
}

// Do not implement Clone. This must be carefully copied.
#[derive(Debug)]
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

    /// # Safety
    ///
    /// Caller must guarantee that the returned replica will not violate pointer
    /// rules. In other words, callers must comply pointer aliasing and must not
    /// use it after free.
    pub(crate) unsafe fn copy(&self) -> Self {
        Self {
            this: self.this,
            vtable: self.vtable,
            _marker: self._marker,
        }
    }

    /// Returns pointer to a certain entity container for the given entity key.
    ///
    /// Note that you can acquire two or more entity container pointers at a
    /// time. But you must check pointer uniqueness when you're turning them
    /// into mutable references.
    pub(crate) fn entity_container_ptr(
        &self,
        ekey: EntityKeyRef<'_>,
    ) -> Option<NonNull<EntityContainer>> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.get_entity_container_mut)(self.this, ekey)
                .map(|cont| NonNull::new_unchecked(cont as *mut _))
        }
    }

    pub(crate) fn get_shared_ptr(&self) -> NonNull<Shared> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.get_shared)(self.this)
        }
    }
}

impl EcsEntry for Ecs<'_> {
    fn add_system<Sys>(&mut self, desc: SystemDesc<Sys>) -> Result<SystemId, EcsError<SystemData>>
    where
        Sys: System,
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

        // Registers the system.
        let res = unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_system_inner)(self.this, sdata, group_index, volatile, private)
        };

        // @@@ TODO: If we failed to activate it, we have to unregister it.
        //
        // Activates the system.
        if let Ok(sid) = res.as_ref() {
            if let Some((live, at)) = activation {
                let must_ok = self.activate_system(*sid, at, live);
                assert!(must_ok.is_ok());
            }
        }
        res
    }

    fn unregister_system(&mut self, sid: SystemId) -> Result<(), EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_system_inner)(self.this, &sid)
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

    fn inactivate_system(&mut self, sid: SystemId) -> Result<(), EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.inactivate_system_inner)(self.this, &sid)
        }
    }

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_entity_inner)(self.this, desc)
        }
    }

    fn register_entity_of<T>(&mut self) -> Result<EntityIndex, EcsError>
    where
        T: AsEntityReg,
    {
        self.register_entity(T::as_entity_descriptor())
    }

    fn unregister_entity<'r, K>(&mut self, ekey: K) -> Result<EntityContainer, EcsError>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_entity_inner)(self.this, ekey.into())
        }
    }

    fn add_entity<E>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError<E>>
    where
        E: Entity,
    {
        let ekey = EntityKeyRef::Index(&ei);

        let cont = unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.get_entity_container_mut)(self.this, ekey)
        };

        if let Some(cont) = cont {
            let ri = value.move_to(&mut **cont);
            Ok(EntityId::new(ei, ri))
        } else {
            let reason = debug_format!("{}", std::any::type_name::<E>());
            Err(EcsError::UnknownEntity(reason, value))
        }
    }

    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), EcsError<ResourceDesc>> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_resource_inner)(self.this, desc)
        }
    }

    fn unregister_resource(
        &mut self,
        rkey: &ResourceKey,
    ) -> Result<Option<Box<dyn Any>>, EcsError> {
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
pub struct EcsApp<W, S = std::hash::RandomState, const N: usize = 1>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
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

    shared: Arc<Shared>,

    vtable: EcsVTable,
}

impl<W, S, const N: usize> EcsApp<W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    pub fn new(workers: Vec<W>, nums: [usize; N]) -> Self {
        let shared = Arc::new(Shared::new());

        Self {
            sys_stor: SystemStorage::new(),
            ent_stor: EntityStorage::new(),
            res_stor: ResourceStorage::new(),
            cache_stor: CacheStorage::new(),
            sched: Scheduler::new(workers, nums, &shared),
            shared,
            vtable: EcsVTable::new::<W, S, N>(),
        }
    }

    pub fn destroy(mut self) -> Vec<W> {
        // Remaining commands and systems must be cancelled.
        self.clear_command();
        self.clear_system();

        // Takes workers out from the scheduler.
        let old = mem::replace(
            &mut self.sched,
            Scheduler::new(Vec::new(), [0; N], &self.shared),
        );
        old.take_workers()
    }

    pub fn into_raw(self) -> LeakedEcsApp {
        LeakedEcsApp::new(self)
    }

    pub fn collect_poisoned_systems(&mut self) -> Vec<(SystemData, Box<dyn Any + Send>)> {
        self.sys_stor.drain_poisoned().collect()
    }

    #[must_use]
    pub fn run(&mut self) -> RunningEcs<'_, W, S, N> {
        RunningEcs::new(self)
    }

    // TODO: doc example to test downcast error
    // error: EcsError<SystemData>
    fn register_system_inner(
        &mut self,
        mut sdata: SystemData,
        group_index: u16,
        volatile: bool,
        private: bool,
    ) -> Result<SystemId, EcsError<SystemData>> {
        if let Err(e) = validate_request::<W, S, N>(self, &sdata) {
            return Err(e.with_data(sdata));
        }
        complete_data::<W, S, N>(self, &mut sdata, group_index, private);
        let sid = sdata.id();
        return self.sys_stor.register(sdata, volatile).map(|()| sid);

        // === Internal helper functions ===

        fn validate_request<W, S, const N: usize>(
            this: &EcsApp<W, S, N>,
            sdata: &SystemData,
        ) -> Result<(), EcsError>
        where
            W: Work + 'static,
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
            if let Err(reason) = rinfo.validate() {
                return Err(EcsError::InvalidRequest(reason, ()));
            }

            // 2. Validates queried resources.
            for rkey in rinfo.resource_keys() {
                if !this.res_stor.contains(rkey) {
                    let reason = debug_format!("failed to find a resource `{:?}`", rkey);
                    return Err(EcsError::UnknownResource(reason, ()));
                }
            }

            // 1. Validates request's `EntWrite`.
            // 2. Validates queried entities.
            let (_, r_qinfo) = rinfo.read();
            let (_, w_qinfo) = rinfo.write();
            let r_sels = r_qinfo.selectors();
            let w_sels = w_qinfo.selectors();
            let sels = r_sels.iter().chain(w_sels);
            for ekey in rinfo.entity_keys() {
                if let Some(cont) = this.ent_stor.get_entity_container(ekey) {
                    for (_, sinfo) in sels.clone() {
                        if sinfo.filter(|ckey| cont.contains_column(ckey)) {
                            let reason = debug_format!(
                                "entity query `{:?}` cannot be coexist with filter `{}` in `{}`, they conflict",
                                ekey,
                                sinfo.name(),
                                rinfo.name(),
                            );
                            return Err(EcsError::InvalidRequest(reason, ()));
                        }
                    }
                } else {
                    let reason = debug_format!("failed to find an entity `{:?}`", ekey);
                    return Err(EcsError::UnknownEntity(reason, ()));
                }
            }

            Ok(())
        }

        fn complete_data<W, S, const N: usize>(
            this: &mut EcsApp<W, S, N>,
            sdata: &mut SystemData,
            group_index: u16,
            private: bool,
        ) where
            W: Work + 'static,
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

    fn unregister_system_inner(&mut self, sid: &SystemId) -> Result<(), EcsError> {
        self.sys_stor.unregister(sid)
    }

    fn activate_system_inner(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError> {
        // Activates the system.
        self.sys_stor.activate(target, at, live)?;

        // Refreshes cache item for the system.
        let sgroup = self.sys_stor.get_group_mut(target.group_index() as usize);
        // Safety: The system was successfully activated, so we definitely can
        // get the system data.
        let sdata = unsafe { sgroup.get_active(target).unwrap_unchecked() };
        self.cache_stor.remove_item(target, &self.ent_stor);
        self.cache_stor
            .create_item(sdata, &mut self.ent_stor, &mut self.res_stor);
        Ok(())
    }

    fn inactivate_system_inner(&mut self, sid: &SystemId) -> Result<(), EcsError> {
        self.sys_stor.inactivate(sid)
    }

    fn register_entity_inner(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        // Registers entity.
        let ei = self.ent_stor.register(desc)?;
        let ekey = EntityKeyRef::Index(&ei);
        self.cache_stor
            .update_by_entity_reg(ekey, &mut self.ent_stor, &mut self.res_stor);

        // Makes wait queue for the entity.
        let cont = unsafe { self.ent_stor.get_entity_container(ekey).unwrap_unchecked() };
        self.sched
            .get_wait_queues_mut()
            .initialize_entity_queue(ei.index(), cont.num_columns());

        Ok(ei)
    }

    fn unregister_entity_inner(
        &mut self,
        ekey: EntityKeyRef<'_>,
    ) -> Result<EntityContainer, EcsError> {
        self.cache_stor.update_by_entity_unreg(
            ekey,
            &mut self.ent_stor,
            &mut self.res_stor,
            |sid: &SystemId| self.sys_stor.inactivate(sid).unwrap(),
        );
        if let Some((_, cont)) = self.ent_stor.unregister(ekey) {
            Ok(cont)
        } else {
            let reason = debug_format!("failed to find an entity `{:?}`", ekey);
            Err(EcsError::UnknownEntity(reason, ()))
        }
    }

    fn register_resource_inner(
        &mut self,
        desc: ResourceDesc,
    ) -> Result<(), EcsError<ResourceDesc>> {
        // TODO: Currently, `desc` contains raw pointer and its not Send and
        // Sync. So we cannot convert it to Box<dyn Error + Send + Sync>.
        let index = self.res_stor.register(desc)?;
        self.sched
            .get_wait_queues_mut()
            .initialize_resource_queue(index);
        Ok(())
    }

    fn unregister_resource_inner(
        &mut self,
        rkey: &ResourceKey,
    ) -> Result<Option<Box<dyn Any>>, EcsError> {
        self.cache_stor
            .update_by_resource_unreg(rkey, &self.ent_stor, |sid: &SystemId| {
                self.sys_stor.inactivate(sid).unwrap()
            });
        match self.res_stor.unregister(rkey) {
            Some(Or::A(owned)) => Ok(Some(owned)),
            Some(Or::B(_ptr)) => Ok(None),
            None => {
                let reason = debug_format!("failed to find a resource `{:?}`", rkey);
                Err(EcsError::UnknownResource(reason, ()))
            }
        }
    }

    fn process_buffered_commands(&mut self) {
        // `ecs` borrows `Self` mutably, so we cannot access `sched` in it.
        // So captures its address first.
        let sched_ptr: *const Scheduler<W, S, N> = &self.sched as *const _;
        let ecs = Ecs::new(self);

        // TODO:
        // - Removes unsafefy. Should I flip call hierarchy.
        // - If command panics, recover from it or abort?
        unsafe {
            let sched = sched_ptr.as_ref().unwrap_unchecked();
            sched.consume_command(move |cmd| {
                let c_ecs = ecs.copy();
                let _ = cmd.command(c_ecs);
            });
        }
    }

    /// Cancels out remaining commands.
    ///
    /// Commands are functions that can be executed or cancelled. They can be
    /// cancelled by getting called [`cancel`].
    ///
    /// [`cancel`]: crate::ecs::cmd::Command::cancel
    fn clear_command(&mut self) {
        self.sched.clear_command();
    }

    /// Cancels out remaining systems.
    ///
    /// Systems are functions that can be executed or cancelled. They can be
    /// cancelled by becoming [`SystemState::Dead`] states.
    ///
    /// [`SystemState::Dead`]: crate::ecs::sys::system::SystemState::Dead
    fn clear_system(&mut self) {
        for gi in 0..N {
            self.sys_stor.get_group_mut(gi).clear();
        }
    }

    /// Clears dead systems with their cache items.
    fn clear_dead_system(&mut self) {
        for sdata in self.sys_stor.drain_dead() {
            self.cache_stor.remove_item(&sdata.id(), &self.ent_stor);
        }
    }

    fn get_entity_container_mut<'r, K>(&mut self, ekey: K) -> Option<&mut EntityContainer>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        self.ent_stor.get_entity_container_mut(ekey)
    }
}

impl<W, S, const N: usize> EcsEntry for EcsApp<W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    fn add_system<Sys>(&mut self, desc: SystemDesc<Sys>) -> Result<SystemId, EcsError<SystemData>>
    where
        Sys: System,
    {
        Ecs::new(self).add_system(desc)
    }

    fn unregister_system(&mut self, sid: SystemId) -> Result<(), EcsError> {
        Ecs::new(self).unregister_system(sid)
    }

    fn activate_system(
        &mut self,
        target: SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError> {
        Ecs::new(self).activate_system(target, at, live)
    }

    fn inactivate_system(&mut self, sid: SystemId) -> Result<(), EcsError> {
        Ecs::new(self).inactivate_system(sid)
    }

    fn register_entity(&mut self, desc: EntityReg) -> Result<EntityIndex, EcsError> {
        Ecs::new(self).register_entity(desc)
    }

    fn register_entity_of<T>(&mut self) -> Result<EntityIndex, EcsError>
    where
        T: AsEntityReg,
    {
        Ecs::new(self).register_entity_of::<T>()
    }

    fn unregister_entity<'r, K>(&mut self, ekey: K) -> Result<EntityContainer, EcsError>
    where
        K: Into<EntityKeyRef<'r>>,
    {
        Ecs::new(self).unregister_entity(ekey)
    }

    fn add_entity<E>(&mut self, ei: EntityIndex, value: E) -> Result<EntityId, EcsError<E>>
    where
        E: Entity,
    {
        Ecs::new(self).add_entity(ei, value)
    }

    fn register_resource(&mut self, desc: ResourceDesc) -> Result<(), EcsError<ResourceDesc>> {
        Ecs::new(self).register_resource(desc)
    }

    fn unregister_resource(
        &mut self,
        rkey: &ResourceKey,
    ) -> Result<Option<Box<dyn Any>>, EcsError> {
        Ecs::new(self).unregister_resource(rkey)
    }
}

impl<W, S, const N: usize> Drop for EcsApp<W, S, N>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
    fn drop(&mut self) {
        self.clear_command();
        self.clear_system();
    }
}

impl<W, S, const N: usize> Resource for EcsApp<W, S, N>
where
    EcsApp<W, S, N>: Send + 'static,
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
}

pub struct LeakedEcsApp {
    this: Ecs<'static>,
    drop: unsafe fn(Ecs<'static>),
}

impl LeakedEcsApp {
    fn new<W, S, const N: usize>(app: EcsApp<W, S, N>) -> Self
    where
        W: Work + 'static,
        S: BuildHasher + Default + 'static,
    {
        unsafe fn _drop<W, S, const N: usize>(ecs: Ecs<'static>)
        where
            W: Work + 'static,
            S: BuildHasher + Default + 'static,
        {
            let mut ptr = ecs.this.cast::<EcsApp<W, S, N>>();
            drop(Box::from_raw(ptr.as_mut()));
        }

        Self {
            this: Ecs::new(Box::leak(Box::new(app))),
            drop: _drop::<W, S, N>,
        }
    }

    /// # Safety
    ///
    /// See [`Ecs::copy`].
    #[cfg(target_arch = "wasm32")]
    pub(crate) unsafe fn get(&self) -> EcsExt<'static> {
        EcsExt(self.this.copy())
    }
}

impl Drop for LeakedEcsApp {
    fn drop(&mut self) {
        // Safety:
        // - `self.drop` holds proper drop method for `self.this`
        // - It cannot be double free because we release `self.this` here only.
        // See `Self::new()` for more details.
        unsafe { (self.drop)(self.this.copy()) };
    }
}

pub struct EcsExt<'ecs>(Ecs<'ecs>);

impl EcsExt<'_> {
    pub fn schedule_all(&mut self) {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.schedule_all)(self.this);
        }
    }
}

impl<'ecs> Deref for EcsExt<'ecs> {
    type Target = Ecs<'ecs>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[repr(transparent)]
pub struct RunningEcs<'ecs, W, S, const N: usize>
where
    W: Work + 'static,
    S: BuildHasher + Default + 'static,
{
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

        // Clears dead systems caused by the execution above.
        self.ecs.clear_dead_system();

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

#[derive(Debug)]
pub(crate) struct Shared {
    ent_move: Mutex<EntMoveStorage>,
}

impl Shared {
    fn new() -> Self {
        Self {
            ent_move: Mutex::new(EntMoveStorage::new()),
        }
    }

    pub(crate) fn lock_entity_move_storage(&self) -> MutexGuard<'_, EntMoveStorage> {
        self.ent_move.lock().unwrap()
    }
}
