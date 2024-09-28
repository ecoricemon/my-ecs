use super::{
    cache::{CacheStorage, RefreshCacheStorage},
    ent::{
        entity::{Entity, EntityId, EntityIndex, EntityKey},
        storage::{AsEntityDesc, EntityContainer, EntityDesc, EntityStorage},
    },
    resource::{MaybeOwned, Resource, ResourceKey, ResourceStorage},
    sched::Scheduler,
    sys::{
        request::StoreRequestInfo,
        storage::SystemStorage,
        system::{
            FnOnceSystem, InsertPos, Invoke, NonZeroTick, PrivateSystem, System, SystemBond,
            SystemData, SystemGroup, SystemId, SystemKey,
        },
    },
    worker::HoldWorkers,
    EcsError, EcsResult,
};
use crate::util::prelude::*;
use std::{
    any::Any, cell::RefCell, fmt::Debug, hash::BuildHasher, marker::PhantomData, mem, ptr::NonNull,
    rc::Rc,
};

#[rustfmt::skip]
pub trait EcsEntry {
    fn register_system<T, Sys>(
        &mut self, gi: usize, volatile: bool, sys: T
    ) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static;

    fn register_once_system<T, Req, F>(
        &mut self, gi: usize, sys: T
    ) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send;

    fn unregister_system(
        &mut self, gi: usize, sid: &SystemId
    ) -> Option<SystemData>;

    fn activate_system(
        &mut self, target: &SystemId, at: InsertPos, live: NonZeroTick,
    ) -> EcsResult<()>;

    fn inactivate_system(&mut self, gi: usize, sid: &SystemId) -> EcsResult<()>;

    fn append_system<T, Sys>(
        &mut self, gi: usize, live: NonZeroTick, volatile: bool, sys: T,
    ) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static;

    fn append_once_system<T, Req, F>(
        &mut self, gi: usize, sys: T
    ) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send;

    fn register_entity(&mut self, desc: EntityDesc) -> EntityIndex;

    fn register_entity_of<T: AsEntityDesc>(&mut self) -> EntityIndex;

    fn add_entity<E>(
        &mut self, ei: EntityIndex, value: E
    ) -> EcsResult<EntityId>
    where
        E: Entity;

    fn register_resource(
        &mut self, key: ResourceKey, value: MaybeOwned, is_dedicated: bool,
    ) -> Result<(), MaybeOwned>;
}

#[rustfmt::skip]
#[derive(Debug)]
struct EcsVTable {
    register_system_inner:
        unsafe fn(NonNull<u8>, usize, bool, SystemKey, SystemData) 
            -> EcsResult<()>,

    unregister_system_inner: 
        unsafe fn(NonNull<u8>, usize, &SystemId) -> Option<SystemData>,

    activate_system_inner:
        unsafe fn(NonNull<u8>, &SystemId, InsertPos, NonZeroTick) 
            -> EcsResult<()>,

    inactivate_system_inner: 
        unsafe fn(NonNull<u8>, usize, &SystemId) -> EcsResult<()>,

    register_entity_inner: 
        unsafe fn(NonNull<u8>, EntityDesc) -> EntityIndex,

    register_resource_inner:
        unsafe fn(NonNull<u8>, ResourceKey, MaybeOwned, bool) 
            -> Result<(), MaybeOwned>,

    next_system_id: 
        unsafe fn(NonNull<u8>, usize) -> SystemId,

    request_info_storage: 
        unsafe fn(NonNull<u8>) -> Rc<RefCell<dyn StoreRequestInfo>>,

    get_entity_container_mut: 
        unsafe fn(NonNull<u8>, &EntityKey) -> Option<&mut EntityContainer>,
}

impl EcsVTable {
    fn new<Wp, S, const N: usize>() -> Self
    where
        Wp: HoldWorkers + Default + 'static,
        S: BuildHasher + Default + 'static,
    {
        unsafe fn register_system_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            gi: usize,
            volatile: bool,
            skey: SystemKey,
            sdata: SystemData,
        ) -> EcsResult<()>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.register_system_inner(gi, volatile, skey, sdata)
        }

        unsafe fn unregister_system_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            gi: usize,
            sid: &SystemId,
        ) -> Option<SystemData>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.unregister_system_inner(gi, sid)
        }

        unsafe fn activate_system_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            target: &SystemId,
            at: InsertPos,
            live: NonZeroTick,
        ) -> EcsResult<()>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.activate_system_inner(target, at, live)
        }

        unsafe fn inactivate_system_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            gi: usize,
            sid: &SystemId,
        ) -> EcsResult<()>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.inactivate_system_inner(gi, sid)
        }

        unsafe fn register_entity_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            desc: EntityDesc,
        ) -> EntityIndex
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.register_entity_inner(desc)
        }

        unsafe fn register_resource_inner<Wp, S, const N: usize>(
            this: NonNull<u8>,
            key: ResourceKey,
            value: MaybeOwned,
            is_dedicate: bool,
        ) -> Result<(), MaybeOwned>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.register_resource_inner(key, value, is_dedicate)
        }

        unsafe fn next_system_id<Wp, S, const N: usize>(this: NonNull<u8>, gi: usize) -> SystemId
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.next_system_id(gi)
        }

        unsafe fn request_info_stoarge<Wp, S, const N: usize>(
            this: NonNull<u8>,
        ) -> Rc<RefCell<dyn StoreRequestInfo>>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.request_info_storage()
        }

        unsafe fn get_entity_container_mut<'i, 'o, Wp, S, const N: usize>(
            this: NonNull<u8>,
            ekey: &'i EntityKey,
        ) -> Option<&'o mut EntityContainer>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            let this: &'o mut EcsApp<Wp, S, N> = this.cast().as_mut();
            this.get_entity_container_mut(ekey)
        }

        Self {
            register_system_inner: register_system_inner::<Wp, S, N>,
            unregister_system_inner: unregister_system_inner::<Wp, S, N>,
            activate_system_inner: activate_system_inner::<Wp, S, N>,
            inactivate_system_inner: inactivate_system_inner::<Wp, S, N>,
            register_entity_inner: register_entity_inner::<Wp, S, N>,
            register_resource_inner: register_resource_inner::<Wp, S, N>,
            next_system_id: next_system_id::<Wp, S, N>,
            request_info_storage: request_info_stoarge::<Wp, S, N>,
            get_entity_container_mut: get_entity_container_mut::<Wp, S, N>,
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
    pub fn default<Wp>(worker_pool: Wp) -> EcsApp<Wp, std::hash::RandomState, 1>
    where
        Wp: HoldWorkers + Default + 'static,
    {
        Self::create(worker_pool)
    }

    pub fn create<Wp, S, const N: usize>(worker_pool: Wp) -> EcsApp<Wp, S, N>
    where
        Wp: HoldWorkers + Default + 'static,
        S: BuildHasher + Default + 'static,
    {
        EcsApp::new(worker_pool)
    }

    fn new<Wp, S, const N: usize>(ecs: &'ecs mut EcsApp<Wp, S, N>) -> Self
    where
        Wp: HoldWorkers + Default + 'static,
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
    fn register_system<T, Sys>(&mut self, gi: usize, volatile: bool, sys: T) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static,
    {
        unsafe {
            let vtable = self.vtable.as_ref();
            let sid = (vtable.next_system_id)(self.this, gi);
            let sys: SystemBond<Sys> = sys.into();
            let sys: Sys = sys.into_inner();
            let skey = sys.skey();
            let sdata = sys.into_data((vtable.request_info_storage)(self.this), sid);

            (vtable.register_system_inner)(self.this, gi, volatile, skey, sdata).map(|()| sid)
        }
    }

    fn register_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send,
    {
        // FnOnce system will be removed from memory when it's expired.
        const VOLATILE: bool = true;
        let sys: FnOnceSystem<Req, F> = sys.into();
        self.register_system(gi, VOLATILE, sys)
    }

    fn unregister_system(&mut self, gi: usize, sid: &SystemId) -> Option<SystemData> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.unregister_system_inner)(self.this, gi, sid)
        }
    }

    fn activate_system(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> EcsResult<()> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.activate_system_inner)(self.this, target, at, live)
        }
    }

    fn inactivate_system(&mut self, gi: usize, sid: &SystemId) -> EcsResult<()> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.inactivate_system_inner)(self.this, gi, sid)
        }
    }

    fn append_system<T, Sys>(
        &mut self,
        gi: usize,
        live: NonZeroTick,
        volatile: bool,
        sys: T,
    ) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static,
    {
        let res = self.register_system(gi, volatile, sys);
        if let Ok(sid) = res.as_ref() {
            let must_ok = self.activate_system(sid, InsertPos::Back, live);
            debug_assert!(must_ok.is_ok());
        }
        res
    }

    fn append_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send,
    {
        // FnOnce system will be removed from memory when it's expired.
        const VOLATILE: bool = true;
        const LIVE: NonZeroTick = unsafe { NonZeroTick::new_unchecked(1) };
        let f: FnOnceSystem<Req, F> = sys.into();
        self.append_system(gi, LIVE, VOLATILE, f)
    }

    fn register_entity(&mut self, desc: EntityDesc) -> EntityIndex {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_entity_inner)(self.this, desc)
        }
    }

    fn register_entity_of<T: AsEntityDesc>(&mut self) -> EntityIndex {
        self.register_entity(T::as_entity_descriptor())
    }

    fn add_entity<E: Entity>(&mut self, ei: EntityIndex, value: E) -> EcsResult<EntityId> {
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

    fn register_resource(
        &mut self,
        key: ResourceKey,
        value: MaybeOwned,
        is_dedicated: bool,
    ) -> Result<(), MaybeOwned> {
        unsafe {
            let vtable = self.vtable.as_ref();
            (vtable.register_resource_inner)(self.this, key, value, is_dedicated)
        }
    }
}

/// * `Wp` - Worker pool type.
/// * `S` - Hasher.
/// * `N` - Number of [`SystemGroup`]s.
//
// We know N > 0 due to the validation in `Multi`.
#[derive(Debug)]
pub struct EcsApp<Wp, S = std::hash::RandomState, const N: usize = 1> {
    /// System storage.
    sys: SystemStorage<S, N>,

    /// Entity and component storage.
    /// The storage contains all kinds of entities and components.
    ent: EntityStorage<S>,

    /// Resource storage.
    /// The storage contains pointers to resources.
    res: ResourceStorage<S>,

    cache: CacheStorage<S>,

    sched: Scheduler<S>,

    worker_pool: Wp,

    vtable: EcsVTable,
}

impl<Wp> EcsApp<Wp, std::hash::RandomState, 1>
where
    Wp: HoldWorkers + Default + 'static,
{
    pub fn run_default(&mut self) {
        self.run().call(0, &mut |ecs| ecs.schedule());
    }
}

impl<Wp, S, const N: usize> EcsApp<Wp, S, N>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    fn new(mut worker_pool: Wp) -> Self {
        assert!(!worker_pool.workers().is_empty());

        Self {
            sys: SystemStorage::new(),
            ent: EntityStorage::new(),
            res: ResourceStorage::new(),
            cache: CacheStorage::new(),
            sched: Scheduler::new(),
            worker_pool,
            vtable: EcsVTable::new::<Wp, S, N>(),
        }
    }

    pub fn take_worker_pool(&mut self) -> Wp {
        mem::take(&mut self.worker_pool)
    }

    pub fn get_entity_storage(&self) -> &EntityStorage<S> {
        &self.ent
    }

    pub fn get_entity_storage_mut(&mut self) -> &mut EntityStorage<S> {
        &mut self.ent
    }

    pub fn get_resource_storage(&self) -> &ResourceStorage<S> {
        &self.res
    }

    pub fn get_resource_storage_mut(&mut self) -> &mut ResourceStorage<S> {
        &mut self.res
    }

    pub fn collect_poisoned_systems(&mut self) -> Vec<(SystemData, Box<dyn Any + Send>)> {
        self.sys.collect_poisoned()
    }

    #[must_use]
    pub fn run(&mut self) -> WorkingEcs<'_, Wp, S, N> {
        WorkingEcs::new(self)
    }

    fn register_system_inner(
        &mut self,
        gi: usize,
        volatile: bool,
        skey: SystemKey,
        sdata: SystemData,
    ) -> EcsResult<()> {
        validate_request(self, &sdata)?;
        self.cache.create(&sdata, &self.ent, &self.res);
        return self.sys.register(gi, skey, sdata, volatile, &self.res);

        // === Internal helper functions ===

        fn validate_request<W, S, const N: usize>(
            this: &EcsApp<W, S, N>,
            sdata: &SystemData,
        ) -> EcsResult<()>
        where
            S: BuildHasher + Default + 'static,
        {
            // Validations procedure is as follows.
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
                if !this.res.contains(rkey) {
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
                if let Some(cont) = this.ent.get_entity_container(ekey) {
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
    }

    fn unregister_system_inner(&mut self, gi: usize, sid: &SystemId) -> Option<SystemData> {
        self.sys.unregister(gi, sid)
    }

    fn activate_system_inner(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        mut live: NonZeroTick,
    ) -> EcsResult<()> {
        // It can be in the middle of scheduling,
        // which means there may be no chance to run target system in this time.
        // In that case, we need to add `live` by 1 to guarantee the total number of run.
        match at {
            InsertPos::After(after) => {
                let sgroup = self.sys.get_group_mut(after.group_index() as usize);
                if let Some(next) = sgroup.get_active_mut().peek_next(after) {
                    if self.sched.get_run_history().contains(&next.id()) {
                        live = live.saturating_add(1);
                    }
                }
            }
            InsertPos::Back => { /* target must be run in this time */ }
            InsertPos::Front => {
                if !self.sched.get_run_history().is_empty() {
                    live = live.saturating_add(1);
                }
            }
        }

        // Activates it.
        self.sys.activate(target, at, live)
    }

    fn inactivate_system_inner(&mut self, gi: usize, sid: &SystemId) -> EcsResult<()> {
        self.sys.inactivate(gi, sid)
    }

    fn register_entity_inner(&mut self, desc: EntityDesc) -> EntityIndex {
        // Registers entity.
        let ei = self.ent.register_entity(desc);
        self.cache.update(&self.ent, ei);

        // Makes wait queue for the entity.
        let cont = unsafe {
            self.ent
                .get_entity_container(&EntityKey::from(ei))
                .unwrap_unchecked()
        };
        self.sched
            .get_wait_queues()
            .initialize_entity_queue(ei.index(), cont.get_column_num());

        ei
    }

    fn register_resource_inner(
        &mut self,
        key: ResourceKey,
        value: MaybeOwned,
        is_dedicated: bool,
    ) -> Result<(), MaybeOwned> {
        let index = self.res.register(key, value, is_dedicated)?;
        self.sched
            .get_wait_queues()
            .initialize_resource_queue(index);
        Ok(())
    }

    fn handle_commands(&mut self) {
        // `raw` borrows `Self` mutably, so we cannot access `sched` in it.
        // So captures its address first.
        let sched_ptr: *const Scheduler<S> = &self.sched as *const _;
        let raw = Ecs::new(self);

        // Safety: `raw` cannot manipulate command channel.
        // We can safely consume command channel.
        unsafe {
            let sched = sched_ptr.as_ref().unwrap_unchecked();
            sched.consume_commands(|cmd| {
                cmd.command(raw);
            });
        }
    }

    fn next_system_id(&mut self, gi: usize) -> SystemId {
        self.sys.get_group_mut(gi).next_system_id()
    }

    fn request_info_storage(&mut self) -> Rc<RefCell<dyn StoreRequestInfo>> {
        self.sys.request_info_storage()
    }

    fn get_entity_container_mut(&mut self, ekey: &EntityKey) -> Option<&mut EntityContainer> {
        self.ent.get_entity_container_mut(ekey)
    }
}

impl<Wp, S, const N: usize> EcsEntry for EcsApp<Wp, S, N>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    fn register_system<T, Sys>(&mut self, gi: usize, volatile: bool, sys: T) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static,
    {
        Ecs::new(self).register_system(gi, volatile, sys)
    }

    fn register_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send,
    {
        Ecs::new(self).register_once_system(gi, sys)
    }

    fn unregister_system(&mut self, gi: usize, sid: &SystemId) -> Option<SystemData> {
        Ecs::new(self).unregister_system(gi, sid)
    }

    /// Activates the system. If the system is already active, nothing takes place.
    fn activate_system(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> EcsResult<()> {
        Ecs::new(self).activate_system(target, at, live)
    }

    fn inactivate_system(&mut self, gi: usize, sid: &SystemId) -> EcsResult<()> {
        Ecs::new(self).inactivate_system(gi, sid)
    }

    fn append_system<T, Sys>(
        &mut self,
        gi: usize,
        live: NonZeroTick,
        volatile: bool,
        sys: T,
    ) -> EcsResult<SystemId>
    where
        T: Into<SystemBond<Sys>>,
        Sys: System + 'static,
    {
        Ecs::new(self).append_system(gi, live, volatile, sys)
    }

    fn append_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send,
    {
        Ecs::new(self).append_once_system(gi, sys)
    }

    fn register_entity(&mut self, desc: EntityDesc) -> EntityIndex {
        Ecs::new(self).register_entity(desc)
    }

    fn register_entity_of<T: AsEntityDesc>(&mut self) -> EntityIndex {
        Ecs::new(self).register_entity_of::<T>()
    }

    fn add_entity<E: Entity>(&mut self, ei: EntityIndex, value: E) -> EcsResult<EntityId> {
        Ecs::new(self).add_entity(ei, value)
    }

    /// Registers the resource.
    /// If the registration failed, nothing takes place and returns received value.
    /// In other words, the old resouce data won't be dropped.
    fn register_resource(
        &mut self,
        key: ResourceKey,
        value: MaybeOwned,
        is_dedicated: bool,
    ) -> Result<(), MaybeOwned> {
        Ecs::new(self).register_resource(key, value, is_dedicated)
    }
}

impl<Wp: 'static, S: 'static, const N: usize> Resource for EcsApp<Wp, S, N> {}

pub struct WorkingEcs<'ecs, Wp, S, const N: usize>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    ecs: &'ecs mut EcsApp<Wp, S, N>,
    gi: usize,
}

impl<'ecs, Wp, S, const N: usize> WorkingEcs<'ecs, Wp, S, N>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    const UNINIT: usize = usize::MAX;

    fn new(ecs: &'ecs mut EcsApp<Wp, S, N>) -> Self {
        ecs.sched.open_workers(ecs.worker_pool.workers());

        Self {
            ecs,
            gi: Self::UNINIT,
        }
    }

    pub fn call<F>(&mut self, gi: usize, f: &mut F) -> &mut Self
    where
        F: FnMut(&mut Self),
    {
        self.gi = gi;
        f(self);
        self.ecs.handle_commands();
        self.gi = Self::UNINIT;
        self
    }

    pub fn schedule(&mut self) {
        let Self { ecs, gi } = self;
        assert_ne!(*gi, Self::UNINIT);

        let mut cache = RefreshCacheStorage {
            cache: &mut ecs.cache.items,
            ent: &mut ecs.ent,
            res: &mut ecs.res,
        };

        let dedi = &ecs.sys.dedi_sys;

        if let Some(sgroup) = ecs.sys.sgroups.get_mut(*gi) {
            ecs.sched
                .execute(sgroup, ecs.worker_pool.workers(), &mut cache, dedi);
        } else {
            panic!(
                "{}",
                debug_format!("system group index({gi}) is out of bounds")
            );
        }
    }

    pub fn sys(&self) -> &SystemGroup<S> {
        self.ecs.sys.sgroups.get(self.gi).unwrap()
    }
}

impl<'ecs, Wp, S, const N: usize> Drop for WorkingEcs<'ecs, Wp, S, N>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    fn drop(&mut self) {
        let Self { ecs, .. } = self;

        ecs.sched.close_workers(ecs.worker_pool.workers());
    }
}
