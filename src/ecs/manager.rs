use super::{
    cache::{CacheStorage, RefreshCacheStorage},
    ent::{
        entity::{Entity, EntityId, EntityIndex, EntityKey},
        storage::{AsEntityDesc, EntityDesc, EntityStorage},
    },
    resource::{MaybeOwned, Resource, ResourceKey, ResourceStorage},
    sched::Scheduler,
    sys::{
        storage::SystemStorage,
        system::{
            FnOnceSystem, FnSystem, InsertPos, Invoke, NonZeroTick, PrivateSystem,
            StructOrFnSystem, System, SystemData, SystemGroup, SystemId, SystemKey,
        },
    },
    worker::Work,
    EcsError, EcsResult,
};
use crate::util::prelude::*;
use std::{any::Any, collections::HashSet, fmt::Debug, hash::BuildHasher, time::Duration};

/// * `S` - Hasher.
/// * `N` - Number of [`SystemGroup`], which operates in a different configurable way from each other.
//
// We know N > 0 due to the validation in `Multi`.
#[derive(Debug)]
pub struct Ecs<S = std::hash::RandomState, const N: usize = 1> {
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
}

impl Ecs<std::hash::RandomState, 1> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn operate<W: Work>(&mut self, workers: &mut [W]) {
        OperableEcs::new(self, workers).operate(&mut |ecs| ecs.schedule());
    }
}

impl<S, const N: usize> Ecs<S, N>
where
    S: BuildHasher + Default + 'static,
{
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

    pub fn register_system<T, Sys, Req, F>(
        &mut self,
        gi: usize,
        volatile: bool,
        sys: T,
    ) -> EcsResult<SystemId>
    where
        T: Into<StructOrFnSystem<Sys, Req, F>>,
        Sys: System + 'static,
        FnSystem<Req, F>: System + 'static,
        F: Send,
    {
        let sid = self.sys.get_system_group_mut(gi).next_system_id();
        let sys: StructOrFnSystem<Sys, Req, F> = sys.into();
        let (skey, sdata) = match sys {
            StructOrFnSystem::Struct(s) => {
                let skey = Sys::key();
                let sdata = s.into_data(self.sys.request_info_storage(), sid);
                (skey, sdata)
            }
            StructOrFnSystem::Fn(f) => {
                let skey = f.skey();
                let sdata = f.into_data(self.sys.request_info_storage(), sid);
                (skey, sdata)
            }
        };

        validate_request(self, &sdata)?;
        register_system_inner(self, gi, volatile, skey, sdata)?;
        return Ok(sid);

        // === Internal helper functions ===

        fn validate_request<S, const N: usize>(
            this: &Ecs<S, N>,
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

        fn register_system_inner<S, const N: usize>(
            this: &mut Ecs<S, N>,
            gi: usize,
            volatile: bool,
            skey: SystemKey,
            sdata: SystemData,
        ) -> EcsResult<()>
        where
            S: BuildHasher + Default + 'static,
        {
            this.cache.create(&sdata, &this.ent, &this.res);
            this.sys
                .register_system(gi, skey, sdata, volatile, &this.res)
        }
    }

    pub fn register_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System + 'static,
        F: Send,
    {
        // FnOnce system will be removed from memory when it's expired.
        const VOLATILE: bool = true;
        let f: FnOnceSystem<Req, F> = sys.into();
        self.register_system(gi, VOLATILE, f)
    }

    /// Activates the system. If the system is already active, nothing takes place.
    pub fn activate_system(
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
                let sgroup = self.sys.get_system_group_mut(after.group_index() as usize);
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
        self.sys.activate_system(target, at, live)
    }

    pub fn append_system<T, Sys, Req, F>(
        &mut self,
        gi: usize,
        live: NonZeroTick,
        volatile: bool,
        sys: T,
    ) -> EcsResult<SystemId>
    where
        T: Into<StructOrFnSystem<Sys, Req, F>>,
        Sys: System + 'static,
        FnSystem<Req, F>: System + 'static,
        F: Send,
    {
        let res = self.register_system(gi, volatile, sys);
        if let Ok(sid) = res.as_ref() {
            let must_ok = self.activate_system(sid, InsertPos::Back, live);
            debug_assert!(must_ok.is_ok());
        }
        res
    }

    pub fn append_once_system<T, Req, F>(&mut self, gi: usize, sys: T) -> EcsResult<SystemId>
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

    pub fn register_entity_of<T: AsEntityDesc>(&mut self) -> EntityIndex {
        self.register_entity(T::as_entity_descriptor())
    }

    pub fn register_entity(&mut self, desc: EntityDesc) -> EntityIndex {
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

    pub fn add_entity<E: Entity>(&mut self, ei: EntityIndex, value: E) -> EcsResult<EntityId> {
        if let Some(cont) = self.ent.get_entity_container_mut(&EntityKey::from(ei)) {
            let itemi = value.move_to(&mut **cont);
            Ok(EntityId::new(ei, itemi))
        } else {
            let errmsg = debug_format!("{}", std::any::type_name::<E>());
            Err(EcsError::UnknownEntity(errmsg))
        }
    }

    /// Registers the resource.
    /// If the registration failed, nothing takes place and returns received value.
    /// In other words, the old resouce data won't be dropped.
    pub fn register_resource(
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

    pub fn set_scheduler_timeout(&mut self, dur: Duration) {
        self.sched.set_wait_timeout(dur);
    }

    pub fn collect_poisoned_systems(&mut self) -> Vec<(SystemData, Box<dyn Any + Send>)> {
        self.sys.collect_poisoned()
    }

    pub fn with_worker<'ecs, 'w, W: Work>(
        &'ecs mut self,
        workers: &'w mut [W],
    ) -> OperableEcs<'ecs, 'w, W, S, N> {
        OperableEcs::new(self, workers)
    }
}

impl<S, const N: usize> Default for Ecs<S, N>
where
    S: BuildHasher + Default + 'static,
{
    fn default() -> Self {
        Self {
            sys: SystemStorage::new(),
            ent: EntityStorage::new(),
            res: ResourceStorage::new(),
            cache: CacheStorage::new(),
            sched: Scheduler::new(),
        }
    }
}

impl<S: 'static, const N: usize> Resource for Ecs<S, N> {}

#[derive(Debug)]
pub struct OperableEcs<'ecs, 'w, W, S, const N: usize>
where
    W: Work,
    S: BuildHasher + Default,
{
    sgroups: &'ecs mut Multi<SystemGroup<S>, N>,
    cache: RefreshCacheStorage<'ecs, S>,
    dedi: &'ecs HashSet<SystemId, S>,
    sched: &'ecs mut Scheduler<S>,
    workers: &'w mut [W],
    sgroup_idx: usize,
}

impl<'ecs, 'w, W, S, const N: usize> OperableEcs<'ecs, 'w, W, S, N>
where
    W: Work,
    S: BuildHasher + Default,
{
    fn new(ecs: &'ecs mut Ecs<S, N>, workers: &'w mut [W]) -> Self {
        assert!(!workers.is_empty());

        // Opens workers.
        ecs.sched.open_workers(workers);

        Self {
            sgroups: &mut ecs.sys.sgroups,
            cache: RefreshCacheStorage {
                cache: &mut ecs.cache.items,
                ent: &mut ecs.ent,
                res: &mut ecs.res,
            },
            dedi: &ecs.sys.dedi_sys,
            sched: &mut ecs.sched,
            workers,
            sgroup_idx: 0,
        }
    }

    pub fn operate<F>(&mut self, op: &mut F) -> &mut Self
    where
        F: FnMut(&mut WorkingEcs<W, S, N>),
    {
        let mut working = WorkingEcs::new(self);
        op(&mut working);
        self.sgroup_idx += 1;
        self
    }
}

impl<'ecs, 'w, W, S, const N: usize> Drop for OperableEcs<'ecs, 'w, W, S, N>
where
    W: Work,
    S: BuildHasher + Default,
{
    fn drop(&mut self) {
        // Closes workers.
        self.sched.close_workers(self.workers);
    }
}

#[repr(transparent)]
pub struct WorkingEcs<'o, 'ecs, 'w, W, S, const N: usize>
where
    W: Work,
    S: BuildHasher + Default,
{
    ecs: &'o mut OperableEcs<'ecs, 'w, W, S, N>,
}

impl<'o, 'ecs, 'w, W, S, const N: usize> WorkingEcs<'o, 'ecs, 'w, W, S, N>
where
    W: Work,
    S: BuildHasher + Default,
{
    fn new(ecs: &'o mut OperableEcs<'ecs, 'w, W, S, N>) -> Self {
        Self { ecs }
    }

    pub fn schedule(&mut self) {
        let Self { ecs } = self;
        if let Some(sgroup) = ecs.sgroups.get_mut(ecs.sgroup_idx) {
            ecs.sched
                .execute(sgroup, ecs.workers, &mut ecs.cache, ecs.dedi);
        } else {
            let errmsg = debug_format!("operate() has called more than {N}");
            panic!("{}", errmsg);
        }
    }

    pub fn sys(&self) -> &SystemGroup<S> {
        self.ecs.sgroups.get(self.ecs.sgroup_idx).unwrap()
    }
}
