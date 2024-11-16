use super::{
    ent::{
        component::ComponentKey,
        entity::{EntityIndex, EntityKey, EntityKeyKind, EntityTag},
        storage::EntityStorage,
    },
    resource::{ResourceKey, ResourceStorage},
    sys::{
        filter::{FilterInfo, RawFiltered},
        query::{EntQueryInfo, QueryInfo, ResQueryInfo},
        request::{RequestInfo, SystemBuffer},
        system::{SystemData, SystemId, SystemInfo},
    },
    wait::{WaitIndices, WaitRetryIndices},
};
use crate::ds::prelude::*;
use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    hash::BuildHasher,
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::Weak,
};

/// The storage is updated by some events as follows.
///
/// | Events                  | Actions                          |
/// | :---                    | :---                             |
/// | System registration     | Creates a cache item             |
/// | System unregistration   | Removes a cache item             |
/// | Entity registration     | Can update cache items           |
/// | Entity unregistration   | Can remove or update cache items |
/// | Resource registration   | None                             |
/// | Resource unregistration | Can remove cache items           |
///
/// Do not forget to call proper methods for events.
#[derive(Debug)]
pub(super) struct CacheStorage<S> {
    items: HashMap<SystemId, (CacheItem, Weak<SystemInfo>), S>,
    noti: HashMap<CacheNoti, HashSet<SystemId, S>, S>,
}

impl<S> CacheStorage<S>
where
    S: Default,
{
    pub(super) fn new() -> Self {
        Self {
            items: HashMap::default(),
            noti: HashMap::default(),
        }
    }
}

impl<S> CacheStorage<S>
where
    S: BuildHasher + Default,
{
    /// Creates a new cache item for the newly registered system as update of
    /// system registration.
    ///
    /// You can call this method before or after you register the system.
    pub(super) fn update_by_system_reg(
        &mut self,
        sdata: &SystemData,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) {
        assert!(!self.items.contains_key(&sdata.id()));

        // TODO: Validation: Conflicts b/w read and write.
        // But, Users may want to insert/remove Entity using EntityContainer
        // while read some columns from the Entity.

        // TODO: Validation: restrict duplicated filter or resource or entity in a single query.

        // Caches read & write queries.
        let rinfo = sdata.get_request_info();
        let qinfo = rinfo.read().1.as_ref();
        let (wait_read, buf_read) = cache_query(qinfo, ent_stor);
        let qinfo = rinfo.write().1.as_ref();
        let (wait_write, buf_write) = cache_query(qinfo, ent_stor);

        // Caches read & write resource queries.
        let rqinfo = rinfo.res_read().1.as_ref();
        let wait_res_read = cache_res_query(rqinfo, res_stor);
        let rqinfo = rinfo.res_write().1.as_ref();
        let wait_res_write = cache_res_query(rqinfo, res_stor);

        // Caches write entity query.
        let eqinfo = rinfo.ent_write().1.as_ref();
        let wait_ent_write = cache_ent_query(eqinfo, ent_stor);

        // Inserts wait queue indices.
        let wait = WaitIndices {
            read: wait_read,
            write: wait_write,
            res_read: wait_res_read,
            res_write: wait_res_write,
            ent_write: wait_ent_write,
        };
        let wait = Rc::new(RefCell::new(wait));

        // Creates and inserts cache item.
        let sid = sdata.id();
        let mut item = CacheItem::new(wait);
        item.buf.read = buf_read;
        item.buf.write = buf_write;
        item.finish_update(ent_stor, res_stor);
        self.items.insert(sid, (item, sdata.info()));

        // Adds notification for the cache item.
        let add_noti = |key| Self::add_noti_item(&mut self.noti, key, sid);
        Self::update_noti(rinfo, add_noti);

        return;

        // === Internal helper functions ===

        /// Creates 'wait indices' and 'buffer for filtered data' for a query.
        ///
        /// - 'Wait indices' are a set of entity and component index pairs.
        ///   We can find specific components requered by the query using them.
        ///   They are a part of [`WaitIndices`].
        ///
        /// - 'Buffer for filtered data' is a set of buffer that hold component data.
        ///   The buffer will eventually be served to a worker.
        ///   They are a part of [`SystemBuffer`].
        fn cache_query<S>(
            qinfo: &QueryInfo,
            ent_stor: &EntityStorage<S>,
        ) -> (DedupVec<(usize, usize), false>, Box<[RawFiltered]>)
        where
            S: BuildHasher + Default,
        {
            let mut merged_wait = DedupVec::new();
            let mut merged_filtered = Vec::new();
            for (_, finfo) in qinfo.filters().iter() {
                let (wait, filtered) = FilterUtil::filter_all(ent_stor, finfo);

                // Gathers `wait indices` and `buffer for filtered data`.
                let wait = wait.into_iter().map(|(ei, ci)| (ei.index(), ci));
                merged_wait.extend(wait);
                merged_filtered.push(filtered);
            }
            (merged_wait, merged_filtered.into_boxed_slice())
        }

        /// Creates 'wait indices' for a resource query.
        ///
        /// - 'Wait indices' are a set of resource indices.
        ///   We can find specific resources requered by the resource query using them.
        ///   They are a part of [`WaitIndices`].
        fn cache_res_query<S>(
            rqinfo: &ResQueryInfo,
            res_stor: &ResourceStorage<S>,
        ) -> DedupVec<usize, false>
        where
            S: BuildHasher + Default,
        {
            // TODO: In here, assumes there is no duplication.
            let mut waits = DedupVec::new();
            for rkey in rqinfo.rkeys() {
                let index = res_stor.index(rkey).unwrap();
                waits.push(index);
            }
            waits
        }

        /// Creates 'wait indices' for an entity query.
        ///
        /// - 'Wait indices' are a set of entity indices.
        ///   We can find specific entity contianers requered by the entity query using them.
        ///   They are a part of [`WaitIndices`].
        fn cache_ent_query<S>(
            eqinfo: &EntQueryInfo,
            ent_stor: &EntityStorage<S>,
        ) -> DedupVec<usize, false>
        where
            S: BuildHasher + Default,
        {
            let mut wait = DedupVec::new();
            for ekey in eqinfo.ekeys() {
                let ekey = ent_stor
                    .convert_entity_key(ekey, EntityKeyKind::Index)
                    .unwrap();
                let ei = ekey.index();

                wait.push(ei.index());
            }
            wait
        }
    }

    /// Removes a cache item for the unregistered system as update of system
    /// unregistration.
    ///
    /// Note that you must call this method before you unregister the system.
    pub(super) fn update_by_system_unreg(&mut self, sid: &SystemId) {
        self.remove_cache_item(sid);
    }

    /// Updates related cache items for the newly registered entity. In this
    /// method, operations below can heppen.
    /// - Read and write queries in cache items can be updated.
    ///
    /// Note that you must call this method after you register the entity.
    pub(super) fn update_by_entity_reg<Q>(
        &mut self,
        ekey: Q,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        Q: Into<EntityKey>,
    {
        inner(self, &ekey.into(), ent_stor, res_stor);

        // === Internal helper functions ===

        fn inner<S>(
            this: &mut CacheStorage<S>,
            ekey: &EntityKey,
            ent_stor: &mut EntityStorage<S>,
            res_stor: &mut ResourceStorage<S>,
        ) where
            S: BuildHasher + Default,
        {
            let ei = *ent_stor
                .convert_entity_key(ekey, EntityKeyKind::Index)
                .unwrap()
                .index();
            let (mut r_sids, mut w_sids) = (Vec::new(), Vec::new());
            for ckey in ent_stor.get_component_keys(ekey).unwrap() {
                if let Some(inner_set) = this.noti.get(&CacheNoti::Read(*ckey)) {
                    r_sids.extend(inner_set);
                }
                if let Some(inner_set) = this.noti.get(&CacheNoti::Write(*ckey)) {
                    w_sids.extend(inner_set);
                }
            }
            for sid in r_sids {
                let (item, sinfo) = this.items.get_mut(sid).unwrap();
                let sinfo = sinfo.upgrade().unwrap();
                let rinfo = sinfo.get_request_info();
                let mut item_wait = item.wait.borrow_mut();

                // Adds wait & buf indices for read query.
                let qinfo = &rinfo.read().1;
                let wait = &mut item_wait.read;
                let buf = &mut item.buf.read;
                extend(ent_stor, ei, qinfo, wait, buf);

                drop(item_wait);
                item.finish_update(ent_stor, res_stor);
            }
            for sid in w_sids {
                let (item, sinfo) = this.items.get_mut(sid).unwrap();
                let sinfo = sinfo.upgrade().unwrap();
                let rinfo = sinfo.get_request_info();
                let mut item_wait = item.wait.borrow_mut();

                // Adds wait & buf indices for write query.
                let qinfo = &rinfo.write().1;
                let wait = &mut item_wait.write;
                let buf = &mut item.buf.write;
                extend(ent_stor, ei, qinfo, wait, buf);

                drop(item_wait);
                item.finish_update(ent_stor, res_stor);
            }
        }

        fn extend<S>(
            ent_stor: &EntityStorage<S>,
            ei: EntityIndex,
            qinfo: &QueryInfo,
            wait: &mut DedupVec<(usize, usize), false>,
            buf: &mut [RawFiltered],
        ) where
            S: BuildHasher + Default,
        {
            debug_assert_eq!(qinfo.filters().len(), buf.len());

            for ((_, finfo), filtered) in qinfo.filters().iter().zip(buf.iter_mut()) {
                if let Some((ci, etag)) = FilterUtil::filter(ent_stor, ei, finfo) {
                    wait.push((ei.index(), ci));
                    filtered.add(etag, ci);
                }
            }
        }
    }

    /// Updates related cache items for the unregistered entity. In this method,
    /// operations below can happen.
    /// - Cache items can be removed.
    /// - Read and write queries in cache items can be updated.
    ///
    /// Note that you must call this method before you unregister the entity.
    pub(super) fn update_by_entity_unreg<Q>(
        &mut self,
        ekey: Q,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        Q: Into<EntityKey>,
    {
        inner(self, ekey.into(), ent_stor, res_stor);

        // === Internal helper functions ===

        fn inner<S>(
            this: &mut CacheStorage<S>,
            ekey: EntityKey,
            ent_stor: &mut EntityStorage<S>,
            res_stor: &mut ResourceStorage<S>,
        ) where
            S: BuildHasher + Default,
        {
            let ei = *ent_stor
                .convert_entity_key(&ekey, EntityKeyKind::Index)
                .unwrap()
                .index();

            // Removes cache items for the systems that request the entity.
            let noti_key = CacheNoti::EntWrite(ekey);
            if let Some(inner_set) = this.noti.get(&noti_key) {
                let sids = inner_set.iter().cloned().collect::<Vec<_>>();
                for sid in sids.iter() {
                    this.remove_cache_item(sid);
                }
            }

            // Updates chche items for the systems that request components
            // belonging to the entity.
            let CacheNoti::EntWrite(ekey) = noti_key else {
                unreachable!()
            };
            let (mut r_sids, mut w_sids) = (Vec::new(), Vec::new());
            for ckey in ent_stor.get_component_keys(&ekey).unwrap() {
                if let Some(inner_set) = this.noti.get(&CacheNoti::Read(*ckey)) {
                    r_sids.extend(inner_set);
                }
                if let Some(inner_set) = this.noti.get(&CacheNoti::Write(*ckey)) {
                    w_sids.extend(inner_set);
                }
            }
            for sid in r_sids {
                let (item, sinfo) = this.items.get_mut(sid).unwrap();
                let sinfo = sinfo.upgrade().unwrap();
                let rinfo = sinfo.get_request_info();
                let mut item_wait = item.wait.borrow_mut();

                // Removes wait & buf indices for read query.
                let qinfo = &rinfo.read().1;
                let wait = &mut item_wait.read;
                let buf = &mut item.buf.read;
                shrink(ent_stor, ei, qinfo, wait, buf);

                drop(item_wait);
                item.finish_update(ent_stor, res_stor);
            }
            for sid in w_sids {
                let (item, sinfo) = this.items.get_mut(sid).unwrap();
                let sinfo = sinfo.upgrade().unwrap();
                let rinfo = sinfo.get_request_info();
                let mut item_wait = item.wait.borrow_mut();

                // Removes wait & buf indices for write query.
                let qinfo = &rinfo.write().1;
                let wait = &mut item_wait.write;
                let buf = &mut item.buf.write;
                shrink(ent_stor, ei, qinfo, wait, buf);

                drop(item_wait);
                item.finish_update(ent_stor, res_stor);
            }
        }

        fn shrink<S>(
            ent_stor: &EntityStorage<S>,
            ei: EntityIndex,
            qinfo: &QueryInfo,
            wait: &mut DedupVec<(usize, usize), false>,
            buf: &mut [RawFiltered],
        ) where
            S: BuildHasher + Default,
        {
            debug_assert_eq!(qinfo.filters().len(), buf.len());

            let eii = ei.index();
            let ekey = EntityKey::Index(ei);
            let cont = ent_stor.get_entity_container(&ekey).unwrap();

            for ((_, finfo), filtered) in qinfo.filters().iter().zip(buf.iter_mut()) {
                // Finds ci.
                let target = finfo.target().get_inner();
                let Some(ci) = cont.get_column_index(target) else {
                    continue;
                };

                let old = wait.remove(&(eii, ci));
                debug_assert_eq!(old, Some((eii, ci)));

                let old = filtered.remove(ci);
                debug_assert_eq!(old.unwrap().index(), ei);
            }
        }
    }

    /// Updates related cache items for the unregistered resource. In this
    /// method, operations below can happen.
    /// - Cache items can be removed.
    ///
    /// You can call this method before or after you register the system.
    //
    // Resource registration after system is not allowed. Therefore,
    // 'update_by_resource_reg()' doesn't exist.
    pub(super) fn update_by_resource_unreg(&mut self, rkey: ResourceKey) {
        let mut sids = Vec::new();

        if let Some(inner_set) = self.noti.get(&CacheNoti::ResRead(rkey)) {
            sids.extend(inner_set);
        }
        if let Some(inner_set) = self.noti.get(&CacheNoti::ResWrite(rkey)) {
            sids.extend(inner_set);
        }

        for sid in sids.iter() {
            self.remove_cache_item(sid);
        }
    }

    /// Removes system's cache item if it exists. If the cache item was already
    /// removed by other events like unregistration resource, nothing takes
    /// place.
    fn remove_cache_item(&mut self, sid: &SystemId) {
        // Removes cache item.
        if let Some((_item, sinfo)) = self.items.remove(sid) {
            // Removes notification for the cache item.
            let sinfo = sinfo.upgrade().unwrap();
            let rinfo = sinfo.get_request_info();
            let remove_noti = |key| Self::remove_noti_item(&mut self.noti, &key, sid);
            Self::update_noti(rinfo, remove_noti);
        }
    }

    fn update_noti<F>(rinfo: &RequestInfo, mut f: F)
    where
        F: FnMut(CacheNoti),
        S: BuildHasher + Default,
    {
        // Component notification for system's queries.
        for (_, finfo) in rinfo.read().1.filters() {
            f(CacheNoti::Read(*finfo.target()));
        }
        for (_, finfo) in rinfo.write().1.filters() {
            f(CacheNoti::Write(*finfo.target()));
        }

        // Resource notification for system's resource queries.
        for rkey in rinfo.res_read().1.rkeys() {
            f(CacheNoti::ResRead(*rkey));
        }
        for rkey in rinfo.res_write().1.rkeys() {
            f(CacheNoti::ResWrite(*rkey));
        }

        // Entity notification for system's entity query.
        for ekey in rinfo.ent_write().1.ekeys() {
            f(CacheNoti::EntWrite(ekey.clone()));
        }
    }

    fn add_noti_item(
        noti: &mut HashMap<CacheNoti, HashSet<SystemId, S>, S>,
        key: CacheNoti,
        sid: SystemId,
    ) where
        S: BuildHasher + Default,
    {
        noti.entry(key)
            .and_modify(|inner_set| {
                inner_set.insert(sid);
            })
            .or_insert(HashSet::from_iter([sid]));
    }

    fn remove_noti_item(
        noti: &mut HashMap<CacheNoti, HashSet<SystemId, S>, S>,
        key: &CacheNoti,
        sid: &SystemId,
    ) {
        let Some(inner_set) = noti.get_mut(key) else {
            return;
        };
        inner_set.remove(sid);
        if inner_set.is_empty() {
            noti.remove(key);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(super) enum CacheNoti {
    /// Component key a cache item is referencing.
    ///
    /// - When new entity is registered, related cache items are updated for
    ///   their read and write queries.
    /// - When an entity is unregistered, same update happens.
    Read(ComponentKey),
    Write(ComponentKey),

    /// Resource key a cache item is referencing.
    ///
    /// - When a resource is unregistered, related cache items are removed.
    ResRead(ResourceKey),
    ResWrite(ResourceKey),

    /// Entity key a cache item is referencing.
    ///
    /// - When an entity is unregistered, related cache items are removed.
    EntWrite(EntityKey),
}

struct FilterUtil;
impl FilterUtil {
    /// Filters currently registered entity containers by the given filter.
    fn filter_all<S>(
        ent_stor: &EntityStorage<S>,
        finfo: &FilterInfo,
    ) -> (Vec<(EntityIndex, usize)>, RawFiltered)
    where
        S: BuildHasher + Default,
    {
        let (v_ei_ci, (v_etag, v_ci)): (Vec<_>, (Vec<_>, Vec<_>)) = ent_stor
            .iter_entity_container()
            .filter_map(|(_, ei, _)| {
                Self::filter(ent_stor, ei, finfo).map(|(ci, etag)| {
                    let ei_ci = (ei, ci);
                    let etag_ci = (etag, ci);
                    (ei_ci, etag_ci)
                })
            })
            .unzip();

        (v_ei_ci, RawFiltered::new(v_etag, v_ci))
    }

    /// Determines the entity is matched by the filter.
    /// If so, returns matching information.
    fn filter<S>(
        ent_stor: &EntityStorage<S>,
        ei: EntityIndex,
        finfo: &FilterInfo,
    ) -> Option<(usize, EntityTag)>
    where
        S: BuildHasher + Default,
    {
        let ekey = EntityKey::from(ei);
        let cont = ent_stor.get_entity_container(&ekey)?;
        if !finfo.filter(|ckey| cont.contains_column(ckey)) {
            return None;
        }

        // Safety:
        // - ckeys: `ekey` has its container, which means `ekey` can be converted.
        // - etag: Scheduler guarantees arguments won't be dropped or incorrectly aliased
        // while the etag is in use.
        // - ci: It's safe because we've already filtered.
        unsafe {
            let ckeys = ent_stor.get_component_keys(&ekey).unwrap_unchecked();
            let etag = EntityTag::new(ei, cont.name().clone(), ckeys, cont.comp_names());
            let ci = cont.get_column_index(finfo.target()).unwrap_unchecked();
            Some((ci, etag))
        }
    }
}

/// Each system has a dedicated cache item.
/// Cache item contains indices to the wait queues for entities, components, and resources.
/// Plus, the item also contains buffer for request data.
#[derive(Debug)]
pub(super) struct CacheItem {
    wait: Rc<RefCell<WaitIndices>>,
    retry: WaitRetryIndices,
    buf: Box<SystemBuffer>,
}

impl CacheItem {
    fn new(wait: Rc<RefCell<WaitIndices>>) -> Self {
        Self {
            wait,
            retry: WaitRetryIndices::new(),
            buf: Box::new(SystemBuffer::new()),
        }
    }

    pub(super) fn get_wait_indices(&self) -> Ref<WaitIndices> {
        self.wait.borrow()
    }

    pub(super) fn get_request_buffer_mut(&mut self) -> &mut SystemBuffer {
        &mut self.buf
    }

    pub(super) fn request_buffer_ptr(&mut self) -> NonNullExt<SystemBuffer> {
        // Safety: Infallible.
        unsafe { NonNullExt::new_unchecked(self.get_request_buffer_mut() as *mut _) }
    }

    fn refresh<S>(&mut self, _ent_stor: &mut EntityStorage<S>, _res_stor: &mut ResourceStorage<S>)
    where
        S: BuildHasher + Default,
    {
        #[cfg(feature = "borrow_check")]
        self._refresh(_ent_stor, _res_stor);
    }

    fn finish_update<S>(
        &mut self,
        _ent_stor: &mut EntityStorage<S>,
        _res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default,
    {
        #[cfg(not(feature = "borrow_check"))]
        {
            self.buf.clear_force();
            self._refresh(_ent_stor, _res_stor);
        }
    }

    fn _refresh<S>(&mut self, ent_stor: &mut EntityStorage<S>, res_stor: &mut ResourceStorage<S>)
    where
        S: BuildHasher + Default,
    {
        // Updates component buffer.
        for filtered in self.buf.read.iter_mut() {
            let (etags, col_idxs, query_res) = filtered.take();

            // The buffer must be consumed in advance.
            debug_assert!(query_res.is_empty());
            for (ei, ci) in RawFiltered::iter_index_pair(etags, col_idxs) {
                let cont = ent_stor.get_entity_container(&EntityKey::from(ei)).unwrap();
                let col = cont.borrow_column(ci).unwrap();
                query_res.push(col);
            }
        }
        for filtered in self.buf.write.iter_mut() {
            let (etags, col_idxs, query_res) = filtered.take();

            // The buffer must be consumed in advance.
            debug_assert!(query_res.is_empty());
            for (ei, ci) in RawFiltered::iter_index_pair(etags, col_idxs) {
                let cont = ent_stor
                    .get_entity_container_mut(&EntityKey::from(ei))
                    .unwrap();
                let col = cont.borrow_column_mut(ci).unwrap();
                query_res.push(col);
            }
        }

        // Updates read resource buffer.
        // The buffer must be consumed in advance.
        debug_assert!(self.buf.res_read.is_empty());
        for ri in self.wait.borrow().res_read.iter().cloned() {
            let borrowed = res_stor.borrow(ri).unwrap();
            self.buf.res_read.push(borrowed);
        }

        // Updates write resource buffer.
        // The buffer must be consumed in advance.
        debug_assert!(self.buf.res_write.is_empty());
        for ri in self.wait.borrow().res_write.iter().cloned() {
            let borrowed = res_stor.borrow_mut(ri).unwrap();
            self.buf.res_write.push(borrowed);
        }

        // Updates entity buffer.
        // The buffer must be consumed in advance.
        debug_assert!(self.buf.ent_write.is_empty());
        for ei in self.wait.borrow().ent_write.iter().cloned() {
            // Safety: We didn't keep the generation of the entity container,
            // But we guarantee that it's fine.
            // TODO: Should we preserve the generation as well?
            let borrowed = unsafe { ent_stor.borrow_unchecked_mut(ei).unwrap() };
            self.buf.ent_write.push(borrowed);
        }
    }
}

/// Cache storage at a time.
/// This dosen't allow new item to be registered,
/// but you can read or write each item in the cache.
#[derive(Debug)]
pub(super) struct RefreshCacheStorage<'a, S> {
    pub(super) cache_stor: &'a mut CacheStorage<S>,
    pub(super) ent_stor: &'a mut EntityStorage<S>,
    pub(super) res_stor: &'a mut ResourceStorage<S>,
}

impl<'a, S> RefreshCacheStorage<'a, S>
where
    S: BuildHasher,
{
    pub(crate) fn new(
        cache_stor: &'a mut CacheStorage<S>,
        ent_stor: &'a mut EntityStorage<S>,
        res_stor: &'a mut ResourceStorage<S>,
    ) -> Self {
        Self {
            cache_stor,
            ent_stor,
            res_stor,
        }
    }

    pub(crate) fn get(&self, sid: &SystemId) -> Option<&CacheItem> {
        self.cache_stor.items.get(sid).map(|(item, _sinfo)| item)
    }

    pub(crate) fn get_mut(&mut self, sid: &SystemId) -> Option<RefreshCacheItem<S>> {
        self.cache_stor
            .items
            .get_mut(sid)
            .map(|(item, _sinfo)| RefreshCacheItem {
                item,
                ent_stor: self.ent_stor,
                res_stor: self.res_stor,
            })
    }
}

#[derive(Debug)]
pub(super) struct RefreshCacheItem<'a, S> {
    item: &'a mut CacheItem,
    ent_stor: &'a mut EntityStorage<S>,
    res_stor: &'a mut ResourceStorage<S>,
}

impl<'a, S> RefreshCacheItem<'a, S>
where
    S: BuildHasher + Default,
{
    pub(super) fn get_wait_retry_indices_mut(
        &mut self,
    ) -> (Ref<WaitIndices>, &mut WaitRetryIndices) {
        (self.item.wait.borrow(), &mut self.item.retry)
    }

    /// Refreshes cache item by re-borrowing the data.
    pub(super) fn refresh(self) -> &'a mut CacheItem {
        let Self {
            item,
            ent_stor,
            res_stor,
        } = self;
        item.refresh(ent_stor, res_stor);
        item
    }
}

impl<'a, S> Deref for RefreshCacheItem<'a, S> {
    type Target = CacheItem;

    fn deref(&self) -> &Self::Target {
        self.item
    }
}

impl<'a, S> DerefMut for RefreshCacheItem<'a, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.item
    }
}

#[cfg(test)]
#[allow(dead_code, non_camel_case_types)]
#[rustfmt::skip]
mod tests {
    use super::*;
    use crate::{self as my_ecs, ecs::sys::system::PrivateSystem};
    use crate::prelude::*;
    use std::hash::RandomState;

    // To test if addresses are cached correctly, declares structs including 
    // non-ZST types.

    // Components and filters.
    #[derive(Component)] struct Empty;
    #[derive(Component)] struct C0(i32); filter!(F0, Target = C0);
    #[derive(Component)] struct C1(i32); filter!(F1, Target = C1);
    #[derive(Component)] struct C2(i32); filter!(F2, Target = C2);

    // Entities.
    #[derive(Entity)] struct E0_C0 { c: C0 }
    #[derive(Entity)] struct E1_C0 { c: C0, x: Empty }
    #[derive(Entity)] struct E2_C1 { c: C1 }
    #[derive(Entity)] struct E3_C1 { c: C1, x: Empty }
    #[derive(Entity)] struct E4_C0C1 { c0: C0, c1: C1 }
    #[derive(Entity)] struct E5_C2 { c: C2 }

    // Resources.
    #[derive(Resource)] struct R0(i32);
    #[derive(Resource)] struct R1(i32);

    #[test]
    fn test_cachestorage_update() {
        let mut cache_stor = CacheStorage::<RandomState>::new();
        let mut ent_stor = EntityStorage::<RandomState>::new();
        let mut res_stor = ResourceStorage::<RandomState>::new();

        validate_cache_read_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
        validate_cache_write_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
        validate_cache_res_read_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
        validate_cache_res_write_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
        validate_cache_ent_write_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
        validate_cache_mixed_update(&mut cache_stor, &mut ent_stor, &mut res_stor);
    }

    // Registers/Unregisters entities and sees if the cache item will be updated
    // as expected.
    fn validate_cache_read_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        // 1. Add E0_C0: Cached 1 C0 by F0
        // 2. Add E1_C0: Cached 2 C0 by F0
        // 3. Add E2_C1: Cached 2 C0 by F0 + 1 C1 by F1
        // 4. Add E3_C1: Cached 2 C0 by F0 + 2 C1 by F1
        // 5. Del E0_C0: Cached 1 C0 by F0 + 2 C1 by F1
        // 6. Del E1_C0: Cached 2 C1 by F1
        // 7. Del E2_C1: Cached 1 C1 by F1
        // 8. Del E3_C1: None
        // 9. Add/Del E5_C2: None

        let sys = FnSystem::from(|_: Read<(F0, F1)>| {});
        let sdata = sys.into_data();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);

        validate_entity_reg::<E0_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[1, 0], &[], 0, 0, 0)
        );
        validate_entity_reg::<E1_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[2, 0], &[], 0, 0, 0)
        );
        validate_entity_reg::<E2_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[2, 1], &[], 0, 0, 0)
        );
        validate_entity_reg::<E3_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[2, 2], &[], 0, 0, 0)
        );
        validate_entity_unreg::<E0_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[1, 2], &[], 0, 0, 0)
        );
        validate_entity_unreg::<E1_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0, 2], &[], 0, 0, 0)
        );
        validate_entity_unreg::<E2_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0, 1], &[], 0, 0, 0)
        );
        validate_entity_unreg::<E3_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0, 0], &[], 0, 0, 0)
        );
        validate_entity_reg::<E5_C2, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0, 0], &[], 0, 0, 0)
        );
        validate_entity_unreg::<E5_C2, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0, 0], &[], 0, 0, 0)
        );

        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    // Registers/Unregisters entities and sees if the cache item will be updated
    // as expected.
    fn validate_cache_write_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        // 1. Add E0_C0: Cached 1 C0 by F0
        // 2. Add E1_C0: Cached 2 C0 by F0
        // 3. Add E2_C1: Cached 2 C0 by F0 + 1 C1 by F1
        // 4. Add E3_C1: Cached 2 C0 by F0 + 2 C1 by F1
        // 5. Del E0_C0: Cached 1 C0 by F0 + 2 C1 by F1
        // 6. Del E1_C0: Cached 2 C1 by F1
        // 7. Del E2_C1: Cached 1 C1 by F1
        // 8. Del E3_C1: None
        // 9. Add/Del E5_C2: None

        let sys = FnSystem::from(|_: Write<(F0, F1)>| {});
        let sdata = sys.into_data();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);

        validate_entity_reg::<E0_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[1, 0], 0, 0, 0)
        );
        validate_entity_reg::<E1_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[2, 0], 0, 0, 0)
        );
        validate_entity_reg::<E2_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[2, 1], 0, 0, 0)
        );
        validate_entity_reg::<E3_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[2, 2], 0, 0, 0)
        );
        validate_entity_unreg::<E0_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[1, 2], 0, 0, 0)
        );
        validate_entity_unreg::<E1_C0, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[0, 2], 0, 0, 0)
        );
        validate_entity_unreg::<E2_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[0, 1], 0, 0, 0)
        );
        validate_entity_unreg::<E3_C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[0, 0], 0, 0, 0)
        );
        validate_entity_reg::<E5_C2, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[0, 0], 0, 0, 0)
        );
        validate_entity_unreg::<E5_C2, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[], &[0, 0], 0, 0, 0)
        );

        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    fn validate_cache_res_read_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        // 1. With R0 and R1, Del R0: Removed item
        // 2. With R0 and R1, Del R1: Removed item

        // Res: None -> R0, R1
        // Cache: None
        res_stor.register(ResourceDesc::new().with_owned(R0(0))).unwrap();
        res_stor.register(ResourceDesc::new().with_owned(R1(0))).unwrap();
        let sys = FnSystem::from(|_: ResRead<(R0, R1)>| {});
        let sdata = sys.into_data();

        // 1. With R0 and R1, Del R0: Removed item
        // Res: R0, R1 -> R1
        // Cache: None -> Sys -> None
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_resource_unreg(R0::resource_key());
        res_stor.unregister(&R0::resource_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // 2. With R0 and R1, Del R1: Removed item
        // Res: R1 -> R0, R1 -> R0
        // Cache: None -> Sys -> None
        res_stor.register(ResourceDesc::new().with_owned(R0(0))).unwrap();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_resource_unreg(R1::resource_key());
        res_stor.unregister(&R1::resource_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // Clean up
        res_stor.unregister(&R0::resource_key());
        res_stor.unregister(&R1::resource_key());
        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    fn validate_cache_res_write_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        // 1. With R0 and R1, Del R0: Removed item
        // 2. With R0 and R1, Del R1: Removed item

        // Res: None -> R0, R1
        // Cache: None
        res_stor.register(ResourceDesc::new().with_owned(R0(0))).unwrap();
        res_stor.register(ResourceDesc::new().with_owned(R1(0))).unwrap();
        let sys = FnSystem::from(|_: ResWrite<(R0, R1)>| {});
        let sdata = sys.into_data();

        // 1. With R0 and R1, Del R0: Removed item
        // Res: R0, R1 -> R1
        // Cache: None -> Sys -> None
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_resource_unreg(R0::resource_key());
        res_stor.unregister(&R0::resource_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // 2. With R0 and R1, Del R1: Removed item
        // Res: R1 -> R0, R1 -> R0
        // Cache: None -> Sys -> None
        res_stor.register(ResourceDesc::new().with_owned(R0(0))).unwrap();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_resource_unreg(R1::resource_key());
        res_stor.unregister(&R1::resource_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // Clean up
        res_stor.unregister(&R0::resource_key());
        res_stor.unregister(&R1::resource_key());
        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    fn validate_cache_ent_write_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        // 1. With E0_C0 and E1_C0, Del E0_C0: Removed item
        // 2. With E0_C0 and E1_C0, Del E1_C0: Removed item

        // Ent: None -> E0_C0, E1_C0
        // Cache: None
        ent_stor.register(E0_C0::as_entity_descriptor()).unwrap();
        ent_stor.register(E1_C0::as_entity_descriptor()).unwrap();
        let sys = FnSystem::from(|_: EntWrite<(E0_C0, E1_C0)>| {});
        let sdata = sys.into_data();

        // 1. With E0_C0 and E1_C0, Del E0_C0: Removed item
        // Ent: E0_C0, E1_C0 -> E1_C0
        // Cache: None -> Sys -> None
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_entity_unreg(E0_C0::entity_key(), ent_stor, res_stor);
        ent_stor.unregister(&E0_C0::entity_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // 2. With E0_C0 and E1_C0, Del E1_C0: Removed item
        // Ent: E1_C0 -> E0_C0, E1_C0 -> E0_C0
        // Cache: None -> Sys -> None
        ent_stor.register(E0_C0::as_entity_descriptor()).unwrap();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);
        cache_stor.update_by_entity_unreg(E1_C0::entity_key(), ent_stor, res_stor);
        ent_stor.unregister(&E1_C0::entity_key()).unwrap();
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());

        // Clean up
        ent_stor.unregister(&E0_C0::entity_key());
        ent_stor.unregister(&E1_C0::entity_key());
        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    fn validate_cache_mixed_update<S>(
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        res_stor.register(ResourceDesc::new().with_owned(R0(0))).unwrap();
        res_stor.register(ResourceDesc::new().with_owned(R1(0))).unwrap();
        ent_stor.register(E5_C2::as_entity_descriptor()).unwrap();

        let sys = FnSystem::from(|
            _: Read<F0>, 
            _: Write<F1>,
            _: ResRead<R0>,
            _: ResWrite<R1>,
            _: EntWrite<E5_C2>| {}
        );
        let sdata = sys.into_data();
        cache_stor.update_by_system_reg(&sdata, ent_stor, res_stor);

        validate_entity_reg::<E4_C0C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[1], &[1], 1, 1, 1)
        );
        validate_entity_unreg::<E4_C0C1, S>(
            &sdata, cache_stor, ent_stor, res_stor, (&[0], &[0], 1, 1, 1)
        );

        cache_stor.update_by_system_unreg(&sdata.id());
        assert!(cache_stor.items.is_empty());
        assert!(cache_stor.noti.is_empty());
    }

    fn validate_entity_reg<E, S>(
        sdata: &SystemData,
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
        expect_len: (&[usize], &[usize], usize, usize, usize),
    ) where
        E: AsEntityReg,
        S: BuildHasher + Default + Clone + 'static,
    {
        // Register entity and then updates cache.
        let ei = ent_stor.register(E::as_entity_descriptor()).unwrap();
        cache_stor.update_by_entity_reg(ei, ent_stor, res_stor);

        // Validates.
        validate_item(&sdata, cache_stor, ent_stor, res_stor, expect_len);
    }

    fn validate_entity_unreg<E, S>(
        sdata: &SystemData,
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
        expect_len: (&[usize], &[usize], usize, usize, usize),
    ) where
        E: Entity + AsEntityReg,
        S: BuildHasher + Default + Clone + 'static,
    {
        // Update cache and then register entity.
        cache_stor.update_by_entity_unreg(E::entity_key(), ent_stor, res_stor);
        ent_stor.unregister(&E::entity_key()).unwrap();

        // Validates.
        validate_item(&sdata, cache_stor, ent_stor, res_stor, expect_len);
    }

    fn validate_item<S>(
        sdata: &SystemData,
        cache_stor: &mut CacheStorage<S>,
        ent_stor: &mut EntityStorage<S>,
        res_stor: &mut ResourceStorage<S>,
        expect_len: (&[usize], &[usize], usize, usize, usize),
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        let (item, _sinfo) = cache_stor.items.get_mut(&sdata.id()).unwrap();
        item.refresh(ent_stor, res_stor);
        validate_len(item, expect_len);
        validate_item_inner(item, &sdata.get_request_info(), ent_stor, res_stor);
        item.buf.clear();
    }

    fn validate_len(item: &CacheItem, expect_len: (&[usize], &[usize], usize, usize, usize)) {
        let validate_query = |buf: &[RawFiltered], exp_lens: &[usize]| {
            assert_eq!(buf.len(), exp_lens.len());
            for (filtered, &expect_len) in buf.iter().zip(exp_lens) {
                let getters = filtered.query_res();
                assert_eq!(getters.len(), expect_len);
            }
        };

        validate_query(&item.buf.read, expect_len.0);
        validate_query(&item.buf.write, expect_len.1);
        assert_eq!(item.buf.res_read.len(), expect_len.2);
        assert_eq!(item.buf.res_write.len(), expect_len.3);
        assert_eq!(item.buf.ent_write.len(), expect_len.4);
    }

    /// Validates cache item with respect to things described below.
    /// - Does it have valid wait indices?
    /// - Does it have valid buffer addresses?
    fn validate_item_inner<S>(
        item: &CacheItem,
        rinfo: &RequestInfo,
        ent_stor: &EntityStorage<S>,
        res_stor: &ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        let sys_idxs = SystemIndices::new(rinfo, ent_stor, res_stor);
        validate_wait_indices(&item.wait.borrow(), &sys_idxs);
        validate_buffer_addresses(&item.buf, &sys_idxs, ent_stor, res_stor);
    }

    /// Checks whether or not wait indices are the same as indices gotten from
    /// storages.
    fn validate_wait_indices(waits: &WaitIndices, sys_idxs: &SystemIndices) {
        let WaitIndices {
            read: wait_read,
            write: wait_write,
            res_read: wait_res_read,
            res_write: wait_res_write,
            ent_write: wait_ent_write,
        } = waits;
        let SystemIndices {
            read: sys_read,
            write: sys_write,
            res_read: sys_res_read,
            res_write: sys_res_write,
            ent_write: sys_ent_write,
        } = sys_idxs;

        let validate_query = |wait: &DedupVec<(usize, usize), false>,
                              sys: &[Vec<(usize, usize)>]| {
            let mut wait = wait.iter().cloned().collect::<Vec<_>>();
            let mut sys = sys.iter().flatten().cloned().collect::<Vec<_>>();

            // - Wait indices are basically deduplicated, but not sorted.
            // - Indices we got for testing are neither sorted nor deduplicated.
            wait.sort_unstable();
            sys.sort_unstable();
            sys.dedup();
            assert_eq!(wait, sys);
        };

        let validate_res_ent_query = |wait: &DedupVec<usize, false>, sys: &[usize]| {
            let mut wait = wait.iter().cloned().collect::<Vec<_>>();
            let mut sys = sys.iter().cloned().collect::<Vec<_>>();

            // # Indices for resource and entity queries cannot be duplicated.
            // - Wait indices are not sorted.
            // - Indices we got for testing are not sorted.
            wait.sort_unstable();
            sys.sort_unstable();
            assert_eq!(wait, sys);
        };

        validate_query(wait_read, sys_read);
        validate_query(wait_write, sys_write);
        validate_res_ent_query(wait_res_read, sys_res_read);
        validate_res_ent_query(wait_res_write, sys_res_write);
        validate_res_ent_query(wait_ent_write, sys_ent_write);
    }

    fn validate_buffer_addresses<S>(
        buf: &SystemBuffer,
        sys_idxs: &SystemIndices,
        ent_stor: &EntityStorage<S>,
        res_stor: &ResourceStorage<S>,
    ) where
        S: BuildHasher + Default + Clone + 'static,
    {
        let SystemBuffer {
            read: buf_read,
            write: buf_write,
            res_read: buf_res_read,
            res_write: buf_res_write,
            ent_write: buf_ent_write,
        } = buf;
        let SystemIndices {
            read: sys_read,
            write: sys_write,
            res_read: sys_res_read,
            res_write: sys_res_write,
            ent_write: sys_ent_write,
        } = sys_idxs;

        let validate_query = |buf: &[RawFiltered], sys: &[Vec<(usize, usize)>]| {
            assert_eq!(buf.len(), sys.len());
            for (buf_filtered, sys_pairs) in buf.iter().zip(sys) {
                let buf_getters = buf_filtered.query_res();
                assert_eq!(buf_getters.len(), sys_pairs.len());

                // Note that buf_getters need to be sorted. See example below.
                // Query: (Fa, ...)
                // Fa -> (E0-C0), (E1-C0), ... : OK.
                // Fa -> (E1-C0), (E0-C0), ... : Also OK.

                let mut buf_ptrs = buf_getters
                    .iter()
                    .map(|getter| getter.ptr())
                    .collect::<Vec<_>>();

                let mut sys_ptrs = sys_pairs
                    .iter()
                    .map(|&(ei, ci)| unsafe {
                        let cont = ent_stor.get_ptr(ei).unwrap().as_ref();
                        cont.get_column_ptr(ci).unwrap()
                    })
                    .collect::<Vec<_>>();

                buf_ptrs.sort_unstable();
                sys_ptrs.sort_unstable();

                assert_eq!(buf_ptrs, sys_ptrs);
            }
        };

        // Validates read and write queries.
        validate_query(buf_read, sys_read);
        validate_query(buf_write, sys_write);

        // Validates resource read query.
        assert_eq!(buf_res_read.len(), sys_res_read.len());
        for (buf_ptr, ri) in buf_res_read.iter().zip(sys_res_read) {
            let sys_ptr = unsafe { res_stor.get_ptr(*ri).unwrap() };
            assert_eq!(buf_ptr.inner(), sys_ptr);
        }

        // Validates resource write query.
        assert_eq!(buf_res_write.len(), sys_res_write.len());
        for (buf_ptr, ri) in buf_res_write.iter().zip(sys_res_write) {
            let sys_ptr = unsafe { res_stor.get_ptr(*ri).unwrap() };
            assert_eq!(buf_ptr.inner(), sys_ptr);
        }

        // Validates entity write query.
        assert_eq!(buf_ent_write.len(), sys_ent_write.len());
        for (buf_ptr, ei) in buf_ent_write.iter().zip(sys_ent_write) {
            let sys_ptr = unsafe { ent_stor.get_ptr(*ei).unwrap() };
            assert_eq!(**buf_ptr, sys_ptr);
        }
    }

    struct SystemIndices {
        // Query: (Fa, Fb, ...)
        // Indices: Vec of Vec of (ei, ci)
        read: Vec<Vec<(usize, usize)>>,
        write: Vec<Vec<(usize, usize)>>,
        // Resource query: (Ra, Rb, ...)
        // Indices: Vec of ri
        res_read: Vec<usize>,
        res_write: Vec<usize>,
        // Entity query: (Ea, Eb, ...)
        // Indices: Vec of ei
        ent_write: Vec<usize>,
    }

    impl SystemIndices {
        fn new<S>(
            rinfo: &RequestInfo,
            ent_stor: &EntityStorage<S>,
            res_stor: &ResourceStorage<S>,
        ) -> Self
        where
            S: BuildHasher + Default + Clone + 'static,
        {
            let query_indices = |qinfo: &QueryInfo| {
                qinfo
                    .filters()
                    .iter()
                    .map(|(_, finfo)| {
                        FilterUtil::filter_all(ent_stor, finfo)
                            .0
                            .into_iter()
                            .map(|(ei, ci)| (ei.index(), ci))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            };

            let res_query_indices = |rqinfo: &ResQueryInfo| {
                rqinfo
                    .rkeys()
                    .iter()
                    .map(|rkey| res_stor.index(rkey).unwrap())
                    .collect::<Vec<_>>()
            };

            let ent_query_indices = |eqinfo: &EntQueryInfo| {
                eqinfo
                    .ekeys()
                    .iter()
                    .map(|ekey| ent_stor.entity_index(ekey).unwrap())
                    .collect::<Vec<_>>()
            };

            Self {
                read: query_indices(&rinfo.read().1),
                write: query_indices(&rinfo.write().1),
                res_read: res_query_indices(&rinfo.res_read().1),
                res_write: res_query_indices(&rinfo.res_write().1),
                ent_write: ent_query_indices(&rinfo.ent_write().1),
            }
        }
    }
}
