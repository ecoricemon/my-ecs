use super::{
    filter::{self, RawFiltered},
    query::{
        EntQueryInfo, EntQueryKey, EntQueryMut, Query, QueryInfo, QueryKey, QueryMut, ResQuery,
        ResQueryInfo, ResQueryKey, ResQueryMut, StoreEntQueryInfo, StoreQueryInfo,
        StoreResQueryInfo,
    },
};
use crate::{
    debug_format,
    ds::prelude::*,
    ecs::{
        ent::entity::{ContainEntity, EntityKey},
        resource::ResourceKey,
    },
};
use std::{any, marker::PhantomData, ptr::NonNull, rc::Rc, sync::atomic::AtomicI32};

/// A single request is about needs for all sorts of components, resources,
/// and entity containers.
/// In other words, a request is a combination of [`Query`]s, [`ResQuery`]s,
/// and queries for entity containers.
/// They must be requested at once in order to prevent dead lock.
/// You can make a request by implementing this trait and put it in a system.
//
// TODO: For now, `Request` doesn't have to be `Send`.
// But, when clients register not thread safe resources to ECS,
// And request it, will it be safe?
pub trait Request: 'static {
    /// Read-only access [`Query`] composed of [`Filter`](super::filter::Filter)s.
    /// Read-only access can help us execute systems simultaneously.
    type Read: Query;

    /// Writable access [`QueryMut`] composed of [`Filter`](super::filter::Filter)s.
    /// Writable access always takes exclusive authority over the target.
    type Write: QueryMut;

    /// Read-only access [`ResQuery`] composed of [`Resource`](super::resource::Resource)s.
    /// Read-only access can help us execute systems simultaneously.
    type ResRead: ResQuery;

    /// Writable access [`ResQueryMut`] composed of [`Resource`](super::resource::Resource)s.
    /// Writable access always takes exclusive authority over the target.
    type ResWrite: ResQueryMut;

    /// Writable access [`EntQueryMut`] composed of [`Entity`](super::entity::Entity).
    /// Writable acess always takes exclusive authority over the target.
    type EntWrite: EntQueryMut;

    fn key() -> RequestKey {
        RequestKey::of::<Self>()
    }
}

/// [`Request`], but not exposed to clients.
/// This trait is implemented and used in the crate only.
pub(crate) trait PrivateRequest: Request {
    fn get_info<S>(stor: &mut S) -> Rc<RequestInfo>
    where
        S: StoreRequestInfo,
    {
        let key = Self::key();
        if let Some(info) = StoreRequestInfo::get(stor, &key) {
            info
        } else {
            let info = Rc::new(RequestInfo {
                name: any::type_name::<Self>(),
                read: (
                    <Self::Read as Query>::key(),
                    <Self::Read as Query>::get_info(stor),
                ),
                write: (
                    <Self::Write as QueryMut>::key(),
                    <Self::Write as QueryMut>::get_info(stor),
                ),
                res_read: (
                    <Self::ResRead as ResQuery>::key(),
                    <Self::ResRead as ResQuery>::get_info(stor),
                ),
                res_write: (
                    <Self::ResWrite as ResQueryMut>::key(),
                    <Self::ResWrite as ResQueryMut>::get_info(stor),
                ),
                ent_write: (
                    <Self::EntWrite as EntQueryMut>::key(),
                    <Self::EntWrite as EntQueryMut>::get_info(stor),
                ),
            });
            StoreRequestInfo::insert(stor, key, &info);
            info
        }
    }
}

impl<T: Request> PrivateRequest for T {}

/// Blanket implementation of [`Request`] for tuples of queries.
impl<R, W, RR, RW, EW> Request for (R, W, RR, RW, EW)
where
    R: Query,
    W: QueryMut,
    RR: ResQuery,
    RW: ResQueryMut,
    EW: EntQueryMut,
{
    type Read = R;
    type Write = W;
    type ResRead = RR;
    type ResWrite = RW;
    type EntWrite = EW;
}

/// A macro for declaration of an empty structure and implementation [`Request`] for the structure.
#[macro_export]
macro_rules! request {
    (
        $vis:vis $id:ident
        $(, Read=( $($read:ty),+ ))?
        $(, Write=( $($write:ty),+ ))?
        $(, ResRead=( $($res_read:ty),+ ))?
        $(, ResWrite=( $($res_write:ty),+ ))?
        $(, EntWrite=( $($ent_write:ty),+ ))?
    ) => {
        #[derive(Debug)]
        $vis struct $id;
        impl $crate::ecs::sys::request::Request for $id {
            #[allow(unused_parens)]
            type Read = ( $( $($read),+ )? );

            #[allow(unused_parens)]
            type Write = ( $( $($write),+ )? );

            #[allow(unused_parens)]
            type ResRead = ( $( $($res_read),+ )? );

            #[allow(unused_parens)]
            type ResWrite = ( $( $($res_write),+ )? );

            #[allow(unused_parens)]
            type EntWrite = ( $( $($ent_write),+ )? );
        }
    };
}

pub(crate) trait StoreRequestInfo:
    StoreQueryInfo + StoreResQueryInfo + StoreEntQueryInfo
{
    fn get(&self, key: &RequestKey) -> Option<Rc<RequestInfo>>;
    fn insert(&mut self, key: RequestKey, info: &Rc<RequestInfo>);
    fn remove(&mut self, key: &RequestKey);
}

/// [`TypeId`] of a [`Request`].
pub type RequestKey = ATypeId<RequestKey_>;
pub struct RequestKey_;

#[derive(Debug, Clone)]
pub(crate) struct RequestInfo {
    name: &'static str,
    read: (QueryKey, Rc<QueryInfo>),
    write: (QueryKey, Rc<QueryInfo>),
    res_read: (ResQueryKey, Rc<ResQueryInfo>),
    res_write: (ResQueryKey, Rc<ResQueryInfo>),
    ent_write: (EntQueryKey, Rc<EntQueryInfo>),
}

impl RequestInfo {
    // For future use
    #[allow(dead_code)]
    pub(crate) fn name(&self) -> &'static str {
        self.name
    }

    pub(crate) fn read(&self) -> &(QueryKey, Rc<QueryInfo>) {
        &self.read
    }

    pub(crate) fn write(&self) -> &(QueryKey, Rc<QueryInfo>) {
        &self.write
    }

    pub(crate) fn res_read(&self) -> &(ResQueryKey, Rc<ResQueryInfo>) {
        &self.res_read
    }

    pub(crate) fn res_write(&self) -> &(ResQueryKey, Rc<ResQueryInfo>) {
        &self.res_write
    }

    pub(crate) fn ent_write(&self) -> &(EntQueryKey, Rc<EntQueryInfo>) {
        &self.ent_write
    }

    pub(crate) fn resource_keys(&self) -> impl Iterator<Item = &ResourceKey> {
        let read = self.res_read().1.as_ref();
        let write = self.res_write().1.as_ref();
        read.rkeys().iter().chain(write.rkeys())
    }

    pub(crate) fn entity_keys(&self) -> impl Iterator<Item = &EntityKey> {
        self.ent_write().1.as_ref().ekeys().iter()
    }

    /// Determines whether the request info is valid or not in terms of
    /// `Read`, `Write`, `ResRead`, and `ResWrite`.
    /// Request info that meets conditions below is valid.
    /// - Write query filters are disjoint against other filters.
    /// - Write resource query doesn't overlap other read or write resource query.
    ///
    /// Note that request info cannot validate `EntWrite` itself.
    /// That must be validated outside.
    pub(crate) fn validate(&self) -> Result<(), String> {
        // 1. Write query contains disjoint filters only?
        let (_, r_qinfo) = self.read();
        let (_, w_qinfo) = self.write();
        let r_filters = r_qinfo.filters();
        let w_filters = w_qinfo.filters();
        for i in 0..w_filters.len() {
            // Doesn't overlap other write?
            for j in i + 1..w_filters.len() {
                if !filter::is_disjoint(&w_filters[i].1, &w_filters[j].1) {
                    let errmsg = debug_format!(
                        "`{}` and `{}` are not disjoint in request `{}`",
                        w_filters[i].1.name(),
                        w_filters[j].1.name(),
                        self.name(),
                    );
                    return Err(errmsg);
                }
            }
            // Doesn't overlap read?
            for (_, r_filter) in r_filters.iter() {
                if !filter::is_disjoint(&w_filters[i].1, r_filter) {
                    let errmsg = debug_format!(
                        "`{}` and `{}` are not disjoint in request `{}`",
                        w_filters[i].1.name(),
                        r_filter.name(),
                        self.name(),
                    );
                    return Err(errmsg);
                }
            }
        }

        // 2. Write resource query doesn't overlap other resource queries?
        let (_, r_rqinfo) = self.res_read();
        let (_, w_rqinfo) = self.res_write();
        let r_keys = r_rqinfo.rkeys();
        let w_keys = w_rqinfo.rkeys();
        for i in 0..w_keys.len() {
            // Doesn't overlap other write?
            for j in i + 1..w_keys.len() {
                if w_keys[i] == w_keys[j] {
                    let errmsg = debug_format!(
                        "duplicate resource query `{:?}` in request `{}`",
                        w_keys[i],
                        self.name(),
                    );
                    return Err(errmsg);
                }
            }
            // Doesn't overlap read?
            for r_key in r_keys.iter() {
                if &w_keys[i] == r_key {
                    let errmsg = debug_format!(
                        "duplicate resource query `{:?}` in request `{}`",
                        w_keys[i],
                        self.name(),
                    );
                    return Err(errmsg);
                }
            }
        }

        Ok(())
    }
}

/// Empty request.
impl Request for () {
    type Read = ();
    type Write = ();
    type ResRead = ();
    type ResWrite = ();
    type EntWrite = ();
}

/// System buffer for request.  
/// Each system has its buffer for the system's request.
/// The buffer has borrowed data for the request in it, but, it doesn't actually own it.
/// Because the buffer exists as long as the system and won't be freed.
/// Plus, each field must be released individually.
//
// Why system buffer, not request buffer?
// Q. Many systems can have the same request, so is they be able to share the same buffer?
// A. Because of borrow check, we need system-individual buffer.
// - We check borrow status, so we need to borrow and release data everytime.
//   * Borrow check helps us avoid running into hidden data race during development.
// - Each system borrows, conceptually, needed data, and then release them at the end of task.
//   * So we can detect borrow violation.
//
// See [RefreshCacheItem::refresh] and [Filtered::drop].
#[derive(Debug)]
pub struct SystemBuffer {
    /// Buffer for read-only borrowed component arrays for the system's request.
    pub(crate) read: Box<[RawFiltered]>,

    /// Buffer for writable borrowed component arrays for the system's request.
    pub(crate) write: Box<[RawFiltered]>,

    /// Buffer for read-only borrowed resources for the system's request.
    pub(crate) res_read: Vec<Borrowed<ManagedConstPtr<u8>, AtomicI32>>,

    /// Buffer for writable borrowed resources for the system's request.
    pub(crate) res_write: Vec<Borrowed<ManagedMutPtr<u8>, AtomicI32>>,

    /// Buffer for writable borrowed entity container for the system's request.
    pub(crate) ent_write: Vec<Borrowed<NonNull<dyn ContainEntity>, AtomicI32>>,
}

// We're going to send this buffer to other threads with a system implementation.
// So it's needed to be `Send` like `dyn Invoke + Send`.
// Obviously, it includes raw pointers, which are unsafe to be sent.
// But scheduler guarantees there will be no violation.
unsafe impl Send for SystemBuffer {}

impl SystemBuffer {
    pub(crate) fn new() -> Self {
        Self {
            read: [].into(),
            write: [].into(),
            res_read: Vec::new(),
            res_write: Vec::new(),
            ent_write: Vec::new(),
        }
    }

    pub(crate) fn clear(&mut self) {
        for read in self.read.iter_mut() {
            read.clear();
        }
        for write in self.write.iter_mut() {
            write.clear();
        }
        self.res_read.clear();
        self.res_write.clear();
        self.ent_write.clear();
    }
}

impl Default for SystemBuffer {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Response<'buf, Req: Request> {
    pub read: <Req::Read as Query>::Output<'buf>,
    pub write: <Req::Write as QueryMut>::Output<'buf>,
    pub res_read: <Req::ResRead as ResQuery>::Output<'buf>,
    pub res_write: <Req::ResWrite as ResQueryMut>::Output<'buf>,
    pub ent_write: <Req::EntWrite as EntQueryMut>::Output<'buf>,
    _cleaner: BufferCleaner<'buf>,
}

impl<'buf, Req: Request> Response<'buf, Req> {
    pub fn new(buf: &'buf mut SystemBuffer) -> Self {
        // Safety: Infallible.
        let _cleaner = BufferCleaner {
            buf_ptr: unsafe { NonNull::new_unchecked(buf as *mut _) },
            _marker: PhantomData,
        };

        Self {
            read: <Req::Read as Query>::convert(&mut buf.read),
            write: <Req::Write as QueryMut>::convert(&mut buf.write),
            res_read: <Req::ResRead as ResQuery>::convert(&mut buf.res_read),
            res_write: <Req::ResWrite as ResQueryMut>::convert(&mut buf.res_write),
            ent_write: <Req::EntWrite as EntQueryMut>::convert(&mut buf.ent_write),
            _cleaner,
        }
    }
}

struct BufferCleaner<'buf> {
    buf_ptr: NonNull<SystemBuffer>,
    _marker: PhantomData<&'buf ()>,
}

impl<'buf> Drop for BufferCleaner<'buf> {
    fn drop(&mut self) {
        // Safety: We're actually borrowing `SystemBuffer` via `buf lifetime.
        let buf = unsafe { self.buf_ptr.as_mut() };
        buf.clear();
    }
}
