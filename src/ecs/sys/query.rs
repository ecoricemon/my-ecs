use super::select::{SelectInfo, SelectKey, SelectedRaw, StoreSelectInfo};
use crate::ds::prelude::*;
use crate::ecs::{
    ent::entity::{ContainEntity, EntityIndex, EntityKey},
    resource::ResourceKey,
};
use my_ecs_macros::repeat_macro;
use std::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
};

/// A shallow wrapper struct for the [`Query::Output`].
#[repr(transparent)]
pub struct Read<'buf, R: Query>(pub(crate) R::Output<'buf>);

impl<'buf, R: Query> Read<'buf, R> {
    pub fn take(self) -> R::Output<'buf> {
        self.0
    }
}

impl<'buf, R: Query> Deref for Read<'buf, R> {
    type Target = R::Output<'buf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A shallow wrapper struct for the [`QueryMut::Output`].
#[repr(transparent)]
pub struct Write<'buf, W: QueryMut>(pub(crate) W::Output<'buf>);

impl<'buf, W: QueryMut> Write<'buf, W> {
    pub fn take(self) -> W::Output<'buf> {
        self.0
    }
}

impl<'buf, W: QueryMut> Deref for Write<'buf, W> {
    type Target = W::Output<'buf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<W: QueryMut> DerefMut for Write<'_, W> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// A shallow wrapper struct for the [`ResQuery::Output`].
#[repr(transparent)]
pub struct ResRead<'buf, RR: ResQuery>(pub(crate) RR::Output<'buf>);

impl<'buf, RR: ResQuery> ResRead<'buf, RR> {
    pub fn take(self) -> RR::Output<'buf> {
        self.0
    }
}

impl<'buf, RR: ResQuery> Deref for ResRead<'buf, RR> {
    type Target = RR::Output<'buf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A shallow wrapper struct for the [`ResQueryMut::Output`].
#[repr(transparent)]
pub struct ResWrite<'buf, RW: ResQueryMut>(pub(crate) RW::Output<'buf>);

impl<'buf, RW: ResQueryMut> ResWrite<'buf, RW> {
    pub fn take(self) -> RW::Output<'buf> {
        self.0
    }
}

impl<'buf, RW: ResQueryMut> Deref for ResWrite<'buf, RW> {
    type Target = RW::Output<'buf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<RW: ResQueryMut> DerefMut for ResWrite<'_, RW> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// A shallow wrapper struct for the [`EntQueryMut::Output`].
#[repr(transparent)]
pub struct EntWrite<'buf, EW: EntQueryMut>(pub(crate) EW::Output<'buf>);

impl<'buf, EW: EntQueryMut> EntWrite<'buf, EW> {
    pub fn take(self) -> EW::Output<'buf> {
        self.0
    }
}

impl<'buf, EW: EntQueryMut> Deref for EntWrite<'buf, EW> {
    type Target = EW::Output<'buf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<EW: EntQueryMut> DerefMut for EntWrite<'_, EW> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Unique identifier for a type implementing [`Query`] or [`QueryMut`].
pub type QueryKey = ATypeId<QueryKey_>;
pub struct QueryKey_;

/// Unique identifier for a type implementing [`ResQuery`] or [`ResQueryMut`].
pub type ResQueryKey = ATypeId<ResQueryKey_>;
pub struct ResQueryKey_;

/// Unique identifier for a type implementing [`EntQueryMut`].
pub type EntQueryKey = ATypeId<EntQueryKey_>;
pub struct EntQueryKey_;

#[derive(Debug, Clone)]
pub struct QueryInfo {
    name: &'static str,
    sels: Box<[(SelectKey, Arc<SelectInfo>)]>,
}

impl QueryInfo {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn selectors(&self) -> &[(SelectKey, Arc<SelectInfo>)] {
        &self.sels
    }
}

#[derive(Debug, Clone)]
pub struct ResQueryInfo {
    name: &'static str,
    rkeys: Box<[ResourceKey]>,
}

impl ResQueryInfo {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn rkeys(&self) -> &[ResourceKey] {
        &self.rkeys
    }
}

#[derive(Debug, Clone)]
pub struct EntQueryInfo {
    pub name: &'static str,
    pub ekeys: Box<[EntityKey]>,
}

impl EntQueryInfo {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn ekeys(&self) -> &[EntityKey] {
        &self.ekeys
    }
}

pub trait StoreQueryInfo: StoreSelectInfo {
    fn contains(&self, key: &QueryKey) -> bool;
    fn get(&self, key: &QueryKey) -> Option<&Arc<QueryInfo>>;
    fn insert(&mut self, key: QueryKey, info: Arc<QueryInfo>);
}

pub trait StoreResQueryInfo {
    fn contains(&self, key: &ResQueryKey) -> bool;
    fn get(&self, key: &ResQueryKey) -> Option<&Arc<ResQueryInfo>>;
    fn insert(&mut self, key: ResQueryKey, info: Arc<ResQueryInfo>);
}

pub trait StoreEntQueryInfo {
    fn contains(&self, key: &EntQueryKey) -> bool;
    fn get(&self, key: &EntQueryKey) -> Option<&Arc<EntQueryInfo>>;
    fn insert(&mut self, key: EntQueryKey, info: Arc<EntQueryInfo>);
}

/// [`Query`] is a combination of [`Filter`](super::filter::Filter)s for read-only access.
/// For instance, `()`, `FilterA`, and `(FilterA, FilterB)` are sorts `Query`.
pub trait Query: 'static {
    type Output<'buf>;

    fn info_from<S>(stor: &mut S) -> QueryInfo
    where
        S: StoreQueryInfo + ?Sized;

    fn convert(buf: &mut [SelectedRaw]) -> Self::Output<'_>;

    fn key() -> QueryKey {
        QueryKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<QueryInfo>
    where
        S: StoreQueryInfo + ?Sized,
    {
        let key = Self::key();

        if !StoreQueryInfo::contains(stor, &key) {
            let qinfo = Arc::new(Self::info_from(stor));
            StoreQueryInfo::insert(stor, key, qinfo);
        }

        // Safety: Inserted right before.
        unsafe { StoreQueryInfo::get(stor, &key).unwrap_unchecked() }
    }
}

/// [`QueryMut`] is a combination of [`Filter`](super::filter::Filter)s for writable access.
/// For instance, `()`, `FilterA`, and `(FilterA, FilterB)` are sorts of `Query`.
pub trait QueryMut: 'static {
    type Output<'buf>;

    fn info_from<S>(stor: &mut S) -> QueryInfo
    where
        S: StoreQueryInfo + ?Sized;

    fn convert(buf: &mut [SelectedRaw]) -> Self::Output<'_>;

    fn key() -> QueryKey {
        QueryKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<QueryInfo>
    where
        S: StoreQueryInfo + ?Sized,
    {
        let key = Self::key();

        if !StoreQueryInfo::contains(stor, &key) {
            let qinfo = Arc::new(Self::info_from(stor));
            StoreQueryInfo::insert(stor, key, qinfo);
        }

        // Safety: Inserted right before.
        unsafe { StoreQueryInfo::get(stor, &key).unwrap_unchecked() }
    }
}

/// [`ResQuery`] is a combination of [`Resource`](super::resource::Resource)s for read-only access.
/// For instance, `()`, `ResA`, and `(ResA, ResB)` are sorts of `ResQuery`.
pub trait ResQuery: 'static {
    type Output<'buf>;

    fn info() -> ResQueryInfo;

    fn convert(buf: &mut Vec<Borrowed<ManagedConstPtr<u8>>>) -> Self::Output<'_>;

    fn key() -> ResQueryKey {
        ResQueryKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<ResQueryInfo>
    where
        S: StoreResQueryInfo + ?Sized,
    {
        let key = Self::key();

        if !stor.contains(&key) {
            let rqinfo = Arc::new(Self::info());
            stor.insert(key, rqinfo);
        }

        // Safety: Inserted right before.
        unsafe { stor.get(&key).unwrap_unchecked() }
    }
}

/// [`ResQueryMut`] is a combination of [`Resource`](super::resource::Resource)s for writable access.
/// For instance, `()`, `ResA`, and `(ResA, ResB)` are sorts of `ResQueryMut`.
pub trait ResQueryMut: 'static {
    type Output<'buf>;

    fn info() -> ResQueryInfo;

    fn convert(buf: &mut Vec<Borrowed<ManagedMutPtr<u8>>>) -> Self::Output<'_>;

    fn key() -> ResQueryKey {
        ResQueryKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<ResQueryInfo>
    where
        S: StoreResQueryInfo + ?Sized,
    {
        let key = Self::key();

        if !stor.contains(&key) {
            let rqinfo = Arc::new(Self::info());
            stor.insert(key, rqinfo);
        }

        // Safety: Inserted right before.
        unsafe { stor.get(&key).unwrap_unchecked() }
    }
}

/// [`EntQueryMut`] is a combination of [`ContainEntity`](super::entity::ContainEntity)s for writable access.
/// For instance, `()`, `EntA`, and `(EntA, EntB)` are sorts of `EntQueryMut`.
pub trait EntQueryMut: 'static {
    type Output<'buf>;

    fn info() -> EntQueryInfo;

    fn convert(
        buf: &mut Vec<(EntityIndex, Borrowed<NonNull<dyn ContainEntity>>)>,
    ) -> Self::Output<'_>;

    fn key() -> EntQueryKey {
        EntQueryKey::of::<Self>()
    }

    fn get_info_from<S>(stor: &mut S) -> &Arc<EntQueryInfo>
    where
        S: StoreEntQueryInfo + ?Sized,
    {
        let key = Self::key();

        if !stor.contains(&key) {
            let eqinfo = Arc::new(Self::info());
            stor.insert(key, eqinfo);
        }

        // Safety: Inserted right before.
        unsafe { stor.get(&key).unwrap_unchecked() }
    }
}

/// Implements [`Query`] and [`QueryMut`] for a tuple of
/// [`Select`](crate::ecs::sys::select::Select).
#[macro_export]
macro_rules! impl_query {
    ($n:expr, $($i:expr),*) => {const _: () = {
        #[allow(unused_imports)]
        use $crate::ecs::sys::{
            query::{Query, QueryInfo, StoreQueryInfo},
            select::{Select, SelectKey, SelectedRaw, Selected, SelectedMut},
        };
        use std::{any::type_name, sync::Arc};
        use paste::paste;

        // Implements `Query` for (A0, A1, ...).
        paste! {
            #[allow(unused_parens)]
            impl<$([<A $i>]: Select),*> Query for ( $([<A $i>]),* ) {
                type Output<'buf> = ( $(Selected<'buf, [<A $i>]::Target>),* );

                fn info_from<S>(_stor: &mut S) -> QueryInfo
                where
                    S: StoreQueryInfo + ?Sized
                {
                    let name = type_name::<Self>();
                    let sels = [ $(
                        (
                            [<A $i>]::key(),
                            Arc::clone([<A $i>]::get_info_from(_stor))
                        )
                    ),* ];
                    let sels: Box<[(SelectKey, Arc<SelectInfo>)]> = sels.into();
                    QueryInfo { name, sels }
                }

                fn convert(buf: &mut [SelectedRaw]) -> Self::Output<'_> {
                    debug_assert_eq!($n, buf.len());

                    #[allow(clippy::unused_unit)]
                    ( $(
                        // Splitting slice via `split_first_mut` is quite tiresome task.
                        // Anyway, we're connecting lifetime from each input to output,
                        // so no problem.
                        // Safety: Infallible.
                        {
                            let x: *mut SelectedRaw = &mut buf[$i] as *mut _;
                            let x: &mut SelectedRaw = unsafe { x.as_mut().unwrap_unchecked() };
                            Selected::new(x)
                        }
                    ),* )
                }
            }
        }

        // Implements `QueryMut` for (A0, A1, ...).
        paste! {
            #[allow(unused_parens)]
            impl<$([<A $i>]: Select),*> QueryMut for ( $([<A $i>]),* ) {
                type Output<'buf> = ( $(SelectedMut<'buf, [<A $i>]::Target>),* );

                fn info_from<S>(_stor: &mut S) -> QueryInfo
                where
                    S: StoreQueryInfo + ?Sized
                {
                    let name = type_name::<Self>();
                    let sels = [ $(
                        (
                            [<A $i>]::key(),
                            Arc::clone([<A $i>]::get_info_from(_stor))
                        )
                    ),* ];
                    let sels: Box<[(SelectKey, Arc<SelectInfo>)]> = sels.into();

                    QueryInfo { name, sels }
                }

                fn convert(buf: &mut [SelectedRaw]) -> Self::Output<'_> {
                    debug_assert_eq!($n, buf.len());

                    #[allow(clippy::unused_unit)]
                    ( $(
                        // Splitting slice via `split_first_mut` is quite tiresome task.
                        // Anyway, we're connecting lifetime from each input to output,
                        // so no problem.
                        // Safety: Infallible.
                        {
                            let x: *mut SelectedRaw = &mut buf[$i] as *mut _;
                            let x: &mut SelectedRaw = unsafe { x.as_mut().unwrap_unchecked() };
                            SelectedMut::new(x)
                        }
                    ),* )
                }
            }
        }
    };};
}
repeat_macro!(impl_query, ..=8);

/// Implements the trait [`ResQuery`] and [`ResQueryMut`] for an anonymous tuple of [`Resource`](super::resource::Resource)s.
#[macro_export]
macro_rules! impl_res_query {
    ($n:expr, $($i:expr),*) => {const _: () = {
        #[allow(unused_imports)]
        use $crate::{
            ecs::{
                sys::query::{ResQuery, ResQueryInfo},
                resource::Resource,
            },
            ds::{borrow::Borrowed, ptr::{ManagedConstPtr, ManagedMutPtr}},
        };
        use std::any::type_name;
        use paste::paste;

        // Implements `ResQuery` for (A0, A1, ...).
        paste! {
            #[allow(unused_parens)]
            impl<$([<A $i>]: Resource),*> ResQuery for ( $([<A $i>]),* ) {
                type Output<'buf> = ( $( &'buf [<A $i>] ),* );

                fn info() -> ResQueryInfo {
                    ResQueryInfo {
                        name: type_name::<Self>(),
                        rkeys: [$([<A $i>]::key()),*].into(),
                    }
                }

                fn convert(_buf: &mut Vec<Borrowed<ManagedConstPtr<u8>>>) -> Self::Output<'_> {
                    debug_assert_eq!($n, _buf.len());

                    // Managed pointer may have type info in it.
                    // But resource pointer must have the type info.
                    // So we can check if the pointers are correctly given.
                    #[cfg(feature = "check")]
                    {
                        $(
                            let ptr: NonNullExt<_> = _buf[$i].inner();
                            let lhs: &TypeIdExt = ptr.get_type().unwrap();

                            let rkey: ResourceKey = [<A $i>]::key();
                            let rhs: &TypeIdExt = rkey.get_inner();

                            assert_eq!(lhs, rhs);
                        )*
                    }

                    #[allow(clippy::unused_unit)]
                    ( $(
                        _buf[$i].map_ref(|ptr| {
                            let ptr: NonNullExt<[<A $i>]> = ptr.inner().cast();
                            unsafe { ptr.as_ref() }
                        })
                    ),* )
                }
            }
        }

        // Implements `ResQueryMut` for (A0, A1, ...).
        paste!{
            #[allow(unused_parens)]
            impl<$([<A $i>]: Resource),*> ResQueryMut for ( $([<A $i>]),* ) {
                type Output<'buf> = ( $( &'buf mut [<A $i>] ),* );

                fn info() -> ResQueryInfo {
                    ResQueryInfo {
                        name: type_name::<Self>(),
                        rkeys: [$([<A $i>]::key()),*].into(),
                    }
                }

                fn convert(_buf: &mut Vec<Borrowed<ManagedMutPtr<u8>>>) -> Self::Output<'_> {
                    debug_assert_eq!($n, _buf.len());

                    // Managed pointer may have type info in it.
                    // But resource pointer must have the type info.
                    // So we can check if the pointers are correctly given.
                    #[cfg(feature = "check")]
                    {
                        $(
                            let ptr: NonNullExt<_> = _buf[$i].inner();
                            let lhs: &TypeIdExt = ptr.get_type().unwrap();

                            let rkey: ResourceKey = [<A $i>]::key();
                            let rhs: &TypeIdExt = rkey.get_inner();

                            assert_eq!(lhs, rhs);
                        )*
                    }

                    #[allow(clippy::unused_unit)]
                    ( $(
                        // Splitting slice via `split_first_mut` is quite tiresome task.
                        // Anyway, we're connecting lifetime from each input to output,
                        // so no problem.
                        // Safety: Infallible.
                        {
                            let x: *mut Borrowed<ManagedMutPtr<u8>>
                                = &mut _buf[$i] as *mut _;
                            let x: &mut Borrowed<ManagedMutPtr<u8>>
                                = unsafe { x.as_mut().unwrap_unchecked() };
                            x.map_mut(|ptr| {
                                let mut ptr: NonNullExt<[<A $i>]> = ptr.inner().cast();
                                unsafe { ptr.as_mut() }
                            })
                        }
                    ),* )
                }
            }
        }
    };};
}
repeat_macro!(impl_res_query, ..=8);

/// Implements the trait [`EntQueryMut`] for an anonymous tuple of [`ContainEntity`](super::entity::ContainEntity)s.
#[macro_export]
macro_rules! impl_ent_query {
    ($n:expr, $($i:expr),*) => {const _: () = {
        #[allow(unused_imports)]
        use $crate::{
            ecs::{
                sys::query::{EntQueryMut, EntQueryInfo},
                ent::{
                    entity::{Entity, ContainEntity},
                    storage::TypedEntityContainer},
            },
            ds::borrow::Borrowed,
        };
        use std::any::type_name;
        use paste::paste;

        // Implements `EntQueryMut` for (A0, A1, ...).
        paste!{
            #[allow(unused_parens)]
            impl<$([<A $i>]: Entity),*> EntQueryMut for ( $([<A $i>]),* ) {
                type Output<'buf> = ( $(TypedEntityContainer<'buf, [<A $i>]>),* );

                fn info() -> EntQueryInfo {
                    EntQueryInfo {
                        name: type_name::<Self>(),
                        ekeys: [$([<A $i>]::key()),*].into(),
                    }
                }

                fn convert(
                    buf: &mut Vec<(EntityIndex, Borrowed<NonNull<dyn ContainEntity>>)>,
                ) -> Self::Output<'_> {
                    debug_assert_eq!($n, buf.len());

                    // clippy warns about possibility that users of the macro
                    // could write unsafe code without usafe block due to '$i'
                    // which is given by users and is in unsafe block. But
                    // 'buf[$i]' is safe code.
                    #[allow(clippy::macro_metavars_in_unsafe)]
                    let res = ( $(
                        unsafe {
                            let (ei, buf) = &buf[$i];
                            TypedEntityContainer::new(*ei, **buf)
                        }
                    ),* );

                    res
                }
            }
        }
    };};
}
repeat_macro!(impl_ent_query, ..=8);
