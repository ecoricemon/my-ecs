use crate::{ds::prelude::*, ecs::EcsError, util::prelude::*};
use std::{
    any::Any,
    collections::HashMap,
    hash::{BuildHasher, Hash},
    ptr::NonNull,
};

/// There are two types of resources.
/// First one is static resource which is defined internally.
/// The other one is user resource which is defined by users.
/// This struct has pointers to those resources and dosen't update it once it's set.
/// Because, resource is a kind of unique data storage, so it makes sense.
#[derive(Debug)]
pub(super) struct ResourceStorage<S> {
    /// Owned resources.
    owned: HashMap<ResourceKey, Box<dyn Any>, S>,

    /// Raw pointers to resources.
    /// Pointers to owned resources are guaranteed to be valid by the struct.
    /// Other pointers must be kept to be valid by client code.
    /// They must be well aligned, not aliased, and alive.
    ptrs: OptVec<SimpleHolder<NonNullExt<u8>>, S>,

    /// [`ResourceKey`] -> index in `Self::ptrs`.
    imap: HashMap<ResourceKey, usize, S>,

    /// Dedicated resources, which are not allowed to be sent to other workers.
    /// So they must be handled by main worker.
    /// For example, in web environment, we must send JS objects through postMessage().
    /// That means objects that are not posted can't be accessed from other workers.
    /// Plus, ecs objects will be dedicated resource in most cases.
    is_dedi: Vec<bool>,
}

impl<S> ResourceStorage<S>
where
    S: Default,
{
    pub(super) fn new() -> Self {
        Self {
            owned: HashMap::default(),
            ptrs: OptVec::new(),
            imap: HashMap::default(),
            is_dedi: Vec::new(),
        }
    }
}

impl<S> ResourceStorage<S>
where
    S: BuildHasher + Default,
{
    /// Registers the resource.
    /// If the registration succeeded, returns its resource index.
    /// Otherwise, nothing takes place and returns received value.
    /// In other words, the old resouce data won't be dropped.
    pub(super) fn register(&mut self, desc: ResourceDesc) -> Result<usize, EcsError<ResourceDesc>> {
        if self.imap.contains_key(&desc.key) {
            let reason = debug_format!("detected duplicated resource `{:?}`", desc.key);
            return Err(EcsError::DupResource(reason, desc));
        }

        let ResourceDesc {
            dedicated,
            key,
            data,
        } = desc;

        let ptr = match data {
            Or::A(mut owned) => {
                // Safety: Infallible.
                let ptr = unsafe { NonNull::new_unchecked(&mut *owned as *mut dyn Any as *mut u8) };
                let must_none = self.owned.insert(key, owned);
                debug_assert!(must_none.is_none());
                ptr
            }
            Or::B(ptr) => ptr,
        };

        // Attaches ResourceKey's type info to the pointer for debug.
        let ptr = NonNullExt::from_nonnull(ptr).with_type(*key.get_inner());

        // Adds the pointer.
        let holder = SimpleHolder::new(ptr);
        let index = self.ptrs.add(holder);

        // Adds the index to the pointer list.
        self.imap.insert(key, index);

        // Adds dedicated mapping.
        if self.is_dedi.len() < index + 1 {
            self.is_dedi.resize(index + 1, false);
        }
        self.is_dedi[index] = dedicated;

        Ok(index)
    }

    pub(super) fn unregister(
        &mut self,
        rkey: &ResourceKey,
    ) -> Option<Or<Box<dyn Any>, NonNull<u8>>> {
        // Removes the resource from `self.owned`, `self.ptrs`, and `self.imap`.
        // But we don't have to remove `self.is_dedi`.
        if let Some(i) = self.imap.remove(rkey) {
            let data = self.owned.remove(rkey);
            let ptr = self.ptrs.take(i);

            // Safety: Pointer must exist.
            debug_assert!(ptr.is_some());
            let holder = unsafe { ptr.unwrap_unchecked() };
            let ptr = *holder.into_value();

            Some(if let Some(data) = data {
                Or::A(data)
            } else {
                Or::B(ptr)
            })
        } else {
            None
        }
    }

    pub(super) fn contains<Q>(&self, key: &Q) -> bool
    where
        ResourceKey: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.imap.contains_key(key)
    }

    pub(super) fn index<Q>(&self, key: &Q) -> Option<usize>
    where
        ResourceKey: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.imap.get(key).cloned()
    }

    pub(super) fn is_dedicated(&self, index: usize) -> bool {
        self.is_dedi[index]
    }

    pub(super) fn is_dedicated2<Q>(&self, key: &Q) -> bool
    where
        ResourceKey: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(index) = self.imap.get(key) {
            self.is_dedicated(*index)
        } else {
            false
        }
    }

    pub(super) fn borrow(&self, index: usize) -> BorrowResult<ManagedConstPtr<u8>> {
        if let Some(holder) = self.ptrs.get(index) {
            holder
                .borrow()
                .map(|borrowed| borrowed.map(|ptr| unsafe { ManagedConstPtr::new(ptr) }))
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    // For consistency
    #[allow(dead_code)]
    pub(super) fn borrow2<Q>(&self, key: &Q) -> BorrowResult<ManagedConstPtr<u8>>
    where
        ResourceKey: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(index) = self.index(key) {
            self.borrow(index)
        } else {
            Err(BorrowError::NotFound)
        }
    }

    pub(super) fn borrow_mut(&mut self, index: usize) -> BorrowResult<ManagedMutPtr<u8>> {
        if let Some(holder) = self.ptrs.get_mut(index) {
            holder
                .borrow_mut()
                .map(|borrowed| borrowed.map(|ptr| unsafe { ManagedMutPtr::new(ptr) }))
        } else {
            Err(BorrowError::OutOfBound)
        }
    }

    // For consistency
    #[allow(dead_code)]
    pub(super) fn borrow_mut2<Q>(&mut self, key: &Q) -> BorrowResult<ManagedMutPtr<u8>>
    where
        ResourceKey: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(index) = self.index(key) {
            self.borrow_mut(index)
        } else {
            Err(BorrowError::NotFound)
        }
    }

    /// # Safety
    ///
    /// Undefine behavior if exclusive borrow happend before.
    //
    // Allows dead_code for test.
    #[allow(dead_code)]
    pub(super) unsafe fn get_ptr(&self, index: usize) -> Option<NonNullExt<u8>> {
        self.ptrs.get(index).map(|holder| *holder.get_unchecked())
    }
}

impl<S> Default for ResourceStorage<S>
where
    S: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct ResourceDesc {
    pub dedicated: bool,
    pub(crate) key: ResourceKey,
    pub data: Or<Box<dyn Any>, NonNull<u8>>,
}

impl ResourceDesc {
    pub fn new() -> Self {
        Self {
            dedicated: false,
            key: EmptyResource::key(),
            data: Or::B(NonNull::dangling()),
        }
    }

    pub fn with_dedicated(mut self, is_dedicated: bool) -> Self {
        self.dedicated = is_dedicated;
        self
    }

    pub fn with_owned<R: Resource>(mut self, data: R) -> Self {
        self.key = R::key();
        self.data = Or::A(Box::new(data));
        self
    }

    /// # Safety
    ///
    /// If caller registered the resource to ecs and accesses memory at the data
    /// address while ecs is working, it's undefined behavior.
    pub unsafe fn with_ptr<R: Resource>(mut self, data: *mut R) -> Self {
        self.key = R::key();
        self.data = Or::B(NonNull::new(data as *mut u8).unwrap());
        self
    }
}

impl Default for ResourceDesc {
    fn default() -> Self {
        Self::new()
    }
}

/// Unique data over entire application.
#[allow(private_interfaces)]
pub trait Resource: Send + 'static {
    #[doc(hidden)]
    fn key() -> ResourceKey {
        ResourceKey::of::<Self>()
    }
}

/// Empty resource.
struct EmptyResource;
impl Resource for EmptyResource {}

/// Unique identifier for a type implementing [`Resource`].
pub(crate) type ResourceKey = ATypeId<ResourceKey_>;
pub(crate) struct ResourceKey_;
