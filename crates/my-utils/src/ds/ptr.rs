use super::types::TypeIdExt;
use std::{
    cmp, fmt, hash,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// A pointer that implements [`Send`] and [`Sync`] regardless of whether `T` implements both
/// [`Send`] and [`Sync`].
///
/// # Safety
///
/// This pointer can be sent to another worker. Owner must guarantee that sending the pointer is
/// safe. For instance, if you are controlling access to pointer over workers completely, it will be
/// safe in terms of `Send` and `Sync`.
#[derive(Debug)]
#[repr(transparent)]
pub struct SendSyncPtr<T: ?Sized>(NonNull<T>);

unsafe impl<T: ?Sized> Send for SendSyncPtr<T> {}
unsafe impl<T: ?Sized> Sync for SendSyncPtr<T> {}

impl<T: ?Sized> SendSyncPtr<T> {
    /// Creates a [`SendSyncPtr`] by wrapping the given pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let ptr = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = SendSyncPtr::new(ptr);
    /// ```
    #[inline]
    pub const fn new(ptr: NonNull<T>) -> Self {
        Self(ptr)
    }

    /// Creates a [`SendSyncPtr`] that is dangling, but well-aligned.
    ///
    /// In many Rust functions, they require aligned pointers even if they are some trash values.
    /// This function will be usuful in that cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let dangling = SendSyncPtr::<i32>::dangling();
    /// ```
    #[inline]
    pub const fn dangling() -> Self
    where
        T: Sized,
    {
        Self::new(NonNull::dangling())
    }

    /// Returns true if the pointer is dangling.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    ///
    /// let dangling = SendSyncPtr::<i32>::dangling();
    /// assert!(dangling.is_dangling());
    /// ```
    #[inline]
    pub fn is_dangling(&self) -> bool
    where
        T: Sized,
    {
        self == &Self::dangling()
    }

    /// Creates a [`NonNull`] from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let nn = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = SendSyncPtr::new(nn);
    /// assert_eq!(ptr.as_nonnull(), nn);
    /// ```
    #[inline]
    pub const fn as_nonnull(self) -> NonNull<T> {
        self.0
    }

    /// Creates a raw pointer from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let nn = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = SendSyncPtr::new(nn);
    /// assert_eq!(ptr.as_ptr(), nn.as_ptr());
    /// ```
    #[inline]
    pub const fn as_ptr(self) -> *mut T {
        self.0.as_ptr()
    }

    /// Returns a shared reference to the value.
    ///
    /// # Safety
    ///
    /// See [`NonNull::as_ref`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let ptr = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = SendSyncPtr::new(ptr);
    /// let ref_v = unsafe { ptr.as_ref() };
    /// assert_eq!(ref_v, &v);
    /// ```
    #[inline]
    pub unsafe fn as_ref<'a>(&self) -> &'a T {
        unsafe { self.0.as_ref() }
    }

    /// Returns a mutable reference to the value.
    ///
    /// # Safety
    ///
    /// See [`NonNull::as_mut`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let ptr = NonNull::new(&mut v as *mut i32).unwrap();
    /// let mut ptr = SendSyncPtr::new(ptr);
    /// let mut_v = unsafe { ptr.as_mut() };
    /// ```
    #[inline]
    pub unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        unsafe { self.0.as_mut() }
    }

    /// Adds an offset to the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::add`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    /// let ptr = NonNull::new(arr.as_ptr().cast_mut()).unwrap();
    /// let ptr = SendSyncPtr::new(ptr);
    ///
    /// let ref_v = unsafe { ptr.add(1).as_ref() };
    /// assert_eq!(ref_v, &'b');
    ///
    /// let ref_v = unsafe { ptr.add(2).as_ref() };
    /// assert_eq!(ref_v, &'c');
    /// ```
    #[inline]
    pub const unsafe fn add(self, count: usize) -> Self
    where
        T: Sized,
    {
        let inner = unsafe {
            let ptr = self.0.as_ptr().add(count);
            NonNull::new_unchecked(ptr)
        };
        Self::new(inner)
    }

    /// Subtracts an offset from the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::sub`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    ///
    /// let ptr = NonNull::new(arr.as_ptr_range().end.cast_mut()).unwrap();
    /// let ptr = SendSyncPtr::new(ptr);
    ///
    /// unsafe {
    ///     let r = ptr.sub(1).as_ref();
    ///     assert_eq!(r, &'c');
    ///     let r = ptr.sub(2).as_ref();
    ///     assert_eq!(r, &'b');
    /// }
    /// ```
    #[inline]
    pub const unsafe fn sub(self, count: usize) -> Self
    where
        T: Sized,
    {
        let inner = unsafe {
            let ptr = self.0.as_ptr().sub(count);
            NonNull::new_unchecked(ptr)
        };
        Self::new(inner)
    }

    /// Casts the pointer to another type.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::SendSyncPtr;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0x1234_5678;
    /// let ptr = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = SendSyncPtr::new(ptr);
    ///
    /// let ptr = ptr.cast::<[u8; 4]>();
    /// let ref_v = unsafe { ptr.as_ref() };
    /// assert_eq!(*ref_v, i32::to_ne_bytes(v));
    /// ```
    #[inline]
    pub const fn cast<U>(self) -> SendSyncPtr<U> {
        // Safety: Nothing has changed except `T` -> `U`.
        SendSyncPtr::new(self.0.cast())
    }
}

/// Comparison by address
impl<T: ?Sized> PartialEq for SendSyncPtr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr().cast::<()>().eq(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> Eq for SendSyncPtr<T> {}

impl<T: ?Sized> PartialOrd for SendSyncPtr<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Comparison by address
impl<T: ?Sized> Ord for SendSyncPtr<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ptr().cast::<()>().cmp(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> hash::Hash for SendSyncPtr<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T: ?Sized> Clone for SendSyncPtr<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for SendSyncPtr<T> {}

/// A pointer that is extended with type id or name.
///
/// If 'check' feature is enabled, it contains type id or name. Otherwise, it's just a [`NonNull`].
/// This is useful when you want to know the type of the pointer.
#[cfg_attr(not(feature = "check"), repr(transparent))]
pub struct NonNullExt<T: ?Sized> {
    inner: NonNull<T>,
    #[cfg(feature = "check")]
    ty_or_name: crate::Or<TypeIdExt, &'static str>,
}

impl<T: ?Sized> NonNullExt<T> {
    /// Creates a [`NonNullExt`] from the given pointer.
    ///
    /// Returns `None` if the pointer is null.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// ```
    #[inline]
    pub fn new(ptr: *mut T) -> Option<Self> {
        let ptr = NonNull::new(ptr)?;
        Some(Self::from_nonnull(ptr))
    }

    /// Creates a [`NonNullExt`] from the given pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be non-null.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let mut v = 0;
    /// let ptr = unsafe { NonNullExt::new_unchecked(&mut v as *mut i32) };
    /// ```
    #[inline]
    pub unsafe fn new_unchecked(ptr: *mut T) -> Self {
        debug_assert!(
            !ptr.is_null(),
            "NonNullExt::new_unchecked: expected non-null pointer"
        );

        Self {
            inner: unsafe { NonNull::new_unchecked(ptr) },
            #[cfg(feature = "check")]
            ty_or_name: crate::Or::B(std::any::type_name::<T>()),
        }
    }

    /// Creates a [`NonNullExt`] from the given pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    /// use std::ptr::NonNull;
    ///
    /// let mut v = 0;
    /// let ptr = NonNull::new(&mut v as *mut i32).unwrap();
    /// let ptr = NonNullExt::from_nonnull(ptr);
    /// ```
    #[inline]
    pub fn from_nonnull(ptr: NonNull<T>) -> Self {
        Self {
            inner: ptr,
            #[cfg(feature = "check")]
            ty_or_name: crate::Or::B(std::any::type_name::<T>()),
        }
    }

    /// Creates a [`NonNullExt`] that is dangling, but well-aligned.
    ///
    /// In many Rust functions, they require aligned pointers even if they are some trash values.
    /// This function will be usuful in that cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let dangling = NonNullExt::<i32>::dangling();
    /// ```
    #[inline]
    pub const fn dangling() -> Self
    where
        T: Sized,
    {
        Self {
            inner: NonNull::dangling(),
            #[cfg(feature = "check")]
            ty_or_name: crate::Or::B(""), // type_name() is not const yet.
        }
    }

    /// Returns true if the pointer is dangling.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let dangling = NonNullExt::<i32>::dangling();
    /// assert!(dangling.is_dangling());
    /// ```
    #[inline]
    pub fn is_dangling(&self) -> bool
    where
        T: Sized,
    {
        self == &Self::dangling()
    }

    /// Sets the [`TypeIdExt`] to the pointer then returns the pointer.
    ///
    /// Basically, [`NonNullExt`] contains type name of the pointer if `check` feature is enabled.
    /// You can replace it with the given `TypeIdExt` using this method. But `check` feature is
    /// disabled, this method is no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, TypeIdExt};
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32)
    ///     .unwrap()
    ///     .with_type(TypeIdExt::of::<i32>());
    /// ```
    #[inline]
    pub fn with_type(self, _ty: TypeIdExt) -> Self {
        #[cfg(not(feature = "check"))]
        {
            self
        }

        #[cfg(feature = "check")]
        {
            let mut this = self;
            this.ty_or_name = crate::Or::A(_ty);
            this
        }
    }

    /// Returns [`TypeIdExt`] of the pointer if `check` feature is enabled and the pointer contains
    /// `TypeIdExt` rather than type name.
    ///
    /// If you want to set the `TypeIdExt` to the pointer, call [`NonNullExt::with_type`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, TypeIdExt};
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32)
    ///     .unwrap()
    ///     .with_type(TypeIdExt::of::<i32>());
    /// ```
    #[inline]
    pub fn get_type(&self) -> Option<&TypeIdExt> {
        #[cfg(not(feature = "check"))]
        {
            None
        }

        #[cfg(feature = "check")]
        {
            match &self.ty_or_name {
                crate::Or::A(ty) => Some(ty),
                crate::Or::B(_name) => None,
            }
        }
    }

    /// Returns type name of the pointer if `check` feature is enabled.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let name = ptr.get_name();
    /// ```
    #[inline]
    pub fn get_name(&self) -> Option<&'static str> {
        #[cfg(not(feature = "check"))]
        {
            None
        }

        #[cfg(feature = "check")]
        {
            match &self.ty_or_name {
                crate::Or::A(ty) => Some(ty.name()),
                crate::Or::B(name) => Some(name),
            }
        }
    }

    /// Casts the pointer to another type.
    ///
    /// Note that this method resets [`TypeIdExt`] you set through [`NonNullExt::with_type`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let mut v = 0x1234_5678;
    /// let ptr = NonNullExt::new(&mut v as *mut i32).unwrap();
    ///
    /// let ptr = ptr.cast::<[u8; 4]>();
    /// let ref_v = unsafe { ptr.as_ref() };
    /// assert_eq!(*ref_v, i32::to_ne_bytes(v));
    /// ```
    #[inline]
    pub fn cast<U>(self) -> NonNullExt<U> {
        NonNullExt {
            inner: self.inner.cast(),
            #[cfg(feature = "check")]
            ty_or_name: crate::Or::B(std::any::type_name::<U>()),
        }
    }

    /// Adds an offset to the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::add`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    /// let ptr = NonNullExt::new(arr.as_ptr().cast_mut()).unwrap();
    ///
    /// let ref_v = unsafe { ptr.add(1).as_ref() };
    /// assert_eq!(ref_v, &'b');
    ///
    /// let ref_v = unsafe { ptr.add(2).as_ref() };
    /// assert_eq!(ref_v, &'c');
    /// ```
    #[inline]
    pub unsafe fn add(self, count: usize) -> Self
    where
        T: Sized,
    {
        let inner = unsafe {
            let ptr = self.inner.as_ptr().add(count);
            NonNull::new_unchecked(ptr)
        };

        Self {
            inner,
            #[cfg(feature = "check")]
            ty_or_name: self.ty_or_name,
        }
    }

    /// Subtracts an offset from the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::sub`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::NonNullExt;
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    /// let ptr = NonNullExt::new(arr.as_ptr_range().end.cast_mut()).unwrap();
    ///
    /// unsafe {
    ///     let r = ptr.sub(1).as_ref();
    ///     assert_eq!(r, &'c');
    ///     let r = ptr.sub(2).as_ref();
    ///     assert_eq!(r, &'b');
    /// }
    /// ```
    #[inline]
    pub unsafe fn sub(self, count: usize) -> Self
    where
        T: Sized,
    {
        let inner = unsafe {
            let ptr = self.inner.as_ptr().sub(count);
            NonNull::new_unchecked(ptr)
        };

        Self {
            inner,
            #[cfg(feature = "check")]
            ty_or_name: self.ty_or_name,
        }
    }
}

impl<T: ?Sized> Deref for NonNullExt<T> {
    type Target = NonNull<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: ?Sized> DerefMut for NonNullExt<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: ?Sized> Clone for NonNullExt<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for NonNullExt<T> {}

/// Comparison by address
impl<T: ?Sized> PartialEq for NonNullExt<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr().cast::<()>().eq(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> Eq for NonNullExt<T> {}

impl<T: ?Sized> PartialOrd for NonNullExt<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Comparison by address
impl<T: ?Sized> Ord for NonNullExt<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ptr().cast::<()>().cmp(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> hash::Hash for NonNullExt<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T: ?Sized> fmt::Debug for NonNullExt<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(not(feature = "check"))]
        {
            self.inner.fmt(f)
        }

        #[cfg(feature = "check")]
        {
            write!(f, "NonNullExt({:?})", self.ty_or_name)
        }
    }
}

/// A wrapper of [`NonNullExt`] that can be used to manage a constant pointer.
///
/// When the `check` feature is enabled, the crate tracks whether [`ManagedMutPtr`] that has the
/// same address is being created while the pointer is alive. This could be useful when you need
/// extra debugging facility than `NonNullExt`.
///
/// # Safety
///
/// The pointer is used as a shared reference without unsafe function such as [`NonNull::as_ref`]
/// because the pointer is completely managed. Therefore, You must make sure that the pointer will
/// not violate any conditions of `Pointer to reference conversion` in [`std::ptr`] document.
pub struct ManagedConstPtr<T: ?Sized> {
    inner: NonNullExt<T>,

    #[cfg(feature = "check")]
    is_track: bool,
}

unsafe impl<T: ?Sized + Send> Send for ManagedConstPtr<T> {}

impl<T: ?Sized> ManagedConstPtr<T> {
    /// Creates a [`ManagedConstPtr`] from the given pointer.
    ///
    /// # Safety
    ///
    /// See [`ManagedConstPtr`] safety section.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(ptr) };
    /// ```
    #[inline]
    pub unsafe fn new(ptr: NonNullExt<T>) -> Self {
        Self::_new(
            ptr,
            #[cfg(feature = "check")]
            true,
        )
    }

    #[inline]
    fn _new(inner: NonNullExt<T>, #[cfg(feature = "check")] is_track: bool) -> Self {
        #[cfg(feature = "check")]
        if is_track {
            debug::insert_const_ptr(inner);
        }

        Self {
            inner,
            #[cfg(feature = "check")]
            is_track,
        }
    }

    /// Creates a [`ManagedConstPtr`] that is dangling, but well-aligned.
    ///
    /// In many Rust functions, they require aligned pointers even if they are some trash values.
    /// This function will be usuful in that cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::ManagedConstPtr;
    ///
    /// let dangling = ManagedConstPtr::<i32>::dangling();
    /// ```
    #[inline]
    pub const fn dangling() -> Self
    where
        T: Sized,
    {
        Self {
            inner: NonNullExt::dangling(),

            #[cfg(feature = "check")]
            is_track: false,
        }
    }

    /// Returns true if the pointer is dangling.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::ManagedConstPtr;
    ///
    /// let dangling = ManagedConstPtr::<i32>::dangling();
    /// assert!(dangling.is_dangling());
    /// ```
    #[inline]
    pub fn is_dangling(&self) -> bool
    where
        T: Sized,
    {
        self == &Self::dangling()
    }

    /// Creates a [`NonNullExt`] from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(nne) };
    /// assert_eq!(ptr.as_nonnullext(), nne);
    /// ```
    #[inline]
    pub fn as_nonnullext(&self) -> NonNullExt<T> {
        self.inner
    }

    /// Creates a [`NonNull`] from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(nne) };
    /// assert_eq!(ptr.as_nonnull(), *nne);
    /// ```
    #[inline]
    pub fn as_nonnull(&self) -> NonNull<T> {
        self.inner.inner
    }

    /// Creates a raw poitner from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(nne) };
    /// assert_eq!(ptr.as_ptr(), nne.as_ptr());
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.inner.as_ptr().cast_const()
    }

    /// Converts the pointer into a shared reference.
    ///
    /// Note that trace of the address by `check` feature ends by consuming the pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(nne) };
    /// assert_eq!(ptr.into_ref(), &0);
    /// ```
    #[inline]
    pub fn into_ref<'a>(self) -> &'a T {
        let inner = self.inner;

        #[cfg(feature = "check")]
        drop(self);

        // Safety: Managed pointer.
        unsafe { inner.as_ref() }
    }

    /// Casts the pointer to another type.
    ///
    /// This method doesn't break the trace of the address by `check` feature. But internal type
    /// information is reset. See [`NonNullExt::cast`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let mut v = 0x1234_5678;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedConstPtr::new(nne) };
    ///
    /// let ptr = ptr.cast::<[u8; 4]>();
    /// let ref_v = ptr.into_ref();
    /// assert_eq!(*ref_v, i32::to_ne_bytes(v));
    /// ```
    #[inline]
    pub fn cast<U>(self) -> ManagedConstPtr<U> {
        #[cfg(not(feature = "check"))]
        {
            ManagedConstPtr {
                inner: self.inner.cast(),
            }
        }

        #[cfg(feature = "check")]
        {
            let inner = self.inner.cast();
            let is_track = self.is_track;

            drop(self);

            ManagedConstPtr::_new(inner, is_track)
        }
    }

    /// Adds an offset to the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::add`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    /// let ptr = NonNullExt::new(arr.as_ptr().cast_mut()).unwrap();
    ///
    /// unsafe {
    ///     let ptr = ManagedConstPtr::new(ptr);
    ///     assert_eq!(*ptr.add(2), 'c');
    /// }
    /// ```
    #[inline]
    pub unsafe fn add(&self, count: usize) -> Self
    where
        T: Sized,
    {
        Self::_new(
            self.inner.add(count),
            #[cfg(feature = "check")]
            self.is_track,
        )
    }

    /// Subtracts an offset from the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::sub`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedConstPtr};
    ///
    /// let arr: [char; 3] = ['a', 'b', 'c'];
    /// let ptr = NonNullExt::new(arr.as_ptr_range().end.cast_mut()).unwrap();
    ///
    /// unsafe {
    ///     let ptr = ManagedConstPtr::new(ptr);
    ///     assert_eq!(*ptr.sub(2), 'b');
    /// }
    /// ```
    #[inline]
    pub unsafe fn sub(&self, count: usize) -> Self
    where
        T: Sized,
    {
        Self::_new(
            self.inner.sub(count),
            #[cfg(feature = "check")]
            self.is_track,
        )
    }
}

impl<T: ?Sized> Drop for ManagedConstPtr<T> {
    fn drop(&mut self) {
        #[cfg(feature = "check")]
        if self.is_track {
            debug::remove_ptr(*self.inner);
        }
    }
}

impl<T: ?Sized> Deref for ManagedConstPtr<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: We assume that the pointer is valid by the constructor.
        unsafe { self.inner.as_ref() }
    }
}

impl<T: ?Sized> Clone for ManagedConstPtr<T> {
    fn clone(&self) -> Self {
        Self::_new(
            self.inner,
            #[cfg(feature = "check")]
            self.is_track,
        )
    }
}

/// Comparison by address
impl<T: ?Sized> PartialEq for ManagedConstPtr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr().cast::<()>().eq(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> Eq for ManagedConstPtr<T> {}

impl<T: ?Sized> PartialOrd for ManagedConstPtr<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Comparison by address
impl<T: ?Sized> Ord for ManagedConstPtr<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ptr().cast::<()>().cmp(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> hash::Hash for ManagedConstPtr<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T: ?Sized> fmt::Debug for ManagedConstPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// A wrapper of [`NonNullExt`] that can be used to manage a mutable pointer.
///
/// When the `check` feature is enabled, the crate tracks whether [`ManagedMutPtr`] or
/// [`ManagedConstPtr`] that has the same address is being created while the pointer is alive. This
/// could be useful when you need extra debugging facility than `NonNullExt`.
///
/// # Safety
///
/// The pointer is used as a mutable reference without unsafe function such as [`NonNull::as_mut`]
/// because the pointer is completely managed. Therefore, You must make sure that the pointer will
/// not violate any conditions of `Pointer to reference conversion` in [`std::ptr`] document.
pub struct ManagedMutPtr<T: ?Sized> {
    inner: NonNullExt<T>,

    #[cfg(feature = "check")]
    is_track: bool,
}

unsafe impl<T: ?Sized + Send> Send for ManagedMutPtr<T> {}

impl<T: ?Sized> ManagedMutPtr<T> {
    /// Creates a [`ManagedMutPtr`] from the given pointer.
    ///
    /// # Safety
    ///
    /// See [`ManagedMutPtr`] safety section.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let ptr = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(ptr) };
    /// ```
    #[inline]
    pub unsafe fn new(ptr: NonNullExt<T>) -> Self {
        Self::_new(
            ptr,
            #[cfg(feature = "check")]
            true,
        )
    }

    #[inline]
    fn _new(inner: NonNullExt<T>, #[cfg(feature = "check")] is_track: bool) -> Self {
        #[cfg(feature = "check")]
        if is_track {
            debug::insert_mut_ptr(inner);
        }

        Self {
            inner,
            #[cfg(feature = "check")]
            is_track,
        }
    }

    /// Creates a [`ManagedMutPtr`] that is dangling, but well-aligned.
    ///
    /// In many Rust functions, they require aligned pointers even if they are some trash values.
    /// This function will be usuful in that cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::ManagedMutPtr;
    ///
    /// let dangling = ManagedMutPtr::<i32>::dangling();
    /// ```
    #[inline]
    pub const fn dangling() -> Self
    where
        T: Sized,
    {
        Self {
            inner: NonNullExt::dangling(),
            #[cfg(feature = "check")]
            is_track: false,
        }
    }

    /// Returns true if the pointer is dangling.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::ManagedMutPtr;
    ///
    /// let dangling = ManagedMutPtr::<i32>::dangling();
    /// assert!(dangling.is_dangling());
    /// ```
    #[inline]
    pub fn is_dangling(&self) -> bool
    where
        T: Sized,
    {
        self == &Self::dangling()
    }

    /// Creates a [`NonNullExt`] from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// assert_eq!(ptr.as_nonnullext(), nne);
    /// ```
    #[inline]
    pub fn as_nonnullext(&self) -> NonNullExt<T> {
        self.inner
    }

    /// Creates a [`NonNull`] from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// assert_eq!(ptr.as_nonnull(), *nne);
    /// ```
    #[inline]
    pub fn as_nonnull(&self) -> NonNull<T> {
        self.inner.inner
    }

    /// Creates a raw poitner from this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// assert_eq!(ptr.as_ptr(), nne.as_ptr());
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        self.inner.as_ptr()
    }

    /// Converts the pointer into a mutable reference.
    ///
    /// Note that trace of the address by `check` feature ends by consuming the pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// assert_eq!(ptr.into_mut(), &0);
    /// ```
    #[inline]
    pub fn into_mut<'a>(self) -> &'a mut T {
        let mut inner = self.inner;

        #[cfg(feature = "check")]
        drop(self);

        // Safety: Managed pointer.
        unsafe { inner.as_mut() }
    }

    /// Casts the pointer to another type.
    ///
    /// This method doesn't break the trace of the address by `check` feature. But internal type
    /// information is reset. See [`NonNullExt::cast`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0x1234_5678;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    ///
    /// let ptr = ptr.cast::<[u8; 4]>();
    /// let ref_v = ptr.into_mut();
    /// assert_eq!(*ref_v, i32::to_ne_bytes(v));
    /// ```
    #[inline]
    pub fn cast<U>(self) -> ManagedMutPtr<U> {
        #[cfg(not(feature = "check"))]
        {
            ManagedMutPtr {
                inner: self.inner.cast(),
            }
        }

        #[cfg(feature = "check")]
        {
            let inner = self.inner.cast();
            let is_track = self.is_track;

            drop(self);

            ManagedMutPtr::_new(inner, is_track)
        }
    }

    /// Changes constness without changing the type.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let mut v = 0;
    /// let nne = NonNullExt::new(&mut v as *mut i32).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// let ptr = ptr.cast_const();
    /// ```
    #[inline]
    pub fn cast_const(self) -> ManagedConstPtr<T> {
        #[cfg(not(feature = "check"))]
        {
            ManagedConstPtr { inner: self.inner }
        }

        #[cfg(feature = "check")]
        {
            let inner = self.inner;
            let is_track = self.is_track;

            drop(self);

            ManagedConstPtr::_new(inner, is_track)
        }
    }

    /// Adds an offset to the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::add`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let arr: [char; 2] = ['a', 'b'];
    /// let nne = NonNullExt::new(arr.as_ptr().cast_mut()).unwrap();
    /// let ptr = unsafe { ManagedMutPtr::new(nne) };
    /// unsafe { assert_eq!(*ptr.add(1), 'b') };
    /// ```
    #[inline]
    pub unsafe fn add(&self, count: usize) -> Self
    where
        T: Sized,
    {
        Self::_new(
            self.inner.add(count),
            #[cfg(feature = "check")]
            self.is_track,
        )
    }

    /// Subtracts an offset from the pointer then returns the result.
    ///
    /// Note that `count` is in units of `T`. For example, `count` = 3 means 12 bytes offset if `T`
    /// is `i32`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::sub`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::{NonNullExt, ManagedMutPtr};
    ///
    /// let arr: [char; 2] = ['a', 'b'];
    /// let ptr = NonNullExt::new(arr.as_ptr_range().end.cast_mut()).unwrap();
    ///
    /// unsafe {
    ///     let ptr = ManagedMutPtr::new(ptr);
    ///     assert_eq!(*ptr.sub(2), 'a');
    /// };
    /// ```
    #[inline]
    pub unsafe fn sub(&self, count: usize) -> Self
    where
        T: Sized,
    {
        Self::_new(
            self.inner.sub(count),
            #[cfg(feature = "check")]
            self.is_track,
        )
    }
}

impl<T: ?Sized> Drop for ManagedMutPtr<T> {
    fn drop(&mut self) {
        #[cfg(feature = "check")]
        if self.is_track {
            debug::remove_ptr(*self.inner);
        }
    }
}

impl<T: ?Sized> Deref for ManagedMutPtr<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: We assume that the pointer is valid by the constructor.
        unsafe { self.inner.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for ManagedMutPtr<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: We assume that the pointer is valid by the constructor.
        unsafe { self.inner.as_mut() }
    }
}

/// Comparison by address.
impl<T: ?Sized> PartialEq for ManagedMutPtr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr().cast::<()>().eq(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> Eq for ManagedMutPtr<T> {}

impl<T: ?Sized> PartialOrd for ManagedMutPtr<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Comparison by address.
impl<T: ?Sized> Ord for ManagedMutPtr<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ptr().cast::<()>().cmp(&other.as_ptr().cast::<()>())
    }
}

impl<T: ?Sized> hash::Hash for ManagedMutPtr<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T: ?Sized> fmt::Debug for ManagedMutPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

// ManagedMutPtr is not a pure pointer unlike NonNull. It can be dereferenced as shared or mutable
// reference without need for unsafe block. That means it's more like a mutable reference. So, we
// don't implement Clone and Copy for it.
// impl<T: ?Sized> Clone for ManagedMutPtr<T> {..}
// impl<T: ?Sized> Copy for ManagedMutPtr<T> {..}

#[cfg(feature = "check")]
mod debug {
    use super::*;
    use dashmap::DashMap;
    use once_cell::sync::Lazy;
    use std::mem;

    enum RefCount {
        Shared(u16),
        Exclusive,
    }

    static RC_MAP: Lazy<DashMap<[usize; 2], RefCount>> = Lazy::new(DashMap::new);

    const MAX_RC: u16 = 256;

    fn create_key<T: ?Sized>(ptr: NonNull<T>) -> [usize; 2] {
        const PTR_SIZE: usize = size_of::<*const ()>();
        // Wide pointer size may change in the future.
        // See https://doc.rust-lang.org/reference/type-layout.html#pointers-and-references-layout
        const WIDE_PTR_SIZE: usize = PTR_SIZE * 2;

        const _: () = {
            assert!(PTR_SIZE == size_of::<usize>());
            assert!(WIDE_PTR_SIZE == size_of::<[usize; 2]>());
        };

        match mem::size_of_val(&ptr) {
            PTR_SIZE => [0, ptr.as_ptr() as *mut () as usize],
            WIDE_PTR_SIZE => {
                // Safety: We checked the size.
                unsafe { mem::transmute_copy(&ptr) }
            }
            _ => unimplemented!(),
        }
    }

    /// Inserts the pointer to the global map.
    ///
    /// In the map, shared pointer is allowed to be inserted multiple times.
    ///
    /// # Panics
    ///
    /// - Panics if insertion count is greater than the limit (256).
    /// - Panics if the map contained the pointer as exclusive pointer.
    pub(super) fn insert_const_ptr<T: ?Sized>(ptr: NonNullExt<T>) {
        let key = create_key(*ptr);
        RC_MAP
            .entry(key)
            .and_modify(|rc| match rc {
                RefCount::Shared(cnt) => {
                    *cnt += 1;
                    assert!(*cnt <= MAX_RC, "too many managed const pointers");
                }
                RefCount::Exclusive => {
                    panic!(
                        "couldn't register `{:p}` as a managed pointer. \
                        a exclusive managed pointer has the same address",
                        ptr.as_ptr()
                    );
                }
            })
            .or_insert(RefCount::Shared(1));
    }

    /// Inserts the pointer to the global map.
    ///
    /// In the map, exclusive pointer is not allowed to be inserted multiple times. To insert the
    /// same pointer, you must remove the pointer first.
    ///
    /// Note, however, that zero-sized `T` is considered shared pointer. It means the pointer is
    /// allowed to be inserted many times.
    ///
    /// # Panics
    ///
    /// Panics if the map contained the pointer.
    pub(super) fn insert_mut_ptr<T: ?Sized>(ptr: NonNullExt<T>) {
        let key = create_key(*ptr);
        RC_MAP
            .entry(key)
            .and_modify(|rc| match rc {
                RefCount::Shared(_) => {
                    panic!(
                        "couldn't register `{:p}` as a managed pointer. \
                        a shared managed pointer has the same address",
                        ptr.as_ptr()
                    );
                }
                RefCount::Exclusive => {
                    panic!(
                        "couldn't register `{:p}` as a managed pointer. \
                        a mutable managed pointer has the same address",
                        ptr.as_ptr()
                    );
                }
            })
            .or_insert(RefCount::Exclusive);
    }

    pub(super) fn remove_ptr<T: ?Sized>(ptr: NonNull<T>) {
        let key = create_key(ptr);
        assert!(
            RC_MAP.contains_key(&key),
            "couldn't find the managed pointer `{ptr:p}`"
        );
        RC_MAP.remove_if_mut(&key, |_, rc| match rc {
            RefCount::Shared(cnt) => {
                *cnt -= 1;
                *cnt == 0
            }
            RefCount::Exclusive => true,
        });
    }
}
