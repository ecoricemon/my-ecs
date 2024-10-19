use std::{
    future::Future,
    marker::PhantomPinned,
    mem,
    pin::Pin,
    ptr::NonNull,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

pub trait WakeSend: Send + Sync + Clone + 'static {
    fn wake_send(&self, handle: UnsafeFuture);
}

impl<F> WakeSend for F
where
    F: Fn(UnsafeFuture) + Send + Sync + Clone + 'static,
{
    fn wake_send(&self, handle: UnsafeFuture) {
        (self)(handle)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct UnsafeFuture {
    /// Pointer to boxed [`FutureData`].  
    /// This pointer also acts like 'data' field of [`std::task::RawWaker`].
    data: NonNull<u8>,
}

unsafe impl Send for UnsafeFuture {}

impl UnsafeFuture {
    /// Allocates and creates [`FutureData`] and returns its pointer
    /// wrppaed in this struct.
    pub fn new<F, R, W>(future: F, waker: W) -> Self
    where
        F: Future<Output = R> + Send + 'static,
        R: Send + 'static,
        W: WakeSend,
    {
        let pinned = FutureData::new(future, waker);

        // `FutureData` is created wrapped in `Pin<Box<T>>` because it's another type of future.
        // But this struct will manage it through its pointer, so let's unwrap it.
        //
        // # Safety: We won't move the `FutureData` in this struct.
        let data = unsafe {
            let boxed = Pin::into_inner_unchecked(pinned);
            NonNull::new_unchecked(Box::into_raw(boxed)).cast::<u8>()
        };

        Self { data }
    }

    /// Drops and deallocates linked [`FutureData`].
    ///
    /// # Safety
    ///
    /// Caller must call this method only once over cloned [`UnsafeFuture`]s.
    pub unsafe fn destroy(self) {
        // Safety
        // - `self.data` is a valid pointer to a `FutureData`.
        // - drop method will be called only once.
        let vtable = self.data.cast::<FutureVTable>().as_mut();
        (vtable.drop)(self.data)
    }

    /// # Safety
    ///
    /// Undefined behavior if conditions below are not met.
    /// - Linked [`FutureData`] must be alive, not have been dropped.
    /// - Polling must occur on only one thread at a time,
    ///   and caller should synchronize over threads.
    /// - Type `R` must be the same as the one future creates.
    pub unsafe fn poll_unchecked<R>(self) -> Poll<ReadyFuture<R>>
    where
        R: Send + 'static,
    {
        let vtable = self.data.cast::<FutureVTable>().as_mut();
        if (vtable.poll_unchecked)(self.data) {
            let take_output_unchecked = mem::transmute::<unsafe fn(), unsafe fn(NonNull<u8>) -> R>(
                vtable.take_output_unchecked,
            );
            let output = (take_output_unchecked)(self.data);
            Poll::Ready(ReadyFuture {
                output,
                handle: self,
            })
        } else {
            Poll::Pending
        }
    }

    /// # Safety
    ///
    /// Waker type `W` must be the same as the type determined on [`new`].
    ///
    /// [`new`]: Self::new
    pub unsafe fn will_wake<W>(self, other: &W) -> bool
    where
        W: WakeSend + Eq,
    {
        let waker = FutureData::<(), (), W>::waker_ptr(self.data).as_ref();
        waker == other
    }

    /// # Safety
    ///
    /// Waker type `W` must be the same as the type determined on [`new`].
    ///
    /// [`new`]: Self::new
    pub unsafe fn set_waker<W>(self, waker: W) -> W
    where
        W: WakeSend,
    {
        let old = FutureData::<(), (), W>::waker_ptr(self.data).as_mut();
        mem::replace(old, waker)
    }
}

#[derive(Debug)]
pub struct ReadyFuture<R> {
    output: R,
    handle: UnsafeFuture,
}

impl<R> ReadyFuture<R> {
    /// Deallocates inner future and returns output of the future.
    /// Do not call [`UnsafeFuture::destroy`] for the inner future.
    ///
    /// # Safety
    ///
    /// See [`UnsafeFuture::destroy`].
    pub unsafe fn take(self) -> R {
        self.handle.destroy();
        self.output
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct FutureData<F, R, W> {
    /// Functions that receive a pointer to this struct as first parameter.
    //
    // This field must be located at the first position of this struct, So, raw
    // pointers to this structs can be translated as `FutureVTable`s as well,
    // in turn, clients can call to various functions in vtable just using the
    // one pointer.
    vtable: FutureVTable,

    /// Waker that wakes up the polling thread, a.k.a. executor or runtime.
    //
    // This field must be located at the second position of this struct, So, raw
    // pointers to this structs can be translated as `W`s as well,
    waker: W,

    /// Future data.
    future: F,

    /// Output of the future.
    output: Option<R>,

    _pin: PhantomPinned,
}

impl<F, R, W> FutureData<F, R, W>
where
    F: Future<Output = R> + Send + 'static,
    R: Send + 'static,
    W: WakeSend,
{
    pub fn new(future: F, waker: W) -> Pin<Box<Self>> {
        // Erases type from `take_output_unchecked`, so we can hold it.
        let take_output_unchecked = unsafe {
            mem::transmute::<unsafe fn(NonNull<u8>) -> _, unsafe fn()>(Self::take_output_unchecked)
        };

        // See vtable functions below.
        let vtable = FutureVTable {
            poll_unchecked: Self::poll_unchecked,
            drop: Self::drop,
            take_output_unchecked,
            wake_send: Self::wake_send,
        };

        Box::pin(Self {
            vtable,
            waker,
            future,
            output: None,
            _pin: PhantomPinned,
        })
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// - The given pointer must be a valid pointer to *pinned* [`FutureData`].
    unsafe fn poll_unchecked(data: NonNull<u8>) -> bool {
        // Creates pinned future from the given data pointer.
        let this = data.cast::<FutureData<F, R, W>>().as_mut();
        let pinned_future = Pin::new_unchecked(&mut this.future);

        // Creates `Context` from the given data pointer.
        let data = data.as_ptr().cast_const().cast::<()>();
        let raw_waker = RawWaker::new(data, raw_waker_vtable());
        let waker = Waker::from_raw(raw_waker);
        let mut cx = Context::from_waker(&waker);

        // Polls the future and returns true if it's ready.
        if let Poll::Ready(output) = pinned_future.poll(&mut cx) {
            this.output = Some(output);
            true
        } else {
            false
        }
    }

    /// Calls drop methods on [`FutureData`] pointed by the given data pointer,
    /// then release the memory.
    ///
    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// The given pointer must be a valid pointer to [`FutureData`].
    unsafe fn drop(data: NonNull<u8>) {
        let mut this = data.cast::<FutureData<F, R, W>>();
        drop(Box::from_raw(this.as_mut()));
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// - The given pointer must be a valid pointer to [`FutureData`].
    /// - The `FutureData` must have been ready.
    unsafe fn take_output_unchecked(data: NonNull<u8>) -> R {
        let this = data.cast::<FutureData<F, R, W>>().as_mut();
        this.output.take().unwrap_unchecked()
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// The given pointer must be a valid pointer to [`FutureData`].
    unsafe fn wake_send(data: NonNull<u8>) {
        let this = data.cast::<FutureData<F, R, W>>().as_mut();
        this.waker.wake_send(UnsafeFuture { data })
    }
}

impl<W> FutureData<(), (), W> {
    // Address of waker is determined by its alignment only.
    // It doesn't depend on `F` and `R` because it is located right after
    // `FutureVTable` which has fixed size.
    unsafe fn waker_ptr(data: NonNull<u8>) -> NonNull<W> {
        let this = data.cast::<FutureData<(), (), W>>().as_mut();
        let ptr = &mut this.waker as *mut _;
        NonNull::new_unchecked(ptr)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FutureVTable {
    /// A function pointer to [`FutureData::poll_unchecked`].
    pub poll_unchecked: unsafe fn(NonNull<u8>) -> bool,

    /// A function pointer to [`FutureData::drop`].
    pub drop: unsafe fn(NonNull<u8>),

    /// A function pointer to [`FutureData::take_output_unchecked`].
    //
    // Since future return type is unknown here,
    // this type erased function pointer must be casted with correct type like
    // 'unsafe fn(NonNull<u8>) -> R'.
    pub take_output_unchecked: unsafe fn(),

    /// A function pointer to [`FutureData::wake_send`].
    pub wake_send: unsafe fn(NonNull<u8>),
}

fn raw_waker_vtable() -> &'static RawWakerVTable {
    /// * data - A pointer to [`FutureData`].
    unsafe fn clone(data: *const ()) -> RawWaker {
        RawWaker::new(data, raw_waker_vtable())
    }

    /// * data - A pointer to [`FutureData`].
    unsafe fn wake(data: *const ()) {
        wake_by_ref(data)
    }

    /// * data - A pointer to [`FutureData`].
    unsafe fn wake_by_ref(data: *const ()) {
        let vtable = data.cast::<FutureVTable>().as_ref().unwrap_unchecked();
        let data = NonNull::new_unchecked(data.cast::<u8>().cast_mut());
        (vtable.wake_send)(data)
    }

    /// * data - A pointer to [`FutureData`].
    //
    // This is a drop function for `std::task::RawWaker`, not for `FutureData`.
    // We're treating `UnsafeFuture` as the `RawWaker`,
    // So we don't have to do something here.
    unsafe fn drop(_data: *const ()) {}

    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);

    &VTABLE
}
