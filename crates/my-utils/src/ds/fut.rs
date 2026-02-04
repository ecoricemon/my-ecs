use std::{
    future::Future,
    hint,
    marker::PhantomPinned,
    mem,
    pin::Pin,
    ptr::NonNull,
    sync::{
        atomic::{AtomicU16, Ordering},
        Arc, Condvar, Mutex,
    },
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
    thread,
};

/// A trait to wake a worker and send [`UnsafeFuture`] to the worker.
pub trait WakeSend: Send + Sync + Clone + 'static {
    /// Wakes associated worker and send [`UnsafeFuture`] to the worker.
    fn wake_send(&self, handle: UnsafeFuture);
}

/// A handle to a future data.
///
/// Name contains `future`, but this struct doesn't implement [`Future`] trait. It provides you poll
/// function instead. You can call poll function on a handle and get the result if the `FutureData`
/// is ready.
///
/// Plus, this is actually a type-erased pointer to a `FutureData` so that owners must deal with the
/// pointer carefully. See the example below to get a feel for how to use the struct.
///
/// # Examples
///
/// ```
/// use my_utils::ds::{WakeSend, UnsafeFuture, ReadyFuture};
/// use std::{
///     future::Future,
///     task::{Poll, Context},
///     sync::{Arc, Mutex, Condvar},
///     pin::Pin,
/// };
///
/// #[derive(Clone)]
/// struct MyWaker {
///     pair: Arc<(Mutex<bool>, Condvar)>
/// }
///
/// impl WakeSend for MyWaker {
///     fn wake_send(&self, _: UnsafeFuture) {
///         let (lock, cvar) = &*self.pair;
///         let mut signaled = lock.lock().unwrap();
///         *signaled = true;
///         cvar.notify_one();
///     }
/// }
///
/// struct MyFuture(u32);
///
/// impl Future for MyFuture {
///     type Output = u32;
///
///     fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
///         let this = self.get_mut();
///         if this.0 == 0 {
///             Poll::Ready(10)
///         } else {
///             this.0 -= 1;
///             cx.waker().wake_by_ref();
///             Poll::Pending
///         }
///     }
/// }
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let fut = MyFuture(2);
/// let waker = MyWaker { pair: Arc::clone(&pair) };
/// let consume = |ret: u32, arg: u32| ret + arg;
/// let fut = UnsafeFuture::new(fut, waker, consume);
///
/// unsafe {
///     let mut pending = 0;
///     while fut.poll() == Poll::Pending {
///         let (lock, cvar) = &*pair;
///         let mut signaled = lock.lock().unwrap();
///         while !*signaled {
///             signaled = cvar.wait(signaled).unwrap();
///         }
///         pending += 1;
///     }
///     let ready = ReadyFuture::new(fut);
///     let res: u32 = ready.consume(1_u32);
///
///     assert_eq!(pending, 2);
///     assert_eq!(res, consume(10, 1));
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct UnsafeFuture {
    /// Type-erased pointer to a future data.
    ///
    /// This pointer is something like 'data' field of [`RawWaker`].
    data: NonNull<u8>,
}

unsafe impl Send for UnsafeFuture {}

impl UnsafeFuture {
    /// Creates a future data in heap memory and returns its handle.
    ///
    /// # Leaks
    ///
    /// There will be memory leak if caller doesn't deallocate the future data.
    /// Future data can be deallocated by
    /// - Calling [`UnsafeFuture::destroy`].
    /// - Turning [`UnsafeFuture`] into [`ReadyFuture`] then dropping it. `ReadyFuture` calls
    ///   [`UnsafeFuture::destroy`] when it's dropped.
    ///
    /// # Examples
    ///
    /// See [`UnsafeFuture`] documentation.
    pub fn new<F, R, W, Arg, CR>(future: F, waker: W, consume: fn(R, Arg) -> CR) -> Self
    where
        F: Future<Output = R> + Send + 'static,
        R: Send + 'static,
        W: WakeSend,
    {
        let pinned = FutureData::new(future, waker, consume);

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

    /// Drops and deallocates associated future data.
    ///
    /// You may need this method when you have to cancel out not ready futures.
    ///
    /// # Safety
    ///
    /// This method must be called only once for the same handles.
    pub unsafe fn destroy(self) {
        // Safety
        // - `self.data` is a valid pointer to a `FutureData`.
        // - drop method will be called only once.
        unsafe {
            let fn_drop = FutureHelper::get_vtable_drop(self.data);
            fn_drop(self.data);
        }
    }

    /// Returns true if associated future data is ready.
    ///
    /// # Safety
    ///
    /// Undefined behavior if associated `FutureData` has been dropped.
    pub unsafe fn is_ready(&self) -> bool {
        unsafe {
            let fn_is_ready = FutureHelper::get_vtable_is_ready(self.data);
            fn_is_ready(self.data)
        }
    }

    /// Tries to make more progress on the associated future data.
    ///
    /// Returning value [`Poll::Ready`] means the `FutureData` is completely resolved and ready to
    /// provide its output. [`Poll::Pending`], on the other hand, means the `FutureData` is not yet
    /// ready and will wake async runtime via the waker you inserted at [`UnsafeFuture::new`] when
    /// it can make more progress.
    ///
    /// # Safety
    ///
    /// Associated future data must be alive, not have been dropped.
    ///
    /// # Examples
    ///
    /// See [`UnsafeFuture`] documentation.
    pub unsafe fn poll(self) -> Poll<()> {
        unsafe {
            let fn_poll_unchecked = FutureHelper::get_vtable_poll_unchecked(self.data);
            if fn_poll_unchecked(self.data) {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        }
    }

    /// Returns true if the given waker is the same as the type you inserted at
    /// [`UnsafeFuture::new`].
    ///
    /// # Safety
    ///
    /// Waker type `W` must be the same as the type you inserted at [`UnsafeFuture::new`].
    pub unsafe fn will_wake<W>(self, other: &W) -> bool
    where
        W: WakeSend + PartialEq,
    {
        unsafe { FutureData::<(), (), W, (), ()>::will_wake(self.data, other) }
    }

    /// Sets a new waker to the associated future data.
    ///
    /// # Safety
    ///
    /// Waker type `W` must be the same as the type you inserted at [`UnsafeFuture::new`].
    pub unsafe fn set_waker<W>(self, waker: W) -> W
    where
        W: WakeSend + PartialEq,
    {
        unsafe { FutureData::<(), (), W, (), ()>::set_waker(self.data, waker) }
    }

    /// # Safety
    ///
    /// Argument types `Arg` and `CR` must be the same as the types determined on
    /// [`UnsafeFuture::new`].
    unsafe fn consume<Arg, CR>(self, arg: Arg) -> CR {
        unsafe {
            let raw = FutureHelper::get_vtable_delegate_consume(self.data);
            let fn_delegate_consume =
                mem::transmute::<unsafe fn(), unsafe fn(NonNull<u8>, Arg) -> CR>(raw);
            fn_delegate_consume(self.data, arg)
        }
    }
}

/// A handle to a *ready* future data.
///
/// The struct can be created from ready [`UnsafeFuture`] only, and it doesn't provide methods such
/// as poll except [`ReadyFuture::consume`]. You can get the result from the ready `FutureData`
/// through the consume method, then associated `FutureData` will be dropped and deallocated.
///
/// See [`UnsafeFuture`] documentation to see how this struct is used.
#[derive(Debug)]
#[repr(transparent)]
pub struct ReadyFuture(UnsafeFuture);

impl ReadyFuture {
    /// Creates a new [`ReadyFuture`] from the given ready [`UnsafeFuture`].
    ///
    /// # Panics
    ///
    /// Panics if associated future data is not ready.
    ///
    /// # Safety
    ///
    /// Undefined behavior if associated `FutureData` is not alive.
    ///
    /// # Examples
    ///
    /// See [`UnsafeFuture`] documentation.
    pub unsafe fn new(future: UnsafeFuture) -> Self {
        assert!(unsafe { future.is_ready() });

        Self(future)
    }

    /// Takes the result out of associated future data, then converts it by the consume function
    /// registered at [`UnsafeFuture::new`], and then returns the converted result.
    ///
    /// By taking `self`, it's dropped at the end of the method, then drops and deallocates the
    /// associated future data as well.
    ///
    /// # Safety
    ///
    /// `Arg` and `CR` must be the same as the types determined on [`UnsafeFuture::new`].
    ///
    /// # Examples
    ///
    /// See [`UnsafeFuture`] documentation.
    pub unsafe fn consume<Arg, CR>(self, arg: Arg) -> CR {
        unsafe { self.0.consume(arg) }
        // `self` goes out of scope then be dropped.
    }
}

impl Drop for ReadyFuture {
    fn drop(&mut self) {
        unsafe { self.0.destroy() };
    }
}

#[derive(Debug)]
#[repr(C)]
struct FutureData<F, R, W, Arg, CR> {
    /// Functions that receive a pointer to this struct as first parameter.
    //
    // * Fixed size, field address is equal to FutureData
    //
    // This field must be located at the first position of this struct, So, raw pointers to this
    // structs can be translated as `FutureVTable`s as well, in turn, clients can call to various
    // functions in vtable just using the one pointer.
    vtable: FutureVTable,

    /// True if output is initialized. Also, this provides synchronization between workers.
    ///
    /// * Fixed size, field address can be calculated regardless of generic parameters
    state: AtomicU16,

    /// Function consuming the output with anonymous argument.
    ///
    /// * Fixed size, field address can be calculated regardless of generic parameters
    consume: fn(R, Arg) -> CR,

    /// Waker that wakes up the polling thread, a.k.a. executor or runtime.
    //
    // * Dynamic size, but field address can be calculated if alignment is given.
    waker: W,

    /// Future data.
    future: F,

    /// Output of the future.
    output: Option<R>,

    _pin: PhantomPinned,
}

impl<F, R, W, Arg, CR> FutureData<F, R, W, Arg, CR>
where
    F: Future<Output = R> + Send + 'static,
    R: Send + 'static,
    W: WakeSend,
{
    fn new(future: F, waker: W, consume: fn(R, Arg) -> CR) -> Pin<Box<Self>> {
        // Erases type `Arg` and `CR` from `delegate_consume`, so we can hold it.
        let delegate_consume = unsafe {
            mem::transmute::<unsafe fn(NonNull<u8>, Arg) -> CR, unsafe fn()>(Self::delegate_consume)
        };

        // See vtable eunctions below.
        let vtable = FutureVTable {
            is_ready: Self::is_ready,
            poll_unchecked: Self::poll_unchecked,
            drop: Self::drop,
            wake_send: Self::wake_send,
            delegate_consume,
        };

        Box::pin(Self {
            vtable,
            waker,
            future,
            consume,
            output: None,
            state: AtomicU16::new(0),
            _pin: PhantomPinned,
        })
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// The given pointer must be a valid pointer to *pinned* [`FutureData`].
    unsafe fn is_ready(data: NonNull<u8>) -> bool {
        let ptr_state = FutureHelper::get_ptr_state(data);
        FutureHelper::lock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_OUTPUT,
            FutureHelper::FLAG_SET_OUTPUT,
            Ordering::Acquire,
        );

        let ptr_output = FutureHelper::get_ptr_output::<F, R, W, Arg, CR>(data);
        let output = unsafe { ptr_output.as_ref() };
        let is_ready = output.is_some();

        FutureHelper::unlock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_OUTPUT,
            Ordering::Relaxed,
        );
        is_ready
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// - The given pointer must be a valid pointer to *pinned* [`FutureData`].
    /// - Callers must not call this once the future has completed.
    unsafe fn poll_unchecked(data: NonNull<u8>) -> bool {
        const CLEAR_MASK: u16 =
            FutureHelper::FLAG_CLEAR_MASK_FUTURE & FutureHelper::FLAG_CLEAR_MASK_OUTPUT;
        const SET: u16 = FutureHelper::FLAG_SET_FUTURE | FutureHelper::FLAG_SET_OUTPUT;
        const LOCK_TRY: u32 = 10;

        // We need syncronization here.
        // e.g. poll on worker A -> send future to worker B -> poll on worker B
        let ptr_state = FutureHelper::get_ptr_state(data);
        if FutureHelper::try_wait(ptr_state, CLEAR_MASK, SET, Ordering::Acquire, LOCK_TRY).is_err()
        {
            // Couldn't acquire the lock — another thread is still polling this future. Re-wake so
            // the future gets re-scheduled for a later poll attempt.
            let fn_wake_send = FutureHelper::get_vtable_wake_send(data);
            fn_wake_send(data);
            return false;
        }

        // Creates `Context` from the given data pointer.
        let data_ = data.as_ptr().cast::<()>().cast_const();
        let raw_waker = RawWaker::new(data_, raw_waker_vtable());
        let waker = unsafe { Waker::from_raw(raw_waker) };
        let mut cx = Context::from_waker(&waker);

        // Polls the future and returns true if its output is ready.
        let fut = unsafe {
            let fut = FutureHelper::get_ptr_future::<F, R, W, Arg, CR>(data).as_mut();
            Pin::new_unchecked(fut)
        };
        let is_ready = if let Poll::Ready(output) = fut.poll(&mut cx) {
            let slot = unsafe { FutureHelper::get_ptr_output::<F, R, W, Arg, CR>(data).as_mut() };
            *slot = Some(output);
            true
        } else {
            false
        };

        // We need to synchronize regardless of whether or not the future has completed because this
        // polling could make some progress.
        FutureHelper::unlock_free(ptr_state, CLEAR_MASK, Ordering::Release);
        is_ready
    }

    /// Calls drop methods on [`FutureData`] pointed by the given data pointer, then release the
    /// memory.
    ///
    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// The given pointer must be a valid pointer to [`FutureData`]. Also, other threads must not
    /// access the same future data any longer.
    unsafe fn drop(data: NonNull<u8>) {
        unsafe {
            let this = data.cast::<FutureData<F, R, W, Arg, CR>>().as_mut();

            // Synchronization is required. Future data must be dropped from its synchronized final
            // state.
            this.state.load(Ordering::Acquire);

            drop(Box::from_raw(this));
        };
    }

    /// * data - A pointer to [`FutureData`].
    ///
    /// # Safety
    ///
    /// The given pointer must be a valid pointer to [`FutureData`].
    unsafe fn wake_send(data: NonNull<u8>) {
        let ptr_state = FutureHelper::get_ptr_state(data);
        FutureHelper::lock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            FutureHelper::FLAG_SET_WAKER,
            Ordering::Acquire,
        );

        let ptr_waker = FutureHelper::get_ptr_waker::<W>(data);
        let waker = unsafe { ptr_waker.as_ref() };
        waker.wake_send(UnsafeFuture { data });

        FutureHelper::unlock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            Ordering::Release,
        );
    }

    unsafe fn delegate_consume(data: NonNull<u8>, arg: Arg) -> CR {
        let ptr_state = FutureHelper::get_ptr_state(data);
        FutureHelper::lock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_OUTPUT,
            FutureHelper::FLAG_SET_OUTPUT,
            Ordering::Acquire,
        );

        let mut ptr_output = FutureHelper::get_ptr_output::<F, R, W, Arg, CR>(data);
        let slot = unsafe { ptr_output.as_mut() };
        let output: R = slot.take().unwrap();

        let ptr_consume = FutureHelper::get_ptr_consume::<R, Arg, CR>(data);
        let consume = unsafe { *ptr_consume.as_ptr() };
        let ret = consume(output, arg);

        FutureHelper::unlock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_OUTPUT,
            Ordering::Release,
        );

        ret
    }
}

/// W in FutureData has a fixed offset, so we can get `waker` of the future data regardless of
/// generic parameters.
impl<F, R, W, Arg, CR> FutureData<F, R, W, Arg, CR>
where
    W: WakeSend + PartialEq,
{
    unsafe fn will_wake(data: NonNull<u8>, waker: &W) -> bool {
        let ptr_state = FutureHelper::get_ptr_state(data);
        FutureHelper::lock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            FutureHelper::FLAG_SET_WAKER,
            Ordering::Acquire,
        );

        let ptr_waker = FutureHelper::get_ptr_waker::<W>(data);
        let this_waker = unsafe { ptr_waker.as_ref() };
        let is_same = this_waker == waker;

        FutureHelper::unlock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            Ordering::Relaxed,
        );
        is_same
    }

    unsafe fn set_waker(data: NonNull<u8>, waker: W) -> W {
        let ptr_state = FutureHelper::get_ptr_state(data);
        FutureHelper::lock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            FutureHelper::FLAG_SET_WAKER,
            Ordering::Acquire,
        );

        let mut ptr_waker = FutureHelper::get_ptr_waker::<W>(data);
        let this_waker = unsafe { ptr_waker.as_mut() };
        let old = mem::replace(this_waker, waker);

        FutureHelper::unlock_free(
            ptr_state,
            FutureHelper::FLAG_CLEAR_MASK_WAKER,
            Ordering::Release,
        );
        old
    }
}

type FutureVTableIsReady = unsafe fn(NonNull<u8>) -> bool;
type FutureVTablePollUnchecked = unsafe fn(NonNull<u8>) -> bool;
type FutureVTableDrop = unsafe fn(NonNull<u8>);
type FutureVTableWakeSend = unsafe fn(NonNull<u8>);
type FutureVTableDelegateConsume = unsafe fn();

#[derive(Debug, Clone, Copy)]
struct FutureVTable {
    /// A function pointer to [`FutureData::is_ready`].
    is_ready: FutureVTableIsReady,

    /// A function pointer to [`FutureData::poll_unchecked`].
    poll_unchecked: FutureVTablePollUnchecked,

    /// A function pointer to [`FutureData::drop`].
    drop: FutureVTableDrop,

    /// A function pointer to [`FutureData::wake_send`].
    wake_send: FutureVTableWakeSend,

    /// A function pointer to [`FutureData::delegate_consume`].
    //
    // Since future return type is unknown here, this type erased function pointer must be cast with
    // correct type like 'unsafe fn(NonNull<u8>, Arg)'.
    delegate_consume: FutureVTableDelegateConsume,
}

fn raw_waker_vtable() -> &'static RawWakerVTable {
    /// * data - A pointer to [`FutureData`].
    unsafe fn clone(data: *const ()) -> RawWaker {
        RawWaker::new(data, raw_waker_vtable())
    }

    /// * data - A pointer to [`FutureData`].
    unsafe fn wake(data: *const ()) {
        unsafe { wake_by_ref(data) }
    }

    /// * data - A pointer to [`FutureData`].
    unsafe fn wake_by_ref(data: *const ()) {
        unsafe {
            let data = NonNull::new_unchecked(data.cast::<u8>().cast_mut());
            let fn_wake_send = FutureHelper::get_vtable_wake_send(data);
            fn_wake_send(data)
        }
    }

    /// * data - A pointer to [`FutureData`].
    //
    // This is a drop function for `std::task::RawWaker`, not for `FutureData`. We're treating
    // `UnsafeFuture` as the `RawWaker`, So we don't have to do something here.
    unsafe fn drop(_data: *const ()) {}

    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);

    &VTABLE
}

struct FutureHelper;

impl FutureHelper {
    #[inline]
    fn get_vtable_is_ready(data: NonNull<u8>) -> FutureVTableIsReady {
        let offset = memoffset::offset_of!(FutureVTable, is_ready);
        unsafe { *data.as_ptr().add(offset).cast() }
    }

    #[inline]
    fn get_vtable_poll_unchecked(data: NonNull<u8>) -> FutureVTablePollUnchecked {
        let offset = memoffset::offset_of!(FutureVTable, poll_unchecked);
        unsafe { *data.as_ptr().add(offset).cast() }
    }

    #[inline]
    fn get_vtable_drop(data: NonNull<u8>) -> FutureVTableDrop {
        let offset = memoffset::offset_of!(FutureVTable, drop);
        unsafe { *data.as_ptr().add(offset).cast() }
    }

    #[inline]
    fn get_vtable_wake_send(data: NonNull<u8>) -> FutureVTableWakeSend {
        let offset = memoffset::offset_of!(FutureVTable, wake_send);
        unsafe { *data.as_ptr().add(offset).cast() }
    }

    #[inline]
    fn get_vtable_delegate_consume(data: NonNull<u8>) -> FutureVTableDelegateConsume {
        let offset = memoffset::offset_of!(FutureVTable, delegate_consume);
        unsafe { *data.as_ptr().add(offset).cast() }
    }

    #[inline]
    fn get_ptr_state(data: NonNull<u8>) -> NonNull<AtomicU16> {
        let offset = memoffset::offset_of!(FutureData::<(), (), (), (), ()>, state);
        unsafe {
            let ptr = data.as_ptr().add(offset).cast();
            NonNull::new_unchecked(ptr)
        }
    }

    #[inline]
    fn get_ptr_consume<R, Arg, CR>(data: NonNull<u8>) -> NonNull<fn(R, Arg) -> CR> {
        let offset = memoffset::offset_of!(FutureData::<(), R, (), Arg, CR>, consume);
        unsafe {
            let ptr = data.as_ptr().add(offset).cast();
            NonNull::new_unchecked(ptr)
        }
    }

    #[inline]
    fn get_ptr_waker<W>(data: NonNull<u8>) -> NonNull<W> {
        let offset = memoffset::offset_of!(FutureData::<(), (), W, (), ()>, waker);
        unsafe {
            let ptr = data.as_ptr().add(offset).cast();
            NonNull::new_unchecked(ptr)
        }
    }

    #[inline]
    fn get_ptr_future<F, R, W, Arg, CR>(data: NonNull<u8>) -> NonNull<F> {
        let offset = memoffset::offset_of!(FutureData::<F, R, W, Arg, CR>, future);
        unsafe {
            let ptr = data.as_ptr().add(offset).cast();
            NonNull::new_unchecked(ptr)
        }
    }

    #[inline]
    fn get_ptr_output<F, R, W, Arg, CR>(data: NonNull<u8>) -> NonNull<Option<R>> {
        let offset = memoffset::offset_of!(FutureData::<F, R, W, Arg, CR>, output);
        unsafe {
            let ptr = data.as_ptr().add(offset).cast();
            NonNull::new_unchecked(ptr)
        }
    }

    // === State bits operations ===

    const FLAG_MASK: u16 = 0b1; // 1 bit mask for lock-unlock
    const FLAG_SET: u16 = 0b1; // 0: available, 1: in use

    // Flag about *waker* field of the FutureData
    const FLAG_SHIFT_WAKER: u16 = 0;
    const FLAG_CLEAR_MASK_WAKER: u16 = !(Self::FLAG_MASK << Self::FLAG_SHIFT_WAKER);
    const FLAG_SET_WAKER: u16 = Self::FLAG_SET << Self::FLAG_SHIFT_WAKER;

    // Flag about *future* field of the FutureData
    const FLAG_SHIFT_FUTURE: u16 = 1;
    const FLAG_CLEAR_MASK_FUTURE: u16 = !(Self::FLAG_MASK << Self::FLAG_SHIFT_FUTURE);
    const FLAG_SET_FUTURE: u16 = Self::FLAG_SET << Self::FLAG_SHIFT_FUTURE;

    // Flag about *output* field of the FutureData
    const FLAG_SHIFT_OUTPUT: u16 = 2;
    const FLAG_CLEAR_MASK_OUTPUT: u16 = !(Self::FLAG_MASK << Self::FLAG_SHIFT_OUTPUT);
    const FLAG_SET_OUTPUT: u16 = Self::FLAG_SET << Self::FLAG_SHIFT_OUTPUT;

    /// This will give up a CPU timeslice someone set the `set_flags`, which in turn makes
    /// not light context switching. But the future is designed to be accessed once at a time, so
    /// we're expecting no yeilding optimistically.
    ///
    /// * clear_mask - e.g. `1111_0000_1111` will clear mid 4 bits to 0.
    /// * set_flags - e.g. `0000_0101_0000` will set cleared bits to `0101`.
    fn try_wait(
        ptr_state: NonNull<AtomicU16>,
        clear_mask: u16,
        set_flags: u16,
        success_order: Ordering,
        num_try: u32,
    ) -> Result<(), ()> {
        let state = unsafe { ptr_state.as_ref() };
        let mut cur_state = state.load(Ordering::Relaxed);

        for _ in 0..num_try {
            let expected_cur_state = cur_state & clear_mask;
            let next_state = expected_cur_state | set_flags;
            match state.compare_exchange_weak(
                expected_cur_state,
                next_state,
                success_order,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(()),
                Err(prev_state) => {
                    cur_state = prev_state;
                    thread::yield_now();
                }
            }
        }
        Err(())
    }

    /// No yeilding, No limit
    ///
    /// # Note
    ///
    /// This method can cause priority inversion due to busy-wait if someone set `set_flags` before.
    /// But the future is not desinged to be accessed frequently from multiple threads at the same
    /// time. If the future should work in such circumstances, it would be better to be cooperated
    /// with proper lock mechanism.
    fn lock_free(
        ptr_state: NonNull<AtomicU16>,
        clear_mask: u16,
        set_flags: u16,
        success_order: Ordering,
    ) {
        let state = unsafe { ptr_state.as_ref() };
        let mut cur_state = state.load(Ordering::Relaxed);

        loop {
            // If another thread have authority of the flag, that thread will clear the flag. So,
            // this thread or the other thread definitely make progress.
            let expected_cur_state = cur_state & clear_mask;
            let next_state = expected_cur_state | set_flags;
            match state.compare_exchange_weak(
                expected_cur_state,
                next_state,
                success_order,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(prev_state) => cur_state = prev_state,
            }
            hint::spin_loop();
        }
    }

    /// No yeilding, No limit
    ///
    /// # Note
    ///
    /// See documnetation of [`Self::lock_free`].
    fn unlock_free(ptr_state: NonNull<AtomicU16>, clear_mask: u16, success_order: Ordering) {
        let state = unsafe { ptr_state.as_ref() };
        let mut cur_state = state.load(Ordering::Relaxed);

        loop {
            let next_state = cur_state & clear_mask;
            match state.compare_exchange_weak(
                cur_state,
                next_state,
                success_order,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(prev_state) => cur_state = prev_state,
            }
            hint::spin_loop();
        }
    }
}

/// Runs the given future to completion on the current worker.
///
/// This blocks until the given future is complete, then returns the result of the future.
///
/// # Examples
///
/// ```
/// use my_utils::ds::block_on;
/// use std::{
///     future::Future,
///     task::{Poll, Context},
///     pin::Pin,
/// };
///
/// struct MyFuture {
///     count: u32,
///     result: u32,
/// }
///
/// impl Future for MyFuture {
///     type Output = u32;
///
///     fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
///         let this = self.get_mut();
///         if this.count == 0 {
///             Poll::Ready(this.result)
///         } else {
///             this.count -= 1;
///             this.result += 1;
///             cx.waker().wake_by_ref();
///             Poll::Pending
///         }
///     }
/// }
///
/// let res = block_on(MyFuture { count: 2, result: 0 });
/// assert_eq!(res, 2);
/// ```
pub fn block_on<F, R>(future: F) -> R
where
    F: Future<Output = R> + 'static,
    R: 'static,
{
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let waker = Waker {
        pair: Arc::clone(&pair),
    };

    // The future and its output won't be sent elsewhere.
    let future = DoNotSend(future);
    let future = UnsafeFuture::new(future, waker, |r, ()| r);

    loop {
        unsafe {
            match future.poll() {
                Poll::Ready(()) => {
                    let ready_future = ReadyFuture::new(future);
                    let ret: DoNotSend<R> = ready_future.consume(());
                    return ret.0;
                }
                Poll::Pending => {
                    let (lock, cvar) = &*pair;
                    let mut signaled = lock.lock().unwrap();
                    while !*signaled {
                        signaled = cvar.wait(signaled).unwrap();
                    }
                }
            };
        }
    }

    // === Internal structs ===

    #[derive(Clone)]
    struct Waker {
        pair: Arc<(Mutex<bool>, Condvar)>,
    }

    impl WakeSend for Waker {
        fn wake_send(&self, _: UnsafeFuture) {
            let (lock, cvar) = &*self.pair;
            let mut signaled = lock.lock().unwrap();
            *signaled = true;
            cvar.notify_one();
        }
    }

    #[repr(transparent)]
    struct DoNotSend<T>(T);

    unsafe impl<T> Send for DoNotSend<T> {}

    impl<T: Future> Future for DoNotSend<T> {
        type Output = DoNotSend<T::Output>;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            // Safety: Possible thanks to repr(transparent)
            let this: Pin<&mut T> = unsafe { mem::transmute(self) };
            match this.poll(cx) {
                Poll::Pending => Poll::Pending,
                Poll::Ready(r) => Poll::Ready(DoNotSend(r)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::TimerFuture;
    use crossbeam_channel::Sender;
    use std::{
        future::Future,
        pin::Pin,
        sync::{Arc, Mutex},
        task::{Context, Poll},
        thread::{Builder, JoinHandle},
    };

    #[test]
    fn test_block_on() {
        use std::{sync::Arc, thread, time::Duration};

        let tid = Arc::new(thread::current().id());

        // Future will be run on the same thread calling `block_on`.
        let future = async move {
            let cur_tid = thread::current().id();
            assert_eq!(cur_tid, *tid);
            TimerFuture::after(Duration::from_millis(1)).await;

            let cur_tid = thread::current().id();
            assert_eq!(cur_tid, *tid);
            TimerFuture::after(Duration::from_millis(1)).await;

            let cur_tid = thread::current().id();
            assert_eq!(cur_tid, *tid);
            42
        };

        let res = block_on(future);
        assert_eq!(res, 42);
    }

    /// Tests if polling to [`UnsafeFuture`] is safe over threads. Here's how the test scenario
    /// looks like.
    ///
    /// ```text
    ///     Timeline of each thread
    /// ---------------------------------
    /// main       | waker   | beholder
    /// fut.poll() |         |
    ///            | wake()  |
    ///            |         | fut.poll()
    /// ```
    ///
    /// `beholder` must be able to see what `main` have done to the `fut`. This test will fail if
    /// data race occurs.
    #[test]
    fn test_unsafe_future() {
        let state = Arc::new(Mutex::new(0));

        let (tx, rx) = crossbeam_channel::unbounded::<UnsafeFuture>();
        let c_state = Arc::clone(&state);

        let beholder = Builder::new()
            .name("beholder".to_owned())
            .spawn(move || {
                // `beholder` will be woken up by `waker` thread.
                while let Ok(future) = rx.recv() {
                    match unsafe { future.poll() } {
                        Poll::Ready(()) => {
                            unsafe { drop(ReadyFuture::new(future)) };
                            break;
                        }
                        Poll::Pending => {}
                    }
                }

                // All is ok, let's finish the test.
                assert_eq!(*c_state.lock().unwrap(), 2);
            })
            .unwrap();

        let c_state = Arc::clone(&state);
        let future = async move {
            // If `beholder` cannot see future's change `main` thread made, it will see something
            // that has not changed. Which means that it executes future from the beginning.
            {
                // state: 0 -> 1 on the `main` thread.
                let mut state = c_state.lock().unwrap();
                assert_eq!(*state, 0);
                *state += 1;
            }

            // `After` will spawn `waker` thread which will wake `beholder`.
            After::new(1).await;

            // state: 1 -> 2 on the `beholder` thread.
            let mut state = c_state.lock().unwrap();
            assert_eq!(*state, 1);
            *state += 1;
        };
        let waker = MyWaker { tx };
        let future = UnsafeFuture::new(future, waker, |(), ()| {});

        // First polling on the future.
        let _ = unsafe { future.poll() };

        // Cleans up.
        beholder.join().unwrap();
    }

    #[derive(Clone)]
    struct MyWaker {
        tx: Sender<UnsafeFuture>,
    }

    impl WakeSend for MyWaker {
        fn wake_send(&self, handle: UnsafeFuture) {
            self.tx.send(handle).unwrap();
        }
    }

    struct After {
        cnt: u32,
        handle: Option<JoinHandle<()>>,
    }

    impl After {
        fn new(cnt: u32) -> Self {
            Self { cnt, handle: None }
        }
    }

    impl Drop for After {
        fn drop(&mut self) {
            if let Some(handle) = self.handle.take() {
                handle.join().unwrap();
            }
        }
    }

    impl Future for After {
        type Output = ();

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            if self.cnt > 0 {
                let this = self.get_mut();

                this.cnt -= 1;

                // `waker` thread will wake up `beholder` by sending future.
                let waker = cx.waker().clone();
                let handle = Builder::new()
                    .name("waker".to_owned())
                    .spawn(move || waker.wake())
                    .unwrap();
                this.handle = Some(handle);

                Poll::Pending
            } else {
                Poll::Ready(())
            }
        }
    }
}
