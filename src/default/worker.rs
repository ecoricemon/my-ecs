#[cfg(not(target_arch = "wasm32"))]
pub use non_web::*;

#[cfg(target_arch = "wasm32")]
pub use web::*;

#[cfg(not(target_arch = "wasm32"))]
mod non_web {
    use crate::{ds::prelude::*, ecs::prelude::*};
    use std::{
        sync::mpsc::{self, Sender},
        thread::{Builder, JoinHandle},
    };

    #[derive(Debug)]
    pub struct WorkerBuilder<'a> {
        inner: Builder,
        name: &'a str,
    }

    impl<'a> WorkerBuilder<'a> {
        pub fn new(name: &'a str) -> Self {
            Self {
                inner: Builder::new().name(name.to_owned()),
                name,
            }
        }

        pub fn stack_size(self, size: usize) -> Self {
            Self {
                inner: self.inner.stack_size(size),
                name: self.name,
            }
        }

        pub fn spawn(self) -> Result<Worker, std::io::Error> {
            Worker::spawn(self)
        }
    }

    pub struct Worker {
        name: Box<str>,
        tx: Sender<Option<ManagedConstPtr<SubContext>>>,
        join_handle: Option<JoinHandle<()>>,
    }

    impl Worker {
        fn spawn(builder: WorkerBuilder) -> Result<Self, std::io::Error> {
            let (tx, rx) = mpsc::channel::<Option<ManagedConstPtr<SubContext>>>();
            let join_handle = builder.inner.spawn(move || {
                while let Some(cx) = rx.recv().unwrap() {
                    SubContext::execute(cx);
                }
            })?;
            Ok(Self {
                name: builder.name.into(),
                tx,
                join_handle: Some(join_handle),
            })
        }
    }

    impl Drop for Worker {
        fn drop(&mut self) {
            // `rx` could be broken if worker panics.
            let _ = self.tx.send(None);
            // Safety: `join_handle` must have been filled.
            let join_handle = unsafe { self.join_handle.take().unwrap_unchecked() };
            let _ = join_handle.join();
        }
    }

    impl Work for Worker {
        fn unpark(&mut self, cx: ManagedConstPtr<SubContext>) -> bool {
            let res = self.tx.send(Some(cx)); // TODO: saw failed. but what condition?
            res.is_ok()
        }

        fn name(&self) -> &str {
            &self.name
        }
    }
}

#[cfg(target_arch = "wasm32")]
mod web {
    use crate::{ds::prelude::*, ecs::prelude::*, util::prelude::*};
    use std::{
        cell::RefCell,
        collections::VecDeque,
        fmt, mem,
        ops::{Deref, DerefMut},
        rc::Rc,
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc, OnceLock,
        },
    };
    use wasm_bindgen::prelude::*;

    #[derive(Debug)]
    #[repr(transparent)]
    pub struct MainWorkerBuilder<'a> {
        inner: WorkerBuilder<'a>,
    }

    impl<'a> MainWorkerBuilder<'a> {
        pub fn new() -> Self {
            let inner = WorkerBuilder::new("main-worker").with_listen("mainOnMessage");
            Self { inner }
        }

        pub fn with_name(self, name: &'a str) -> Self {
            Self {
                inner: self.inner.with_name(name),
            }
        }

        pub fn with_init(self, init: &'a str) -> Self {
            Self {
                inner: self.inner.with_init(init),
            }
        }

        pub fn spawn(self) -> Result<MainWorker, JsValue> {
            MainWorker::spawn(self)
        }
    }

    impl<'a> Default for MainWorkerBuilder<'a> {
        fn default() -> Self {
            Self::new()
        }
    }

    #[derive(Debug)]
    #[repr(transparent)]
    pub struct MainWorker {
        inner: Worker,
    }

    impl MainWorker {
        fn spawn(builder: MainWorkerBuilder) -> Result<Self, JsValue> {
            Ok(Self {
                inner: builder.inner.spawn()?,
            })
        }

        pub fn spawn_children(&self, num: usize) {
            if num == 0 {
                return;
            }

            self.delegate(
                |arg| {
                    let num: f64 = arg.unchecked_into_f64();
                    let num = num as usize;
                    MAIN_WORKER_CTX.with_borrow_mut(|ctx| {
                        for _ in 0..num {
                            str_util::increase_rnumber(&mut ctx.child_name);
                            let worker = WorkerBuilder::new(&ctx.child_name).spawn().unwrap();
                            ctx.children.push(worker);
                        }
                    });
                },
                num.into(),
            );
        }

        pub fn with_children(&self, f: fn(&mut [Worker])) {
            let arg = FnCodec::encode_into_array(f);
            self.delegate(
                |arg| {
                    MAIN_WORKER_CTX.with_borrow_mut(|ctx| {
                        let arg: js_sys::Uint32Array = arg.unchecked_into();
                        // Safety: `arg` is `f`.
                        unsafe {
                            let f = FnCodec::decode_from_array(&arg);
                            let f = mem::transmute::<fn(), fn(&mut [Worker])>(f);
                            ctx.pending.push_back(f);
                        };
                        ctx.ready_run();
                    });
                },
                arg.into(),
            );
        }

        /// Calls the given function on main worker context.
        pub fn delegate(&self, f: fn(arg: JsValue), arg: JsValue) {
            MessageFn { f }.post_to(&self.handle(), arg);
        }
    }

    impl Drop for MainWorker {
        fn drop(&mut self) {
            MAIN_WORKER_CTX.with_borrow_mut(|ctx| {
                ctx.children.clear();
            });
        }
    }

    impl Deref for MainWorker {
        type Target = Worker;

        fn deref(&self) -> &Self::Target {
            &self.inner
        }
    }

    impl DerefMut for MainWorker {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.inner
        }
    }

    #[wasm_bindgen(js_name = mainOnMessage)]
    pub fn main_onmessage(msg: JsValue) {
        if let Some(arr) = msg.dyn_ref::<js_sys::Array>() {
            let header = arr.get(0);
            match MessageHeader::from_js_value(header).0 {
                MessageHeader::FN_INNER => {
                    let f = MessageFn::read_body(arr).f;
                    let arg = MessageFn::read_argument(arr);
                    f(arg);
                }
                _ => {
                    crate::log!("[W] unknown message on main worker");
                }
            }
        } else {
            web::worker_post_message(&msg).unwrap();
        }
    }

    thread_local! {
        #[allow(clippy::thread_local_initializer_can_be_made_const)]
        static MAIN_WORKER_CTX: RefCell<MainWorkerContext> = RefCell::new(
            MainWorkerContext::new()
        );

        static READY_RUN: RefCell<Closure<dyn FnMut()>> = RefCell::new(
            Closure::new(|| {
                MAIN_WORKER_CTX.with_borrow_mut(|ctx| ctx.ready_run());
            })
        );
    }

    #[derive(Debug)]
    pub struct MainWorkerContext {
        /// Child workers.
        children: Vec<Worker>,

        /// Child worker name that will be given to the next spawned child worker.
        child_name: String,

        /// Pending functions.
        pending: VecDeque<fn(&mut [Worker])>,
    }

    impl MainWorkerContext {
        fn new() -> Self {
            Self {
                children: Vec::new(),
                child_name: "sub-worker0".to_owned(),
                pending: VecDeque::new(),
            }
        }

        fn ready_run(&mut self) {
            if self.children.iter().all(|child| child.is_ready()) {
                while let Some(f) = self.pending.pop_front() {
                    f(&mut self.children);
                }
            } else {
                READY_RUN.with_borrow(|ready_run| {
                    const WAIT_MS: i32 = 10;
                    let cb = ready_run.as_ref().unchecked_ref();
                    let global = web::worker_global();
                    global
                        .set_timeout_with_callback_and_timeout_and_arguments_0(cb, WAIT_MS)
                        .unwrap();
                });
            }
        }
    }

    impl Default for MainWorkerContext {
        fn default() -> Self {
            Self::new()
        }
    }

    #[derive(Debug)]
    pub struct WorkerBuilder<'a> {
        name: &'a str,
        script: Option<&'a str>,
        listen: &'a str,
        init: &'a str,
    }

    impl<'a> WorkerBuilder<'a> {
        /// Default message listener of the worker.
        /// See [`worker_onmessage`].
        const DEFAULT_LISTEN: &'static str = "workerOnMessage";
        const DEFAULT_INIT: &'static str = "workerInit";

        pub const fn new(name: &'a str) -> Self {
            Self {
                name,
                script: None,
                init: Self::DEFAULT_INIT,
                listen: Self::DEFAULT_LISTEN,
            }
        }

        pub const fn with_name(mut self, name: &'a str) -> Self {
            self.name = name;
            self
        }

        pub const fn with_script(mut self, script: &'a str) -> Self {
            self.script = Some(script);
            self
        }

        pub const fn with_init(mut self, init: &'a str) -> Self {
            self.init = init;
            self
        }

        pub const fn with_listen(mut self, listen: &'a str) -> Self {
            self.listen = listen;
            self
        }

        pub fn spawn(self) -> Result<Worker, JsValue> {
            Worker::spawn(self)
        }
    }

    pub struct Worker {
        /// JS worker handle.
        handle: web_sys::Worker,

        /// Worker name. You can see this name in browser's dev tool.
        name: Box<str>,

        /// Callback for worker's first response, which is a notification of
        /// the worker's readiness.
        /// The callback will be replaced with [`onmsg`] once it called.
        ///
        /// [`onmsg`]: Self::onmsg
        _on_ready: Closure<dyn FnMut()>,

        /// Callback for worker response.
        #[allow(clippy::type_complexity)]
        onmsg: Rc<RefCell<Closure<dyn FnMut(web_sys::MessageEvent)>>>,

        /// Determines the worker is spawned and ready to listen to message.
        ready: Arc<AtomicBool>,
    }

    impl fmt::Debug for Worker {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Worker")
                .field("name", &self.name)
                .field("ready", &self.ready.as_ref())
                .finish_non_exhaustive()
        }
    }

    impl Worker {
        fn spawn(builder: WorkerBuilder) -> Result<Self, JsValue> {
            // Creates a new worker.
            let handle = create_worker(builder.name, builder.script)?;
            let ready = Arc::new(AtomicBool::new(false));
            let onmsg = Rc::new(RefCell::new(Closure::new(|_| {})));
            let c_handle = handle.clone();
            let c_ready = Arc::clone(&ready);
            let c_onmsg = Rc::clone(&onmsg);

            // Listens to worker's ready notification.
            let on_ready = Closure::new(move || {
                let onmsg = c_onmsg.borrow();
                c_handle.set_onmessage(Some(onmsg.as_ref().unchecked_ref()));
                c_ready.store(true, Ordering::Release);
            });
            handle.set_onmessage(Some(on_ready.as_ref().unchecked_ref()));

            // Sets 'WBG_INIT' if it wasn't set yet.
            let wasm_init = WBG_INIT.get_or_init(|| DEFAULT_WBG_INIT.to_owned());

            // TODO: For now, we assume that wasm use shared memory.
            // Initializes the worker.
            use js_sys::{Object, Reflect};
            let msg = Object::new();
            Reflect::set(&msg, &"module".into(), &wasm_bindgen::module())?;
            Reflect::set(&msg, &"memory".into(), &wasm_bindgen::memory())?;
            Reflect::set(&msg, &"url".into(), &IMPORT_META_URL.as_str().into())?;
            Reflect::set(&msg, &"wasmInit".into(), &wasm_init.into())?;
            Reflect::set(&msg, &"init".into(), &builder.init.into())?;
            Reflect::set(&msg, &"listen".into(), &builder.listen.into())?;
            handle.post_message(&msg)?;

            Ok(Self {
                handle,
                name: builder.name.into(),
                _on_ready: on_ready,
                onmsg,
                ready,
            })
        }

        pub fn handle(&self) -> web_sys::Worker {
            self.handle.clone()
        }

        pub fn is_ready(&self) -> bool {
            self.ready.load(Ordering::Relaxed)
        }

        pub fn set_onmessage<F>(&mut self, mut cb: F)
        where
            F: FnMut(JsValue) + 'static,
        {
            let cb: Closure<dyn FnMut(web_sys::MessageEvent)> =
                Closure::new(move |ev: web_sys::MessageEvent| cb(ev.data()));

            if self.is_ready() {
                self.handle.set_onmessage(Some(cb.as_ref().unchecked_ref()));
            }
            *self.onmsg.borrow_mut() = cb;
        }

        pub fn post_message(&self, msg: &JsValue) -> Result<(), JsValue> {
            self.handle.post_message(msg)
        }
    }

    impl Work for Worker {
        fn unpark(&mut self, cx: ManagedConstPtr<SubContext>) -> bool {
            let ptr = cx.inner().as_ptr();
            drop(cx);
            let res = self.handle.post_message(&JsValue::from(ptr));
            res.is_ok()
        }

        fn name(&self) -> &str {
            &self.name
        }
    }

    impl Drop for Worker {
        /// Terminates web worker *immediately*.
        fn drop(&mut self) {
            self.handle.terminate();
        }
    }

    /// Clients can modify init function of wasm glue JS file before they call [`Worker::spawn`].
    /// If you don't set this value, [`DEFAULT_WBG_INIT`] will be set as default value.
    ///
    /// # Example
    ///
    /// ```rust
    /// use my_ecs::default::prelude::*;
    ///
    /// // Some bundlers may minify export name to '_' or 'default'.
    /// crate::WBG_INIT.set("_".to_owned()).unwrap();
    /// Worker::spawn("worker", 0).unwrap();
    /// ```
    pub static WBG_INIT: OnceLock<String> = OnceLock::new();

    /// wasm-bindgen will generate "__wbg_init" as default export function.
    /// But, I expect that it will be exported as 'default'.
    pub const DEFAULT_WBG_INIT: &str = "default";

    pub const DEFAULT_WORKER_SCRIPT: &str = include_str!("worker.js");

    // Some bundlers could warn about circular dependency caused by worker
    // due to the cycle that looks like
    // "Rust wasm - (bind) -> worker.js -> (import) -> wasm".
    //
    // But, if the worker JS file is substituted with a created object,
    // we can avoid the warning.
    //
    // However, in that case, we need to set bundler to cooperate with the
    // created worker object.
    // For instance, in Vite(v5.4.2), you may need following settings.
    //
    // build: {
    //   rollupOptions: {
    //       // We need to split wasm glue module into a sperate chunk
    //       // 1. Not to include window context data.
    //       //    * wasm glue module will be imported in worker context.
    //       //    * In worker context, we can't access something like document.
    //       // 2. To preserve indirectly used exports.
    //       //    * Rollup doesn't know that we're going to access some exported
    //       //      objects, workerOnMessage for instance, in wasm code.
    //       //    * So we need to make Rollup not to drop those objects.
    //       //
    //       // First of all, we need to make a new entry point for wasm.
    //       input: {
    //         wasm: 'pkg/wasm-index.js', // path to wasm glue file.
    //         ...
    //       },
    //
    //       // Then, put the following.
    //       // * https://rollupjs.org/configuration-options/#preserveentrysignatures
    //       //   Although Rollup says default is already 'exports-only',
    //       //   but I guess Vite 5.4.2 changes it to `false`.
    //       preserveEntrySignatures: 'exports-only',
    //     },
    fn create_worker(name: &str, script: Option<&str>) -> Result<web_sys::Worker, JsValue> {
        web_sys::Worker::new_with_options(
            &script_url(script),
            web_sys::WorkerOptions::new()
                .name(name)
                .type_(web_sys::WorkerType::Module),
        )
    }

    #[wasm_bindgen]
    extern "C" {
        /// URL of wasm glue JS file.
        //
        // We need this URL of wasm glue JS file in order to import it dynamically in workers.
        // So that workers can share the same wasm module and memory.
        // But note that bundler may evaluate "import.meta.url" statically during bundling,
        // which is not what we want, we need to evaluate it at runtime.
        // Therefore, you need to configure your bundler not to do it.
        // (e.g. Webpack does it basically, but Vite(v5.1.6) doesn't do it)
        #[wasm_bindgen(js_namespace = ["import", "meta"], js_name = url)]
        static IMPORT_META_URL: String;
    }

    fn script_url(script: Option<&str>) -> String {
        let script = script.unwrap_or(DEFAULT_WORKER_SCRIPT);
        let blob_parts = js_sys::Array::new_with_length(1);
        blob_parts.set(0, JsValue::from_str(script));

        let mut options = web_sys::BlobPropertyBag::new();
        options.type_("application/javascript");

        let blob = web_sys::Blob::new_with_str_sequence_and_options(&blob_parts, &options).unwrap();
        web_sys::Url::create_object_url_with_blob(&blob).unwrap()
    }

    #[wasm_bindgen(js_name = workerInit)]
    pub fn worker_init() {
        // Nothing to do as default behavior.
    }

    /// # Safety
    ///
    /// Undefined behavior if the pointer is not valid or aliased.
    #[wasm_bindgen(js_name = workerOnMessage)]
    pub unsafe fn worker_onmessage(cx: *mut SubContext) {
        let cx = ManagedConstPtr::new(NonNullExt::new_unchecked(cx));
        SubContext::execute(cx);
    }

    /// Message event header.  
    /// Inner value will be transmuted into f64 and vice versa.
    /// You must guarantee that f64 representation is not Nan (or Inf).
    /// If so, someone(maybe JS) will change it's bits except Nan bits.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MessageHeader(pub u64);

    impl MessageHeader {
        const MAGIC: u64 = 0x0EC5 << (16 * 3);

        const BASE: u64 = Self::MAGIC;

        const FN_INNER: u64 = Self::BASE + 1;
        const FN: Self = Self(Self::FN_INNER);

        pub fn into_js_value(self) -> JsValue {
            let value = f64::from_bits(self.0);
            debug_assert!(value.is_finite()); // Nan or Inf are now allowed.
            JsValue::from_f64(value)
        }

        pub fn from_js_value(value: JsValue) -> Self {
            Self(value.unchecked_into_f64().to_bits())
        }
    }

    const F64_SIZE: usize = mem::size_of::<f64>();
    const F64_ROUND_UP: usize = F64_SIZE - 1;
    const HEADER_LEN: usize = (mem::size_of::<MessageHeader>() + F64_ROUND_UP) / F64_SIZE;
    const U32_SIZE: usize = mem::size_of::<u32>();
    const U32_ROUND_UP: usize = U32_SIZE - 1;

    /// Instant message for sending a function.
    #[derive(Debug, Clone, Copy)]
    #[repr(C)]
    struct MessageFn {
        /// Function pointer.
        //
        // NOTE: We cannot turn an address into f64 directly.
        // Address could be 'inf' or 'nan' in f64 representation.
        // See https://en.wikipedia.org/wiki/IEEE_754-1985
        // Those numbers will keep the meaning of 'inf' or 'nan' though,
        // they can be freely different number in perspective of bit.
        // So we put this value in Uint32Array.
        //
        // According to googling, OSes use 48-bit address space on 64 bit machines.
        // Even if so, it could be dangerous to convert addresses to f64
        // when OSes fill preceding bits to 1.
        f: fn(arg: JsValue),
    }

    impl MessageFn {
        const HEADER: MessageHeader = MessageHeader::FN;

        /// Returns minimum length of [`js_sys::Array`] for this message.
        const fn message_array_len() -> u32 {
            // 3, message looks like [header, [body array], arg].
            const BODY_LEN: u32 = 1;
            const ARG_LEN: u32 = 1;
            HEADER_LEN as u32 + BODY_LEN + ARG_LEN
        }

        fn post_to(self, worker: &web_sys::Worker, arg: JsValue) {
            let buf = js_sys::Array::new_with_length(Self::message_array_len());
            Self::write_header(&buf);
            self.write_body(&buf);
            Self::write_argument(&buf, arg);
            worker.post_message(&buf).unwrap();
        }

        fn write_header(buf: &js_sys::Array) {
            buf.set(0, Self::HEADER.into_js_value());
        }

        fn write_body(&self, buf: &js_sys::Array) {
            let body = FnCodec::encode_into_array(self.f);
            buf.set(1, body.into());
        }

        fn write_argument(buf: &js_sys::Array, arg: JsValue) {
            buf.set(2, arg);
        }

        fn read_body(buf: &js_sys::Array) -> Self {
            debug_assert!(buf.length() >= Self::message_array_len());
            assert_eq!(Self::HEADER, MessageHeader::from_js_value(buf.get(0)));

            let body: js_sys::Uint32Array = buf.get(1).unchecked_into();

            // Safety: We checked the message header.
            unsafe {
                let f = FnCodec::decode_from_array(&body);
                Self {
                    f: mem::transmute::<fn(), fn(JsValue)>(f),
                }
            }
        }

        fn read_argument(buf: &js_sys::Array) -> JsValue {
            buf.get(2)
        }
    }

    #[repr(C)]
    union FnCodec {
        src: fn(),
        dst: [u32; Self::len()],
    }

    impl FnCodec {
        const fn len() -> usize {
            // 2 (on 64 bit) or 1 (on 32 bit)
            (mem::size_of::<fn()>() + U32_ROUND_UP) / U32_SIZE
        }

        #[inline]
        fn encode_into_array<Arg, R>(f: fn(Arg) -> R) -> js_sys::Uint32Array {
            let arr = js_sys::Uint32Array::new_with_length(Self::len() as u32);
            arr.copy_from(&Self::encode(f));
            arr
        }

        #[inline]
        const fn encode<Arg, R>(f: fn(Arg) -> R) -> [u32; Self::len()] {
            // Safety: Function pointer can safely become u32 array.
            unsafe {
                Self {
                    src: mem::transmute::<fn(Arg) -> R, fn()>(f),
                }
                .dst
            }
        }

        /// # Safety
        ///
        /// Undefined behavior if the given data is not a valid function pointer.
        //
        // Why we don't return `fn(Arg) -> R` like encode_into_array().
        // - Imagine we're returning `fn(Arg) -> R`.
        //   If caller designated `&i32` to `Arg` and `()` to `R`,
        //   then return type will be `fn(&'x i32)`, where 'x is defined by the caller.
        //   Then, caller can call `fn(&'x i32)` directly, but cannot do other things
        //   like pushing the function pointer into `Vec<for<'a> fn(&'a i32)>`.
        //   Because the Vec requires `for<'a>`, which is quite generic,
        //   but caller can't convert 'x, which is less generic, into `for<'a>`.
        // - Therefore, generic is not sufficient.
        #[inline]
        unsafe fn decode_from_array(arr: &js_sys::Uint32Array) -> fn() {
            let mut buf: [u32; Self::len()] = [0; Self::len()];
            arr.copy_to(&mut buf);
            Self::decode(buf)
        }

        /// # Safety
        ///
        /// Undefined behavior if the given data is not a valid function pointer.
        #[inline]
        const unsafe fn decode(encoded: [u32; Self::len()]) -> fn() {
            Self { dst: encoded }.src
        }
    }
}
