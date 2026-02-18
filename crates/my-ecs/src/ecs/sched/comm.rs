use super::task::{AsyncTask, ParTask, Task};
use crate::{
    cb_deque::{Injector, Steal, Stealer, Worker},
    ecs::{
        cmd::CommandObject,
        worker::{Message, WorkerId},
    },
    utils::ds::{Signal, UnsafeFuture},
};
use crossbeam_channel::{SendError, Sender, TryRecvError};
use my_utils::ds::SignalSlot;
use std::{
    cell::Cell,
    sync::{
        atomic::{AtomicBool, AtomicU32, Ordering},
        Arc, Mutex,
    },
    thread::{self, Thread},
};

thread_local! {
    pub(crate) static WORKER_ID_GEN: Cell<u32> = const { Cell::new(0) };
}

#[derive(Debug)]
pub(crate) struct SubComm {
    /// Global task queue contains [`Task::System`] only.
    ///
    /// It works in 'single producer multiple consumers' fashion and push/pop occurs as follows.
    /// - 'Push' occurs by main worker.
    /// - 'Pop' occurs by all sub workers.
    injector: Arc<Injector<Task>>,

    /// Local task queue contains [`Task::System`], [`Task::Parallel`], and [`Task::Future`].
    ///
    /// It works in 'single producer multiple consumers' fashion and push/pop occurs as follows.
    /// - 'Push' occurs by sub worker.
    /// - 'Pop' occurs by both this sub worker and siblings via [`Stealer`].
    local: Worker<Task>,

    /// Sibling's pop-only local queues.  
    siblings: Arc<[Stealer<Task>]>,

    /// Local future task queue contains [`Task::Future`] only.
    ///
    /// It works in 'multiple producers multiple consumers' fashion and push/pop occurs as follows.
    /// - 'Push' occurs by a thread that called the most inner future's poll().
    /// - 'Pop' occurs by each sub worker.
    //
    // `crossbeam::Worker<T>` is not a 'multiple producers multiple consumers' queue, so uses
    // another `Injector` instead. But if it causes some kind of performance issue, then consider
    // using another queue.
    futures: Arc<[Injector<Task>]>,

    /// Channel sending messages to main worker.
    tx_msg: ParkingSender<Message>,

    /// Channel sending commands to main worker.
    tx_cmd: CommandSender,

    /// Signal to wake or block workers and some counts.
    signal: Arc<GroupSignal>,

    /// Index to [`Self::siblings`], [`Self::futures`], and [`Self::signal`].
    wid: WorkerId,
}

impl SubComm {
    pub(super) fn with_len(
        group_index: u16,
        injector: &Arc<Injector<Task>>,
        signal: &Arc<GroupSignal>,
        tx_msg: &ParkingSender<Message>,
        tx_cmd: &CommandSender,
        len: usize,
    ) -> Vec<Self> {
        // Local queues and stealers.
        let (locals, siblings): (Vec<_>, Vec<_>) = (0..len)
            .map(|_| {
                let local = Worker::<Task>::new_lifo();
                let sibling = local.stealer();
                (local, sibling)
            })
            .unzip();
        let siblings: Arc<[Stealer<Task>]> = siblings.into();

        // Local async queues.
        let asyncs: Arc<[Injector<Task>]> = (0..len).map(|_| Injector::new()).collect();

        locals
            .into_iter()
            .enumerate()
            .map(|(worker_index, local)| {
                let id = WORKER_ID_GEN.with(Cell::get);
                WORKER_ID_GEN.with(|gen| gen.set(id + 1));
                Self {
                    injector: Arc::clone(injector),
                    local,
                    siblings: Arc::clone(&siblings),
                    futures: Arc::clone(&asyncs),
                    tx_msg: tx_msg.clone(),
                    tx_cmd: tx_cmd.clone(),
                    wid: WorkerId::new(id, group_index, worker_index as u16),
                    signal: Arc::clone(signal),
                }
            })
            .collect()
    }

    pub(crate) fn signal(&self) -> &GroupSignal {
        &self.signal
    }

    /// We can also get the worker id from [`WORKER_ID`](crate::ecs::sched::ctrl::WORKER_ID).
    pub(crate) fn worker_id(&self) -> WorkerId {
        let wid = self.maybe_uninit_worker_id();

        #[cfg(debug_assertions)]
        {
            use crate::ecs::sched::ctrl::WORKER_ID;

            assert_eq!(wid, WORKER_ID.with(Cell::get));
        }

        wid
    }

    pub(super) fn maybe_uninit_worker_id(&self) -> WorkerId {
        self.wid
    }

    pub(super) fn num_siblings(&self) -> usize {
        self.siblings.len()
    }

    pub(super) fn set_signal(&mut self, signal: Arc<GroupSignal>) {
        self.signal = signal;
    }

    pub(super) fn wait(&self) {
        self.signal.sub().wait(self.wid.worker_index() as usize);
    }

    pub(super) fn wake_self(&self) {
        self.signal
            .sub()
            .notify_try(self.wid.worker_index() as usize);
    }

    pub(crate) fn send_message(&self, msg: Message) {
        self.tx_msg.send(msg).unwrap();
    }

    pub(crate) fn send_command_or_cancel(&self, cmd: CommandObject) {
        self.tx_cmd.send_or_cancel(cmd);
    }

    pub(super) fn pop(&self) -> Steal<Task> {
        if let Some(task) = self.pop_local() {
            Steal::Success(task)
        } else {
            self.pop_future()
        }
    }

    pub(super) fn pop_local(&self) -> Option<Task> {
        self.local.pop()
    }

    pub(super) fn pop_future(&self) -> Steal<Task> {
        loop {
            let steal = self.futures[self.wid.worker_index() as usize].steal();
            match &steal {
                Steal::Retry => {}
                _ => return steal,
            }
        }
    }

    pub(super) fn push_parallel_task(&self, task: ParTask) {
        self.local.push(Task::Parallel(task));
    }

    pub(crate) fn push_future_task(&self, handle: UnsafeFuture) {
        let task = Task::Async(AsyncTask(handle));
        self.futures[self.wid.worker_index() as usize].push(task);
    }

    pub(crate) fn is_local_empty(&self) -> bool {
        self.local.is_empty()
    }

    pub(super) fn search(&self) -> Steal<Task> {
        self.search_injector()
            .or_else(|| self.search_sibling_locals())
            .or_else(|| self.search_futures())
    }

    pub(super) fn search_injector(&self) -> Steal<Task> {
        loop {
            let steal = self.injector.steal_batch_and_pop(&self.local);
            match &steal {
                Steal::Success(_task) => {
                    if !self.local.is_empty() {
                        self.signal.sub().notify_one();
                    }
                    return steal;
                }
                Steal::Empty => break,
                Steal::Retry => {}
            }
        }
        Steal::Empty
    }

    pub(super) fn search_sibling_locals(&self) -> Steal<Task> {
        for sibling in self
            .siblings
            .iter()
            .cycle()
            .skip(self.wid.worker_index() as usize + 1)
            .take(self.siblings.len() - 1)
        {
            loop {
                let steal = sibling.steal_batch_and_pop(&self.local);
                match &steal {
                    Steal::Success(_task) => {
                        if !(self.local.is_empty() && sibling.is_empty()) {
                            self.signal.sub().notify_one();
                        }
                        return steal;
                    }
                    Steal::Empty => break,
                    Steal::Retry => {}
                }
            }
        }
        Steal::Empty
    }

    pub(super) fn search_futures(&self) -> Steal<Task> {
        for sibling in self
            .futures
            .iter()
            .cycle()
            .skip(self.wid.worker_index() as usize)
            .take(self.futures.len())
        {
            loop {
                let steal = sibling.steal_batch_and_pop(&self.local);
                match &steal {
                    Steal::Success(_task) => {
                        if !(self.local.is_empty() && sibling.is_empty()) {
                            self.signal.sub().notify_one();
                        }
                        return steal;
                    }
                    Steal::Empty => break,
                    Steal::Retry => {}
                }
            }
        }
        Steal::Empty
    }
}

#[derive(Debug)]
pub(crate) struct GroupSignal {
    /// Handle of main worker.
    ///
    /// Sub workers can wake the main worker up through this handle.
    main: Thread,

    /// [`Signal`] for sub workers.
    ///
    /// Main or sub worker can wake up any sub worker through this signal.
    sub: Signal,

    /// Abort flag.
    ///
    /// This flag is written by main worker only. If this is true, sub workers will be closed soon.
    is_abort: AtomicBool,

    /// Number of open sub workers.
    ///
    /// This count is written by sub workers only. Main worker will make use of this count for
    /// making some decisions.
    open_cnt: AtomicU32,

    /// Number of working sub workers.
    ///
    /// This count is written by sub workers only. Main worker will make use of this count for
    /// making some decisions.
    work_cnt: AtomicU32,

    /// Number of running future tasks.
    ///
    /// This count is written by sub workers only. Main worker will make use of this count for
    /// making some decisions.
    fut_cnt: AtomicU32,
}

impl GroupSignal {
    pub(super) fn new(signal_slots: Vec<SignalSlot>) -> Self {
        Self {
            main: thread::current(),
            sub: Signal::new(signal_slots),
            is_abort: AtomicBool::new(false),
            open_cnt: AtomicU32::new(0),
            work_cnt: AtomicU32::new(0),
            fut_cnt: AtomicU32::new(0),
        }
    }

    pub(crate) fn sub(&self) -> &Signal {
        &self.sub
    }

    // === Methods related to ABORT flag ===

    pub(crate) fn is_abort(&self) -> bool {
        self.is_abort.load(Ordering::Relaxed)
    }

    pub(crate) fn set_abort(&self, is_abort: bool) {
        self.is_abort.store(is_abort, Ordering::Relaxed);
    }

    // === Methods related to OPEN count ===
    // OPEN count is wait-wake-able.

    pub(crate) fn open_count(&self) -> u32 {
        self.open_cnt.load(Ordering::Acquire)
    }

    pub(crate) fn wait_open_count(&self, target: u32) {
        while self.open_cnt.load(Ordering::Acquire) != target {
            thread::park();
        }
    }

    pub(crate) fn add_open_count(&self, value: u32) -> u32 {
        let old = self.open_cnt.fetch_add(value, Ordering::Release);
        self.main.unpark();
        old.wrapping_add(value)
    }

    pub(crate) fn sub_open_count(&self, value: u32) -> u32 {
        let old = self.open_cnt.fetch_sub(value, Ordering::Release);
        self.main.unpark();
        old.wrapping_sub(value)
    }

    // === Methods related to WORK count ===

    pub(crate) fn work_count(&self) -> u32 {
        self.work_cnt.load(Ordering::Acquire)
    }

    pub(crate) fn add_work_count(&self, value: u32) -> u32 {
        let old = self.work_cnt.fetch_add(value, Ordering::Release);
        old.wrapping_add(value)
    }

    pub(crate) fn sub_work_count(&self, value: u32) -> u32 {
        let old = self.work_cnt.fetch_sub(value, Ordering::Release);
        old.wrapping_sub(value)
    }

    // === Methods related to FUTURE count ===

    pub(crate) fn future_count(&self) -> u32 {
        self.fut_cnt.load(Ordering::Acquire)
    }

    pub(crate) fn add_future_count(&self, value: u32) -> u32 {
        let old = self.fut_cnt.fetch_add(value, Ordering::Release);
        old.wrapping_add(value)
    }

    pub(crate) fn sub_future_count(&self, value: u32) -> u32 {
        let old = self.fut_cnt.fetch_sub(value, Ordering::Release);
        old.wrapping_sub(value)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct CommandSender {
    inner: ParkingSender<CommandObject>,
    open: Arc<Mutex<bool>>,
}

impl CommandSender {
    pub(crate) fn send_or_cancel(&self, cmd: CommandObject) {
        if let Err(SendError(cmd)) = self.send(cmd) {
            cmd.cancel();
        }
    }

    fn send(&self, cmd: CommandObject) -> Result<(), SendError<CommandObject>> {
        let guard = self.open.lock().unwrap();
        if *guard {
            self.inner.send(cmd)
        } else {
            Err(SendError(cmd))
        }
    }
}

#[derive(Debug)]
pub(crate) struct CommandReceiver {
    inner: ParkingReceiver<CommandObject>,
    open: Arc<Mutex<bool>>,
}

impl CommandReceiver {
    pub(crate) fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub(crate) fn try_recv(&self) -> Result<CommandObject, TryRecvError> {
        self.inner.try_recv()
    }

    pub(crate) fn close(&self) {
        *self.open.lock().unwrap() = false;
    }
}

pub(crate) fn command_channel(th: Thread) -> (CommandSender, CommandReceiver) {
    let (tx, rx) = parking_channel(th);
    let open = Arc::new(Mutex::new(true));
    let c_open = Arc::clone(&open);

    (
        CommandSender { inner: tx, open },
        CommandReceiver {
            inner: rx,
            open: c_open,
        },
    )
}

pub(super) fn parking_channel<T>(th: Thread) -> (ParkingSender<T>, ParkingReceiver<T>) {
    let (tx, rx) = crossbeam_channel::unbounded();
    (ParkingSender::new(tx, th.clone()), ParkingReceiver::new(rx))
}

#[derive(Debug)]
pub(crate) struct ParkingSender<T> {
    tx: Sender<T>,
    th: Thread,
}

impl<T> ParkingSender<T> {
    pub(crate) const fn new(tx: Sender<T>, th: Thread) -> Self {
        Self { tx, th }
    }

    pub(crate) fn send(&self, t: T) -> Result<(), SendError<T>> {
        let res = self.tx.send(t);
        self.th.unpark();
        res
    }
}

impl<T> Clone for ParkingSender<T> {
    fn clone(&self) -> Self {
        Self {
            tx: self.tx.clone(),
            th: self.th.clone(),
        }
    }
}

#[cfg(not(debug_assertions))]
pub(crate) use parking_receiver_release::*;

#[cfg(debug_assertions)]
pub(crate) use parking_receiver_debug::*;

#[cfg(not(debug_assertions))]
mod parking_receiver_release {
    use crossbeam_channel::{Receiver, RecvTimeoutError, TryRecvError};
    use std::{cell::Cell, fmt, thread, time::Duration};

    pub(crate) struct ParkingReceiver<T> {
        rx: Receiver<T>,

        /// Takes the next value out of the channel and holds it to cooperate with
        /// `thread::park_timeout`.
        next: Cell<Option<T>>,
    }

    impl<T> std::fmt::Debug for ParkingReceiver<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("ParkingReceiver")
                .field("rx", &self.rx)
                .finish_non_exhaustive()
        }
    }

    impl<T> ParkingReceiver<T> {
        pub(crate) const fn new(rx: Receiver<T>) -> Self {
            Self {
                rx,
                next: Cell::new(None),
            }
        }

        pub(crate) fn is_empty(&self) -> bool {
            if let Ok(value) = self.try_recv() {
                self.next.set(Some(value));
                false
            } else {
                true
            }
        }

        pub(crate) fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
            if let Ok(value) = self.try_recv() {
                Ok(value)
            } else {
                thread::park_timeout(timeout);
                self.rx.try_recv().map_err(|err| match err {
                    TryRecvError::Empty => RecvTimeoutError::Timeout,
                    TryRecvError::Disconnected => RecvTimeoutError::Disconnected,
                })
            }
        }

        pub(crate) fn wait_timeout(&self, timeout: Duration) {
            if let Ok(value) = self.try_recv() {
                self.next.set(Some(value));
            } else {
                thread::park_timeout(timeout);
            }
        }

        pub(crate) fn try_recv(&self) -> Result<T, TryRecvError> {
            if let Some(value) = self.next.take() {
                Ok(value)
            } else {
                self.rx.try_recv()
            }
        }
    }
}

#[cfg(debug_assertions)]
mod parking_receiver_debug {
    use crossbeam_channel::{Receiver, RecvTimeoutError, TryRecvError};
    use std::{
        cell::{RefCell, RefMut},
        collections::VecDeque,
        thread,
        time::Duration,
    };

    #[derive(Debug)]
    pub(crate) struct ParkingReceiver<T> {
        rx: Receiver<T>,
        buf: RefCell<VecDeque<T>>,
    }

    impl<T> ParkingReceiver<T> {
        pub(crate) fn new(rx: Receiver<T>) -> Self {
            Self {
                rx,
                buf: RefCell::new(VecDeque::new()),
            }
        }

        pub(crate) fn is_empty(&self) -> bool {
            if let Ok(value) = self.try_recv() {
                self.buf.borrow_mut().push_front(value);
                false
            } else {
                true
            }
        }

        /// May return timeout error spuriously.
        //
        // Why `thread::park_timeout()` instead of `Receiver::recv_timeout()`?
        //
        // In web, we cannot get time, but `Receiver::recv_timeout()` tries to get current time, so
        // it fails to compile. Fortunately, in nightly-2024-06-20, `thread::park_timeout()` is
        // implemented via wasm32::memory_atomic_wait32(), so it works.
        // See "nightly-2024-06-20-.../lib/rustlib/src/rust/library/std/src/sys/pal/wasm/atomics/
        // futex.rs"
        pub(crate) fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
            if let Ok(value) = self.try_recv() {
                Ok(value)
            } else {
                thread::park_timeout(timeout);
                self.rx.try_recv().map_err(|err| match err {
                    TryRecvError::Empty => RecvTimeoutError::Timeout,
                    TryRecvError::Disconnected => RecvTimeoutError::Disconnected,
                })
            }
        }

        /// Blocks until a message arrives through the channel.
        ///
        /// If there is arleady a received message, returns immediately. Otherwise, blocks for the
        /// given duration, but it may return spuriously.
        ///
        /// Also note that this method doesn't consume any messages. You will get the message
        /// through other receving methods.
        pub(crate) fn wait_timeout(&self, timeout: Duration) {
            if let Ok(value) = self.try_recv() {
                self.buf.borrow_mut().push_front(value);
            } else {
                thread::park_timeout(timeout);
            }
        }

        pub(crate) fn try_recv(&self) -> Result<T, TryRecvError> {
            if let Some(value) = self.buf.borrow_mut().pop_front() {
                Ok(value)
            } else {
                self.rx.try_recv()
            }
        }

        #[allow(unused)]
        pub(crate) fn buffer(&self) -> RefMut<'_, VecDeque<T>> {
            let mut buf = self.buf.borrow_mut();
            while let Ok(value) = self.rx.try_recv() {
                buf.push_back(value);
            }
            buf
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub(crate) use web::*;

#[cfg(target_arch = "wasm32")]
mod web {
    use super::*;
    use crate::ecs::sys::system::SystemId;

    thread_local! {
        /// Per-thread work that the thread is trying to do.
        pub(crate) static WORK_ID: Cell<WorkId> = const {
            Cell::new(WorkId {
                wid: WorkerId::dummy(),
                sid: SystemId::dummy(),
                kind: TaskKind::System,
            })
        };
    }

    #[derive(Debug, Clone, Copy)]
    pub(crate) struct WorkId {
        pub(crate) wid: WorkerId,
        pub(crate) sid: SystemId,
        pub(crate) kind: TaskKind,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum TaskKind {
        System,
        Parallel,
        Async,
    }
}
