use super::task::{ParTask, Task};
use crate::{
    ds::prelude::*,
    ecs::{
        cmd::Command,
        worker::{Message, WorkerId},
    },
};
use crossbeam_deque as cb;
use std::{
    cell::Cell,
    fmt,
    marker::PhantomData,
    sync::{
        atomic::{AtomicBool, AtomicU32, Ordering},
        mpsc::{self, Receiver, RecvTimeoutError, Sender, TryRecvError},
        Arc, Mutex,
    },
    thread::{self, Thread},
    time::Duration,
};

#[derive(Debug)]
pub(crate) struct SubComm {
    /// Global task queue contains [`Task::System`] only.
    /// It works in spmc fashion and push/pop occurs as follows.
    /// - 'Push' occurs by main worker.
    /// - 'Pop' occurs by all sub workers.
    global: Arc<cb::Injector<Task>>,

    /// Local task queue contains [`Task::System`], [`Task::Parallel`], and
    /// [`Task::Future`].
    /// It works in spmc fashion and push/pop occurs as follows.
    /// - 'Push' occurs by sub worker.
    /// - 'Pop' occurs by both this sub worker and siblings via [`cb::Stealer`].
    local: cb::Worker<Task>,

    /// Sibling's pop-only local queues.  
    siblings: Arc<[cb::Stealer<Task>]>,

    /// Local future task queue contains [`Task::Future`] only.
    /// It works in mpmc fashion and push/pop occurs as follows.
    /// - 'Push' occurs by a thread that called the most inner future's poll().
    /// - 'Pop' occurs by each sub worker.
    //
    // `crossbeam::Worker<T>` is not a mpmc queue, so uses another `Injector`
    // instead. But if it causes some kind of performance issue, then consider
    // using another queue.
    futures: Arc<[cb::Injector<Task>]>,

    /// Channel sending messages to main worker.
    tx_msg: ParkingSender<Message>,

    /// Channel sending commands to main worker.
    tx_cmd: ParkingSender<Box<dyn Command>>,

    /// Signal to wake or block workers and some counts.
    signal: Arc<GlobalSignal>,

    /// Index to [`Self::siblings`], [`Self::futures`], and [`Self::signal`].
    wid: WorkerId,
}

impl SubComm {
    pub(super) fn with_len(
        global: &Arc<cb::Injector<Task>>,
        signal: &Arc<GlobalSignal>,
        tx_msg: &ParkingSender<Message>,
        tx_cmd: &ParkingSender<Box<dyn Command>>,
        len: usize,
    ) -> Vec<Self> {
        thread_local! {
            static WORKER_ID_GEN: Cell<u32> = const { Cell::new(0) };
        }

        // Local queues and stealers.
        let (locals, siblings): (Vec<_>, Vec<_>) = (0..len)
            .map(|_| {
                let local = cb::Worker::<Task>::new_lifo();
                let sibling = local.stealer();
                (local, sibling)
            })
            .unzip();
        let siblings: Arc<[cb::Stealer<Task>]> = siblings.into();

        // Local async queues.
        let asyncs: Arc<[cb::Injector<Task>]> = (0..len).map(|_| cb::Injector::new()).collect();

        locals
            .into_iter()
            .enumerate()
            .map(|(i, local)| {
                let id = WORKER_ID_GEN.get();
                WORKER_ID_GEN.set(id + 1);
                Self {
                    global: Arc::clone(global),
                    local,
                    siblings: Arc::clone(&siblings),
                    futures: Arc::clone(&asyncs),
                    tx_msg: tx_msg.clone(),
                    tx_cmd: tx_cmd.clone(),
                    wid: WorkerId::new(id, i as u32),
                    signal: Arc::clone(signal),
                }
            })
            .collect()
    }

    pub(super) fn signal(&self) -> &GlobalSignal {
        &self.signal
    }

    pub(super) const fn worker_id(&self) -> WorkerId {
        self.wid
    }

    pub(super) fn num_siblings(&self) -> usize {
        self.siblings.len()
    }

    pub(super) fn set_signal(&mut self, signal: Arc<GlobalSignal>) {
        self.signal = signal;
    }

    pub(super) fn wait(&self) {
        self.signal.add_idle_count();
        self.signal.sub().wait(self.wid.index());
        self.signal.sub_idle_count();
    }

    pub(super) fn wake_self(&self) {
        self.signal.sub().notify(self.wid.index());
    }

    pub(crate) fn send_message(&self, msg: Message) {
        self.tx_msg.send(msg).unwrap();
    }

    pub(crate) fn send_command(&self, cmd: Box<dyn Command>) {
        self.tx_cmd.send(cmd).unwrap();
    }

    pub(super) fn pop(&self) -> cb::Steal<Task> {
        if let Some(task) = self.pop_local() {
            cb::Steal::Success(task)
        } else {
            self.pop_future()
        }
    }

    pub(super) fn pop_local(&self) -> Option<Task> {
        self.local.pop()
    }

    pub(super) fn pop_future(&self) -> cb::Steal<Task> {
        loop {
            let steal = self.futures[self.wid.index()].steal();
            match &steal {
                cb::Steal::Retry => {}
                _ => return steal,
            }
        }
    }

    pub(super) fn push_parallel_task(&self, task: ParTask) {
        self.local.push(Task::Parallel(task));
    }

    pub(super) fn push_future_task(&self, handle: UnsafeFuture) {
        self.futures[self.wid.index()].push(Task::Future(handle));
    }

    pub(super) fn is_local_empty(&self) -> bool {
        self.local.is_empty()
    }

    pub(super) fn search(&self) -> cb::Steal<Task> {
        self.search_global()
            .or_else(|| self.search_sibling_locals())
            .or_else(|| self.search_futures())
    }

    pub(super) fn search_global(&self) -> cb::Steal<Task> {
        loop {
            let steal = self.global.steal_batch_and_pop(&self.local);
            match &steal {
                cb::Steal::Success(_task) => {
                    if !self.local.is_empty() {
                        self.signal.sub().notify_one();
                    }
                    return steal;
                }
                cb::Steal::Empty => break,
                cb::Steal::Retry => {}
            }
        }
        cb::Steal::Empty
    }

    pub(super) fn search_sibling_locals(&self) -> cb::Steal<Task> {
        for sibling in self
            .siblings
            .iter()
            .cycle()
            .skip(self.wid.index() + 1)
            .take(self.siblings.len() - 1)
        {
            loop {
                let steal = sibling.steal_batch_and_pop(&self.local);
                match &steal {
                    cb::Steal::Success(_task) => {
                        if !self.local.is_empty() {
                            self.signal.sub().notify_one();
                        }
                        return steal;
                    }
                    cb::Steal::Empty => break,
                    cb::Steal::Retry => {}
                }
            }
        }
        cb::Steal::Empty
    }

    pub(super) fn search_futures(&self) -> cb::Steal<Task> {
        for sibling in self
            .futures
            .iter()
            .cycle()
            .skip(self.wid.index())
            .take(self.futures.len())
        {
            loop {
                let steal = sibling.steal_batch_and_pop(&self.local);
                match &steal {
                    cb::Steal::Success(_task) => {
                        if !self.local.is_empty() {
                            self.signal.sub().notify_one();
                        }
                        return steal;
                    }
                    cb::Steal::Empty => break,
                    cb::Steal::Retry => {}
                }
            }
        }
        cb::Steal::Empty
    }
}

#[derive(Debug)]
pub(super) struct GlobalSignal {
    /// Handle of main worker.
    /// Sub workers can wake the main worker up through this handle.
    main: Thread,

    /// [`Signal`] for sub workers.
    /// Main or sub worker can wake up any sub worker through this signal.
    sub: Signal,

    /// Abort flag.
    /// This flag is written by main worker only.
    /// If this is true, sub workers will cancel out remaining tasks.
    is_abort: AtomicBool,

    /// Close flag.
    /// This flag is written by main worker only.
    /// If this is true, sub workers will be closed soon.
    is_close: AtomicBool,

    /// Number of open sub workers.
    /// This count is written by sub workers only.
    /// Main worker will make use of this count for making some decisions.
    open_cnt: AtomicU32,

    /// Number of idle(waiting) sub workers and future tasks.
    /// This count is written by sub workers only.
    /// Main worker will make use of this count for making some decisions.
    idle_fut_cnt: Mutex<IdleFutureCount>,
}

impl GlobalSignal {
    /// Some atomic counts are composed of 'target' and 'count' bits.
    /// 'target' bits are located at MSB, and 'count' bits are located at LSB.
    /// This shift is the offset bits of the 'target' bits from LSB.
    const TARGET_SHIFT: u32 = 16;

    /// Mask to filter 'target' bits out, so that we can get 'count' bits only.
    const COUNT_MASK: u32 = (1 << Self::TARGET_SHIFT) - 1;

    /// Mask to filter 'count' bits out, so that we can get 'target' bits only.
    /// Don't forget to r-shift on the filtered value to get 'target' number.
    const TARGET_MASK: u32 = !Self::COUNT_MASK;

    pub(super) const ANY_TARGET: u32 = u32::MAX;

    pub(super) fn new(sub_handles: Vec<Thread>) -> Self {
        let mut sub = Signal::default();
        sub.set_handles(sub_handles);

        Self {
            main: thread::current(),
            sub,
            is_abort: AtomicBool::new(false),
            is_close: AtomicBool::new(false),
            open_cnt: AtomicU32::new(0),
            idle_fut_cnt: Mutex::new(IdleFutureCount {
                idle: 0,
                fut: 0,
                notify: false,
                idle_target: 0,
                fut_target: 0,
            }),
        }
    }

    pub(super) fn sub(&self) -> &Signal {
        &self.sub
    }

    // === Methods related to abort flag ===

    pub(super) fn is_abort(&self) -> bool {
        self.is_abort.load(Ordering::Relaxed)
    }

    pub(super) fn set_abort(&self, is_abort: bool) {
        self.is_abort.store(is_abort, Ordering::Relaxed);
    }

    // === Methods related to close flag ===

    pub(super) fn is_close(&self) -> bool {
        self.is_close.load(Ordering::Relaxed)
    }

    pub(super) fn set_exit(&self, is_exit: bool) {
        self.is_close.store(is_exit, Ordering::Relaxed);
    }

    // === Methods related to open count ===

    pub(super) fn open_count(&self) -> u32 {
        self.open_cnt.load(Ordering::Relaxed) & Self::COUNT_MASK
    }

    pub(super) fn wait_open_count(&self, target: u32) {
        Self::wait_for_target(&self.open_cnt, target);
    }

    pub(super) fn add_open_count(&self) {
        let old = self.open_cnt.fetch_add(1, Ordering::Relaxed);
        Self::wake_by_target(&self.main, &self.open_cnt, old, 1);
    }

    pub(super) fn sub_open_count(&self) {
        let old = self.open_cnt.fetch_sub(1, Ordering::Relaxed);
        Self::wake_by_target(&self.main, &self.open_cnt, old, -1);
    }

    // === Methods related to idle & future count ===

    pub(super) fn idle_future_counts(&self) -> (u32, u32) {
        let IdleFutureCount { idle, fut, .. } = *self.idle_fut_cnt.lock().unwrap();
        (idle, fut)
    }

    pub(super) fn wait_idle_future_counts(&self, idle_target: u32, fut_target: u32) -> (u32, u32) {
        debug_assert!(
            idle_target != Self::ANY_TARGET || fut_target != Self::ANY_TARGET,
            "Both idle and future targets cannot be ANY at the same time"
        );

        // If the condition is already met, returns without blocking.
        let mut cnt = self.idle_fut_cnt.lock().unwrap();
        if (idle_target == Self::ANY_TARGET || cnt.idle == idle_target)
            && (fut_target == Self::ANY_TARGET || cnt.fut == fut_target)
        {
            return (cnt.idle, cnt.fut);
        }

        // Sets flag and targets.
        cnt.notify = true;
        cnt.idle_target = idle_target;
        cnt.fut_target = fut_target;
        drop(cnt);

        // Blocks current worker.
        loop {
            thread::park();
            let cnt = self.idle_fut_cnt.lock().unwrap();
            if !cnt.notify {
                return (cnt.idle, cnt.fut);
            }
        }
    }

    fn add_idle_count(&self) {
        self.modify_idle_count(1);
    }

    fn sub_idle_count(&self) {
        self.modify_idle_count(-1);
    }

    pub(super) fn add_future_count(&self) {
        self.modify_future_count(1);
    }

    pub(super) fn sub_future_count(&self) {
        self.modify_future_count(-1);
    }

    fn modify_idle_count(&self, delta: i32) {
        let mut cnt = self.idle_fut_cnt.lock().unwrap();
        cnt.idle = (cnt.idle as i32 + delta) as u32;
        if cnt.need_notify() {
            cnt.notify = false;
            self.main.unpark();
        }
    }

    fn modify_future_count(&self, delta: i32) {
        let mut cnt = self.idle_fut_cnt.lock().unwrap();
        cnt.fut = (cnt.fut as i32 + delta) as u32;
        if cnt.need_notify() {
            cnt.notify = false;
            self.main.unpark();
        }
    }

    fn wait_for_target(cnt: &AtomicU32, target: u32) {
        let target_bits = (!target) << Self::TARGET_SHIFT;
        let mut cur = cnt.load(Ordering::Relaxed);

        // Sets target bits or returns if it's not more required.
        loop {
            // If read value reached the target in this loop, returns.
            if cur == target {
                return;
            }

            // Tries to set target bits. If it succeeds, escapes this loop.
            if let Err(old) =
                cnt.compare_exchange(cur, cur | target_bits, Ordering::Relaxed, Ordering::Relaxed)
            {
                cur = old;
            } else {
                break;
            }
        }

        // We set the target bits. So waits for any sub worker to wake us up.
        while cnt.load(Ordering::Relaxed) != target {
            thread::park();
        }
    }

    fn wake_by_target(main: &Thread, cnt: &AtomicU32, old: u32, delta: i32) {
        let high = old & Self::TARGET_MASK;
        let low = old & Self::COUNT_MASK;
        let target = (!high) >> Self::TARGET_SHIFT;
        let cur = (low as i32 + delta) as u32;

        // We didn't reach the target? Someone who reach the target will wake
        // the main worker, so we're going to return.
        if target != cur {
            return;
        }

        // We reached the target, so we must wake the main worker up.
        // Let's unpark the main once we succeeds to erase target bits.
        let mut cur = high | cur;
        while (cur & Self::TARGET_MASK) != 0 {
            if let Err(old) = cnt.compare_exchange(
                cur,
                cur & (!Self::TARGET_MASK),
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                cur = old;
            } else {
                main.unpark();
                break;
            }
        }
    }
}

#[derive(Debug)]
struct IdleFutureCount {
    idle: u32,
    fut: u32,
    notify: bool,
    idle_target: u32,
    fut_target: u32,
}

impl IdleFutureCount {
    fn need_notify(&self) -> bool {
        self.notify
            && (self.idle_target == GlobalSignal::ANY_TARGET || self.idle == self.idle_target)
            && (self.fut_target == GlobalSignal::ANY_TARGET || self.fut == self.fut_target)
    }
}

pub(super) struct ParkingChannel<T>(PhantomData<T>);

impl<T> ParkingChannel<T> {
    pub(super) fn channel(_th: Thread) -> (ParkingSender<T>, ParkingReceiver<T>) {
        let (tx, rx) = mpsc::channel();
        (
            ParkingSender::new(tx, _th.clone()),
            ParkingReceiver::new(rx),
        )
    }
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

    pub(crate) fn send(&self, t: T) -> Result<(), std::sync::mpsc::SendError<T>> {
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

pub(crate) struct ParkingReceiver<T> {
    rx: Receiver<T>,

    /// Takes the next value out of the channel and holds it.
    /// to cooperate with `thread::park_timeout`.
    next: Cell<Option<T>>,
}

impl<T> fmt::Debug for ParkingReceiver<T> {
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

    pub(crate) fn has(&self) -> bool {
        if let Ok(value) = self.try_recv() {
            self.next.set(Some(value));
            true
        } else {
            false
        }
    }

    /// May return timeout error spuriously.
    //
    // Why `thread::park_timeout()` instead of `Receiver::recv_timeout()`?
    //
    // In web, we cannot get time, but `Receiver::recv_timeout()` tries
    // to get current time, so it fails to compile.
    // Fortunately, in nightly-2024-06-20, `thread::park_timeout()` is
    // implemented via wasm32::memory_atomic_wait32(), so it works.
    // See "nightly-2024-06-20-.../lib/rustlib/src/rust/library/std/src/sys/pal/wasm/atomics/futex.rs"
    pub(crate) fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
        let cur = if let Some(value) = self.next.take() {
            Ok(value)
        } else {
            thread::park_timeout(timeout);
            self.rx.try_recv().map_err(|err| match err {
                TryRecvError::Empty => RecvTimeoutError::Timeout,
                TryRecvError::Disconnected => RecvTimeoutError::Disconnected,
            })
        };

        self.next.set(self.rx.try_recv().ok());

        cur
    }

    pub(crate) fn try_recv(&self) -> Result<T, TryRecvError> {
        if let Some(value) = self.next.take() {
            Ok(value)
        } else {
            self.rx.try_recv()
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
        Future,
    }
}
