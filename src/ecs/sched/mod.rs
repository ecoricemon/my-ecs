pub mod par;

pub mod prelude {
    #[cfg(target_arch = "wasm32")]
    pub use super::web::web_panic_hook;
    pub use super::SubContext;
}

use super::{
    cache::{CacheItem, RefreshCacheStorage},
    cmd::Command,
    sys::{
        request::SystemBuffer,
        system::{Invoke, SystemCycleIter, SystemData, SystemGroup, SystemId},
    },
    wait::WaitQueues,
    worker::{Message, PanicMessage, Work, WorkerIndex},
};
use crate::ds::prelude::*;
use crossbeam_deque as cb;
use par::FnContext;
use std::{
    any::Any,
    cell::{Cell, UnsafeCell},
    collections::{HashSet, VecDeque},
    hash::BuildHasher,
    marker::{PhantomData, PhantomPinned},
    mem,
    pin::Pin,
    ptr::NonNull,
    sync::{
        atomic::{self, AtomicI32, Ordering},
        mpsc::{self, Receiver, Sender},
        Arc, Condvar, Mutex, MutexGuard,
    },
    thread::{self, Thread},
    time::Duration,
};

#[derive(Debug)]
pub(super) struct Scheduler<S> {
    waits: WaitQueues<S>,

    /// System run history.
    run_hist: HashSet<SystemId, S>,

    /// A list holding pending tasks due to data dependency.
    pending: Pending<S>,

    cx: MainContext,
}

impl<S> Scheduler<S>
where
    S: BuildHasher + Default,
{
    const RX_CHANNEL_TIMEOUT: Duration = Duration::from_secs(u64::MAX);

    pub(super) fn new() -> Self {
        Self {
            waits: WaitQueues::new(),
            run_hist: HashSet::default(),
            pending: Pending::new(),
            cx: MainContext::new(),
        }
    }

    pub(super) fn get_run_history(&self) -> &HashSet<SystemId, S> {
        &self.run_hist
    }

    pub(super) fn get_wait_queues(&mut self) -> &mut WaitQueues<S> {
        &mut self.waits
    }

    pub(super) fn open_workers<W>(&mut self, workers: &mut [W])
    where
        W: Work,
    {
        // Extends sub context array if needed.
        self.cx.extend_sub(workers.len());

        for (i, worker) in workers.iter_mut().enumerate() {
            self.open_worker(i, worker, SubState::Open);
        }

        // Waits for all sub workers to be open.
        while self.cx.open < workers.len() {
            if let Ok(msg) = self.cx.rx_msg.recv_timeout(Self::RX_CHANNEL_TIMEOUT) {
                debug_assert_eq!(
                    mem::discriminant(&msg),
                    mem::discriminant(&Message::Open(WorkerIndex::new(0)))
                );
                self.cx.open += 1;
            }
        }
    }

    fn open_worker<W>(&mut self, i: usize, worker: &mut W, state: SubState)
    where
        W: Work,
    {
        // Sets sub state first.
        self.cx.sub_cxs[i].as_mut().set_state(state);

        let ptr = self.cx.ptr_sub(i);
        // Safety: The pointer won't be aliased and they will be valid
        // during scheduling.
        let ptr = unsafe {
            let ptr = NonNullExt::new_unchecked(ptr.cast_mut());
            ManagedConstPtr::new(ptr)
        };
        let must_true = worker.unpark(ptr);
        assert!(must_true);
    }

    pub(super) fn close_workers<W>(&mut self, workers: &mut [W])
    where
        W: Work,
    {
        // If there are open workers, closes them.
        if self.cx.open > 0 {
            self.close_workers_inner(|this, msg| {
                debug_assert_eq!(
                    mem::discriminant(&msg),
                    mem::discriminant(&Message::Closed(WorkerIndex::new(0)))
                );
                this.cx.open -= 1;
            });
        }

        // Unfortunately, worker doesn't own `SubContext`.
        // It actually belongs to main thread, and worker uses its pointer.
        // Therefore, when the main thread received `Closed`,
        // It can destroy `SubContext` before `send()` is not fully finished.
        // So we need additional safety gadget like this.
        while self.cx.injector.closed.load(Ordering::Relaxed) < workers.len() as i32 {
            thread::yield_now();
        }
        self.cx.injector.closed.store(0, Ordering::Relaxed);

        // Clears system run history.
        self.run_hist.clear();

        // Parks workers.
        for worker in workers.iter_mut() {
            let must_true = worker.park();
            assert!(must_true);
        }

        #[cfg(debug_assertions)]
        self.validate_clean();
    }

    fn close_workers_inner<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Self, Message),
    {
        let mut status = self.cx.get_schedule_status();
        status.is_exit = true;
        self.cx.injector.signal_to_sub.notify_all();
        drop(status);

        // Waits for all sub workers to be closed.
        while self.cx.open > 0 {
            if let Ok(msg) = self.cx.rx_msg.recv_timeout(Self::RX_CHANNEL_TIMEOUT) {
                f(self, msg);
            }
        }

        let mut status = self.cx.get_schedule_status();
        status.is_exit = false;
        drop(status);
    }

    /// Schedules all systems(tasks).
    pub(super) fn execute<W>(
        &mut self,
        sgroup: &mut SystemGroup<S>,
        workers: &mut [W],
        cache: &mut RefreshCacheStorage<S>,
        dedi: &HashSet<SystemId, S>,
    ) where
        W: Work,
    {
        self.pending.limit = workers.len();
        let mut state = MainState::Look;
        let mut cycle = sgroup.get_active_mut().iter_begin();
        let mut panicked = Vec::new();

        loop {
            match state {
                MainState::Look => {
                    state = self.look(&cycle, workers.len());
                }
                MainState::Pick => {
                    let success = self.pick(&mut cycle, dedi, cache);
                    if success {
                        state = MainState::Look;
                    } else {
                        state = MainState::Wait;
                    }
                }
                MainState::Work => {
                    self.work();
                    state = MainState::Look;
                }
                MainState::Wait => {
                    self.wait(&mut cycle, cache, &mut panicked, workers);
                    state = MainState::Look;
                }
                MainState::Exit => {
                    self.exit(&mut cycle, cache, &mut panicked, workers);
                    break;
                }
            }
        }

        // If some systems panicked during cycle, gives them poison.
        drop(cycle);
        while let Some((sid, payload)) = panicked.pop() {
            sgroup.poison(&sid, payload).unwrap();
        }

        // Removes expired systems.
        sgroup.tick();
    }

    pub(super) fn consume_commands<F>(&self, mut f: F)
    where
        F: FnMut(Box<dyn Command>),
    {
        while let Ok(cmd) = self.cx.rx_cmd.try_recv() {
            f(cmd);
        }
    }

    fn look(&mut self, cycle: &SystemCycleIter<'_, S>, worker_len: usize) -> MainState {
        let is_pending_normal_empty = self.pending.normal.is_occupied_empty();
        let is_pending_dedi_empty = self.pending.dedi.is_occupied_empty();
        let ready_normal_len = self.cx.get_ready_queue().len();
        let is_ready_dedi_empty = self.cx.dedi.is_empty();
        let cycle_cur = cycle.position();

        if ready_normal_len > worker_len && !is_ready_dedi_empty {
            MainState::Work
        } else if !cycle_cur.is_end() {
            MainState::Pick
        } else if !is_ready_dedi_empty {
            MainState::Work
        } else if ready_normal_len > 0 || !is_pending_normal_empty || !is_pending_dedi_empty {
            MainState::Wait
        } else {
            MainState::Exit
        }
    }

    fn pick(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        dedi: &HashSet<SystemId, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
    ) -> bool {
        // Takes out one system from the cycle list.
        let sdata = cycle.get().unwrap();
        let sid = sdata.id();
        let is_dedi = dedi.contains(&sid);

        // If there's no data dependency, we can push it in ready queue.
        if let Some(cache) = Self::try_update_task(&mut self.waits, sdata, cache) {
            self.run_hist.insert(sid);
            Self::push_ready_system(&mut self.cx, sdata, cache, is_dedi);
            cycle.next();
            true
        }
        // Data dependency detected, then tries to push it in pending list.
        else if self.pending.try_push(cycle.position(), is_dedi) {
            self.run_hist.insert(sid);
            cycle.next();
            true
        }
        // Pending list is full now, then just wait.
        else {
            false
        }
    }

    fn work(&mut self) {
        // Takes out one system from ready queue.
        let task = self.cx.dedi.pop_front().unwrap();

        // TODO: handle panic?
        match task {
            Task::Sys(task) => {
                let _ = task.execute();
            }
            Task::Par(_) => unreachable!("main thread cannot do parallel tasks"),
        }
    }

    fn wait<W>(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
        workers: &mut [W],
    ) where
        W: Work,
    {
        // Waits for message from sub workers.
        if let Ok(msg) = self.cx.rx_msg.recv_timeout(Self::RX_CHANNEL_TIMEOUT) {
            self.handle_message(msg, cycle, cache, panicked, workers);
        }
        // Optimistically consumes messages as many as possible.
        while let Ok(msg) = self.cx.rx_msg.try_recv() {
            self.handle_message(msg, cycle, cache, panicked, workers);
        }
    }

    fn exit<W>(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
        workers: &mut [W],
    ) where
        W: Work,
    {
        // Processes remain messages while waiting for all sub workers to be closed.
        self.close_workers_inner(|this, msg| {
            this.handle_message(msg, cycle, cache, panicked, workers);
        });
    }

    fn handle_message<W>(
        &mut self,
        msg: Message,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
        workers: &mut [W],
    ) where
        W: Work,
    {
        match msg {
            Message::Open(_widx) => {
                self.cx.open += 1;
            }
            Message::Closed(_widx) => {
                self.cx.open -= 1;
            }
            Message::Fin(_widx, sid) => {
                let cache = cache.get(&sid).unwrap();
                self.waits.dequeue(&cache.get_wait_indices());
            }
            Message::Panic(msg) => {
                self.panic_helper(cache, panicked, msg, workers);
            }
        };

        self.pending_to_ready(cycle, cache, true);
        self.pending_to_ready(cycle, cache, false);
    }

    fn pending_to_ready(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
        is_dedi: bool,
    ) {
        let pending = if is_dedi {
            &mut self.pending.dedi
        } else {
            &mut self.pending.normal
        };
        let mut cur = pending.get_first_position();

        while let Some((next, &cycle_pos)) = pending.iter_next(cur) {
            let sdata = cycle.get_at(cycle_pos).unwrap();
            if let Some(cache) = Self::try_update_task(&mut self.waits, sdata, cache) {
                pending.remove(&cycle_pos);
                Self::push_ready_system(&mut self.cx, sdata, cache, is_dedi);
            }
            cur = next;
        }
    }

    fn push_ready_system(
        cx: &mut MainContext,
        sdata: &mut SystemData,
        cache: &mut CacheItem,
        is_dedi: bool,
    ) {
        // Safety: Scheduler guarantees those pointers will be used in the worker only.
        let task = unsafe {
            Task::Sys(SysTask {
                invoker: ManagedMutPtr::new(sdata.task_ptr()),
                buf: ManagedMutPtr::new(cache.request_buffer_ptr()),
                sid: sdata.id(),
            })
        };
        cx.push(task, is_dedi);
    }

    fn panic_helper<W>(
        &mut self,
        cache: &mut RefreshCacheStorage<S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
        msg: PanicMessage,
        _workers: &mut [W],
    ) where
        W: Work,
    {
        if msg.unrecoverable {
            panic!("unrecoverable");
        }

        let cache = {
            #[cfg(not(target_arch = "wasm32"))]
            {
                cache.get(&msg.sid).unwrap()
            }

            // In web, buffer is not released by [`BufferCleaner`] because
            // wasm-bindgen make it abort instead of unwinding stack.
            // So, we need to release it manually.
            //
            // [`BufferCleaner`]: crate::ecs::sys::request::BufferCleaner
            #[cfg(target_arch = "wasm32")]
            {
                let mut cache = cache.get_mut(&msg.sid).unwrap();
                let buf = cache.get_request_buffer_mut();
                buf.clear();
                cache
            }
        };

        self.waits.dequeue(&cache.get_wait_indices());
        panicked.push((msg.sid, msg.payload));

        #[cfg(target_arch = "wasm32")]
        {
            // The worker must be closed without notification.
            // Re-open it with `Search` state so that it can
            // empty its local queue.
            let i = msg.widx.into_inner();
            self.open_worker(i, &mut _workers[i], SubState::Search);
        }
    }

    /// Determines if the system(task) is runnable,
    /// which means there's no data dependency at the moment.
    /// If it's runnable, the system's cached buffer is updated and then returned.
    fn try_update_task<'a>(
        waits: &mut WaitQueues<S>,
        sdata: &mut SystemData,
        cache: &'a mut RefreshCacheStorage<S>,
    ) -> Option<&'a mut CacheItem> {
        let sid = sdata.id();
        let mut cache = cache.get_mut(&sid).unwrap();
        let (wait, retry) = cache.get_wait_retry_indices_mut();
        if waits.enqueue(&wait, retry) {
            // Before we send the data, we need to update(re-borrow) it.
            drop(wait);
            Some(cache.refresh())
        } else {
            None
        }
    }

    #[cfg(debug_assertions)]
    fn validate_clean(&self) {
        // No pending tasks.
        assert_eq!(0, self.pending.normal.len_occupied());
        assert_eq!(0, self.pending.dedi.len_occupied());

        // Validates main and sub contexts.
        self.cx.validate_clean();

        // No waiting request. Takes O(n).
        assert!(self.waits.is_all_queue_empty());
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MainState {
    Look,
    Pick,
    Work,
    Wait,
    Exit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubState {
    Open,
    Wait,
    Search,
    Work,
    Close,
}

#[derive(Debug)]
struct Pending<S> {
    /// Pending *normal* system positions in a system cycle.
    normal: SetValueList<ListPos, S>,

    /// Pending *dedicated* system positions in a system cycle.
    dedi: SetValueList<ListPos, S>,

    /// Maximum number of pending *normal* or *dedicated* systems.
    limit: usize,
}

impl<S> Pending<S>
where
    S: BuildHasher + Default,
{
    const DEFAULT_LIMIT: usize = 1;

    fn new() -> Self {
        Self {
            normal: SetValueList::new(ListPos::end()),
            dedi: SetValueList::new(ListPos::end()),
            limit: Self::DEFAULT_LIMIT,
        }
    }

    fn try_push(&mut self, pos: ListPos, is_dedi: bool) -> bool {
        let list = if is_dedi {
            &mut self.dedi
        } else {
            &mut self.normal
        };
        if list.len_occupied() < self.limit {
            list.push_back(pos);
            true
        } else {
            false
        }
    }
}

#[derive(Debug)]
struct MainContext {
    /// Number of open sub workers.
    open: usize,

    /// Each sub worker has its own context.
    sub_cxs: Vec<Pin<Box<SubContext>>>,

    /// Local queue's stealers.
    /// Each sub worker will own the whole stealers so that it can steal
    /// task from any of local queues.
    stealers: Arc<[cb::Stealer<Task>]>,

    /// Ready normal tasks.
    injector: Arc<MainInjector>,

    /// Ready dedicated tasks.
    dedi: VecDeque<Task>,

    /// Channel receving messages from sub workers.
    rx_msg: ParkingReceiver<Message>,

    /// Channel receving commands from sub workers.
    rx_cmd: ParkingReceiver<Box<dyn Command>>,

    /// This will be cloned and distributed to sub workers.
    _tx_msg: ParkingSender<Message>,
    _tx_cmd: ParkingSender<Box<dyn Command>>,
}

impl MainContext {
    fn new() -> Self {
        let (_tx_msg, rx_msg) = ParkingChannel::channel(thread::current());
        let (_tx_cmd, rx_cmd) = ParkingChannel::channel(thread::current());

        Self {
            open: 0,
            sub_cxs: Vec::new(),
            stealers: [].into(),
            injector: Arc::new(MainInjector::new()),
            dedi: VecDeque::new(),
            rx_msg,
            rx_cmd,
            _tx_msg,
            _tx_cmd,
        }
    }

    fn extend_sub(&mut self, new_len: usize) {
        if new_len <= self.len_sub() {
            return;
        }

        // Creates new local queues and stealers.
        let range = self.len_sub()..new_len;
        let (new_locals, mut new_stealers): (Vec<_>, Vec<_>) = range
            .map(|_| {
                let local = cb::Worker::<Task>::new_lifo();
                let stealer = local.stealer();
                (local, stealer)
            })
            .unzip();

        // Merges old and new stealers and set it to all sub contexts.
        let mut stealers = Vec::with_capacity(new_len);
        stealers.extend_from_slice(&self.stealers);
        stealers.append(&mut new_stealers);
        self.stealers = stealers.into();
        for cx in self.sub_cxs.iter_mut() {
            cx.as_mut().set_siblings(Arc::clone(&self.stealers));
        }

        // Extends sub context array with new contexts.
        for local in new_locals {
            let sub_cx = SubContext {
                start: SubState::Open,
                widx: WorkerIndex::new(self.len_sub()),
                local,
                siblings: Arc::clone(&self.stealers),
                injector: Arc::clone(&self.injector),
                tx_msg: self._tx_msg.clone(),
                tx_cmd: self._tx_cmd.clone(),
                _pin: PhantomPinned,
            };
            self.sub_cxs.push(Box::pin(sub_cx));
        }
    }

    fn len_sub(&self) -> usize {
        self.sub_cxs.len()
    }

    fn ptr_sub(&self, i: usize) -> *const SubContext {
        let sub_cx = &self.sub_cxs[i];
        sub_cx.as_ref().get_ref() as *const _
    }

    fn get_ready_queue(&self) -> &cb::Injector<Task> {
        &self.injector.queue
    }

    fn get_schedule_status(&self) -> MutexGuard<'_, ScheduleStatus> {
        self.injector.status.lock().unwrap()
    }

    fn push(&mut self, task: Task, is_dedi: bool) {
        if is_dedi {
            self.dedi.push_back(task);
        } else {
            self.injector.queue.push(task);
            let mut status = self.injector.status.lock().unwrap();
            status.has_ready_task = true;
            self.injector.signal_to_sub.notify_one();
        }
    }

    #[cfg(debug_assertions)]
    fn validate_clean(&self) {
        // Validates all sub contexts.
        for sub_cx in self.sub_cxs.iter() {
            sub_cx.validate_clean();
        }

        // Are all stealers empty?
        assert!(self.stealers.iter().all(|stealer| stealer.is_empty()));

        // Is normal ready queue empty?
        assert!(self.injector.queue.is_empty());

        // Is dedicated ready queue empty?
        assert!(self.dedi.is_empty());

        // Is status in initial state?
        let status = self.injector.status.lock().unwrap();
        assert!(!status.has_ready_task);
        assert!(!status.is_exit);

        // Is receiving channel empty?
        match self.rx_msg.try_recv() {
            Err(std::sync::mpsc::TryRecvError::Empty) => {}
            Ok(msg) => panic!("unexpected remaining msg in channel: {msg:?}"),
            Err(err) => panic!("unexpected error from channel: {err:?}"),
        }
    }
}

thread_local! {
    pub(super) static SUB_CONTEXT: Cell<NonNullExt<SubContext>> = const {
        Cell::new(NonNullExt::dangling())
    };
}

#[derive(Debug)]
pub struct SubContext {
    /// Starting state.
    start: SubState,

    /// Sub worker index.
    widx: WorkerIndex,

    /// Sub worker's local queue.
    local: cb::Worker<Task>,

    /// Stealers of other sub worker's local queues.
    siblings: Arc<[cb::Stealer<Task>]>,

    /// Main(global) queue.
    injector: Arc<MainInjector>,

    /// Channel sending messages to main thread.
    tx_msg: ParkingSender<Message>,

    /// Channel sending commands to main thread.
    tx_cmd: ParkingSender<Box<dyn Command>>,

    _pin: PhantomPinned,
}

impl SubContext {
    pub fn execute(ptr: ManagedConstPtr<Self>) {
        SUB_CONTEXT.set(ptr.inner());

        let this = {
            #[cfg(not(all(debug_assertions, target_arch = "wasm32")))]
            {
                &*ptr
            }

            // In web and debug mode, drops `ManagedMutPtr` first
            // as a preparation of unexpected panic.
            #[cfg(all(debug_assertions, target_arch = "wasm32"))]
            ptr.into_ref()
        };

        // Run
        let mut state = this.start;
        let mut steal = cb::Steal::Empty;
        loop {
            match state {
                SubState::Open => {
                    this.open();
                    state = SubState::Wait;
                }
                SubState::Wait => {
                    let go = this.wait();
                    state = if go {
                        SubState::Search
                    } else {
                        SubState::Close
                    };
                }
                SubState::Search => {
                    steal = this.search();
                    let found = steal.is_success();
                    state = if found {
                        SubState::Work
                    } else {
                        SubState::Wait
                    };
                }
                SubState::Work => {
                    this.work(&mut steal);
                    state = SubState::Search;
                }
                SubState::Close => {
                    // In debug mode, drops `ManagedMutPtr` before
                    // we notify closed status to main thread.
                    #[cfg(all(debug_assertions, not(target_arch = "wasm32")))]
                    let this = ptr.into_ref();

                    this.close();
                    break;
                }
            }
        }
    }

    pub(super) fn send_command(&self, cmd: Box<dyn Command>) {
        self.tx_cmd.send(cmd).unwrap();
    }

    fn open(&self) {
        // Notifies open to main thread.
        self.tx_msg.send(Message::Open(self.widx)).unwrap();
    }

    fn close(&self) {
        // Notifies closed to main thread.
        self.tx_msg.send(Message::Closed(self.widx)).unwrap();

        // We need an extra closing check to drop `SubContext` safely.
        // See `MainContext::exit()` for more info.
        self.injector.closed.fetch_add(1, Ordering::Release);
    }

    fn wait(&self) -> bool {
        // Waits for ready tasks or exit signal.
        let mut status = self.injector.status.lock().unwrap();
        while !status.has_ready_task && !status.is_exit {
            status = self.injector.signal_to_sub.wait(status).unwrap();
        }
        status.has_ready_task = false;

        !status.is_exit
    }

    fn search(&self) -> cb::Steal<Task> {
        self.search_main().or_else(|| self.search_siblings())
    }

    fn search_main(&self) -> cb::Steal<Task> {
        loop {
            let steal = self.injector.queue.steal_batch_and_pop(&self.local);
            match &steal {
                cb::Steal::Success(_task) => {
                    self.injector.signal_to_sub.notify_one();
                    return steal;
                }
                cb::Steal::Empty => return steal,
                cb::Steal::Retry => {}
            }
        }
    }

    fn search_siblings(&self) -> cb::Steal<Task> {
        for sibling in self
            .siblings
            .iter()
            .cycle()
            .skip(self.widx.into_inner() + 1)
            .take(self.siblings.len() - 1)
        {
            loop {
                let steal = sibling.steal_batch_and_pop(&self.local);
                match &steal {
                    cb::Steal::Success(_task) => {
                        self.injector.signal_to_sub.notify_one();
                        return steal;
                    }
                    cb::Steal::Empty => break,
                    cb::Steal::Retry => {}
                }
            }
        }

        cb::Steal::Empty
    }

    fn work(&self, steal: &mut cb::Steal<Task>) {
        loop {
            match mem::replace(steal, cb::Steal::Empty) {
                cb::Steal::Success(cur) => match cur {
                    Task::Sys(task) => {
                        self.work_for_systask(task);
                    }
                    Task::Par(task) => {
                        self.work_for_partask(task);
                    }
                },
                cb::Steal::Empty => break,
                cb::Steal::Retry => {}
            }

            if let Some(next) = self.local.pop() {
                *steal = cb::Steal::Success(next);
            }
        }
    }

    fn work_for_systask(&self, task: SysTask) {
        let sid = task.sid;

        // In web, panic is normally aborted, but we can detect
        // whether or not panic has been happened through panic hook.
        // We write `WorkId` to thread local variable to be used in
        // panic hook in order to identify where the panic occured.
        #[cfg(target_arch = "wasm32")]
        WORK_ID.set(WorkId {
            widx: self.widx,
            sid,
            is_par: false,
        });

        let resp = match task.execute() {
            Ok(_) => Message::Fin(self.widx, sid),
            Err(payload) => Message::Panic(PanicMessage {
                widx: self.widx,
                sid,
                payload,
                unrecoverable: false,
            }),
        };

        self.tx_msg.send(resp).unwrap();
    }

    fn work_for_partask(&self, task: ParTask) {
        // Like in `work_for_systask()`, sets `WorkId`.
        // But note that panics in parallel tasks cannot be recovered.
        // It will result in panic in main thread.
        #[cfg(target_arch = "wasm32")]
        WORK_ID.set(WorkId {
            widx: self.widx,
            sid: SystemId::dummy(),
            is_par: true,
        });

        task.execute(FnContext::MIGRATED);
    }

    fn set_siblings(self: Pin<&mut Self>, siblings: Arc<[cb::Stealer<Task>]>) {
        // Safety: We do not move self.
        unsafe {
            let this = self.get_unchecked_mut();
            this.siblings = siblings;
        }
    }

    fn set_state(self: Pin<&mut Self>, state: SubState) {
        // Safety: We do not move self.
        unsafe {
            let this = self.get_unchecked_mut();
            this.start = state;
        }
    }

    #[cfg(debug_assertions)]
    fn validate_clean(&self) {
        // Is local queue empty?
        assert!(self.local.is_empty());
    }
}

#[derive(Debug)]
struct MainInjector {
    queue: cb::Injector<Task>,
    signal_to_sub: Condvar,
    status: Mutex<ScheduleStatus>,
    closed: AtomicI32,
}

impl MainInjector {
    fn new() -> Self {
        Self {
            queue: cb::Injector::new(),
            signal_to_sub: Condvar::new(),
            status: Mutex::new(ScheduleStatus::new()),
            closed: AtomicI32::new(0),
        }
    }
}

#[derive(Debug)]
struct ScheduleStatus {
    has_ready_task: bool,
    is_exit: bool,
}

impl ScheduleStatus {
    const fn new() -> Self {
        Self {
            has_ready_task: false,
            is_exit: false,
        }
    }
}

#[derive(Debug)]
enum Task {
    Sys(SysTask),
    Par(ParTask),
}

impl Task {
    const fn id(&self) -> TaskId {
        match self {
            Self::Sys(task) => task.id(),
            Self::Par(task) => task.id(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TaskId {
    Sys(SystemId),
    Par(ParTask),
}

#[derive(Debug)]
struct SysTask {
    invoker: ManagedMutPtr<dyn Invoke + Send>,
    buf: ManagedMutPtr<SystemBuffer>,
    sid: SystemId,
}

impl SysTask {
    fn execute(self) -> Result<(), Box<dyn Any + Send>> {
        #[cfg(not(target_arch = "wasm32"))]
        {
            let Self {
                mut invoker,
                mut buf,
                ..
            } = self;
            let executor = std::panic::AssertUnwindSafe(move || {
                invoker.invoke(&mut buf);
            });
            std::panic::catch_unwind(executor)
        }

        #[cfg(target_arch = "wasm32")]
        {
            #[cfg(not(debug_assertions))]
            {
                let Self {
                    mut invoker,
                    mut buf,
                    ..
                } = self;
                invoker.invoke(&mut buf);
            }

            // In web and debug mode, drops `ManagedMutPtr` first
            // to be recovered when the invoker panics.
            #[cfg(debug_assertions)]
            {
                let Self { invoker, buf, .. } = self;
                let mut invoker_ptr = invoker.inner();
                let mut buf_ptr = buf.inner();
                drop(invoker);
                drop(buf);
                // Safety: Managed pointers.
                unsafe {
                    invoker_ptr.as_mut().invoke(buf_ptr.as_mut());
                }
            }

            Ok(())
        }
    }

    const fn id(&self) -> TaskId {
        TaskId::Sys(self.sid)
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/rayon-core/src/job.rs#L33
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ParTask {
    data: NonNull<()>,
    f: unsafe fn(NonNull<()>, FnContext),
}

unsafe impl Send for ParTask {}

impl ParTask {
    /// # Safety
    ///
    /// Given reference must live until this struct is dropped.
    unsafe fn new<F, R>(t: &ParTaskHolder<F, R>) -> Self
    where
        F: FnOnce(FnContext) -> R + Send,
    {
        // Safety: Infallible.
        let data = unsafe {
            let ptr = t as *const _ as *const ();
            NonNull::new_unchecked(ptr.cast_mut())
        };
        let f = ParTaskHolder::<F, R>::execute;
        Self { data, f }
    }

    fn execute(self, f_cx: FnContext) {
        // Safety: Guaranteed by owner who called new().
        unsafe { (self.f)(self.data, f_cx) };
    }

    const fn id(&self) -> TaskId {
        TaskId::Par(*self)
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/rayon-core/src/job.rs#L72
#[derive(Debug)]
struct ParTaskHolder<F, R> {
    f: UnsafeCell<Option<F>>,
    res: UnsafeCell<Option<R>>,
    panic: UnsafeCell<Option<Box<dyn Any + Send>>>,
    flag: ParTaskFlag,
}

impl<F, R> ParTaskHolder<F, R>
where
    F: FnOnce(FnContext) -> R + Send,
{
    fn new(f: F) -> Self {
        Self {
            f: UnsafeCell::new(Some(f)),
            res: UnsafeCell::new(None),
            panic: UnsafeCell::new(None),
            flag: ParTaskFlag::init(),
        }
    }

    /// Converts `data` into self,
    /// Then takes function out from the function slot and executes it,
    /// and then puts the returned value in the return slot.
    unsafe fn execute(data: NonNull<()>, f_cx: FnContext) {
        let this: &Self = data.cast().as_ref();
        let f = (*this.f.get()).take().unwrap_unchecked();

        #[cfg(not(target_arch = "wasm32"))]
        {
            let executor = std::panic::AssertUnwindSafe(move || f(f_cx));
            match std::panic::catch_unwind(executor) {
                Ok(res) => *this.res.get() = Some(res),
                Err(payload) => *this.panic.get() = Some(payload),
            }
            this.flag.done();
        }

        #[cfg(target_arch = "wasm32")]
        {
            let res = f(f_cx);
            *this.res.get() = Some(res);
            this.flag.done();
        }
    }

    fn is_executed(&self) -> bool {
        self.flag.is_done()
    }

    /// # Safety
    ///
    /// Must have been executed.
    unsafe fn return_or_panic_unchecked(self) -> Result<R, Box<dyn Any + Send>> {
        if let Some(res) = self.res.into_inner() {
            Ok(res)
        } else {
            let payload = self.panic.into_inner().unwrap_unchecked();
            Err(payload)
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
struct ParTaskFlag(AtomicI32);

impl ParTaskFlag {
    const INIT_INNER: i32 = 0;
    const DONE_INNER: i32 = 1;

    fn init() -> Self {
        Self(AtomicI32::new(Self::INIT_INNER))
    }

    fn done(&self) {
        self.0.store(Self::DONE_INNER, Ordering::Release);
    }

    fn is_done(&self) -> bool {
        if self.0.load(Ordering::Relaxed) == Self::DONE_INNER {
            atomic::fence(Ordering::Acquire);
            true
        } else {
            false
        }
    }
}

struct ParkingChannel<T>(PhantomData<T>);

impl<T> ParkingChannel<T> {
    fn channel(_th: Thread) -> (ParkingSender<T>, ParkingReceiver<T>) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            mpsc::channel()
        }

        #[cfg(target_arch = "wasm32")]
        {
            let (tx, rx) = mpsc::channel();
            (
                ParkingSender::new(tx, _th.clone()),
                ParkingReceiver::new(rx),
            )
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
type ParkingSender<T> = Sender<T>;

#[cfg(not(target_arch = "wasm32"))]
type ParkingReceiver<T> = Receiver<T>;

#[cfg(target_arch = "wasm32")]
use web::*;

#[cfg(target_arch = "wasm32")]
pub(super) mod web {
    use super::*;
    use crate::util::prelude::*;
    use std::{
        fmt,
        panic::PanicInfo,
        sync::mpsc::{RecvTimeoutError, TryRecvError},
    };

    thread_local! {
        /// Per-thread work that the thread is trying to do.
        pub(super) static WORK_ID: Cell<WorkId> = const {
            Cell::new(WorkId {
                widx: WorkerIndex::new(usize::MAX),
                sid: SystemId::dummy(),
                is_par: false,
            })
        };
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct WorkId {
        pub(super) widx: WorkerIndex,
        pub(super) sid: SystemId,
        pub(super) is_par: bool,
    }

    #[derive(Debug)]
    pub(super) struct ParkingSender<T> {
        tx: Sender<T>,
        th: Thread,
    }

    impl<T> ParkingSender<T> {
        pub(super) const fn new(tx: Sender<T>, th: Thread) -> Self {
            Self { tx, th }
        }

        pub(super) fn send(&self, t: T) -> Result<(), std::sync::mpsc::SendError<T>> {
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

    pub(super) struct ParkingReceiver<T> {
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
        pub(super) const fn new(rx: Receiver<T>) -> Self {
            Self {
                rx,
                next: Cell::new(None),
            }
        }

        /// May return spuriously.
        //
        // Why `thread::park_timeout()` instead of `Receiver::recv_timeout()`?
        //
        // In web, we cannot get time, but `Receiver::recv_timeout()` tries
        // to get current time, so it fails to compile.
        // Fortunately, in nightly-2024-06-20, `thread::park_timeout()` is
        // implemented via wasm32::memory_atomic_wait32(), so it works.
        // See "nightly-2024-06-20-.../lib/rustlib/src/rust/library/std/src/sys/pal/wasm/atomics/futex.rs"
        pub(super) fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
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

        pub(super) fn try_recv(&self) -> Result<T, TryRecvError> {
            if let Some(value) = self.next.take() {
                Ok(value)
            } else {
                self.rx.try_recv()
            }
        }
    }

    pub fn web_panic_hook(_info: &PanicInfo<'_>) {
        let ptr = SUB_CONTEXT.get();
        if !ptr.is_dangling() {
            let widx = WORK_ID.get().widx;
            let sid = WORK_ID.get().sid;
            let unrecoverable = WORK_ID.get().is_par;
            let payload = Box::new("panic in wasm".to_owned());
            let msg = PanicMessage {
                widx,
                sid,
                unrecoverable,
                payload,
            };

            // Safety: Not a dangling pointer, and `SubContext` is not used.
            // The corresponding thread was panicked a bit ago and
            // it's running this function now.
            let cx = unsafe { ptr.as_ref() };
            let _ = cx.tx_msg.send(Message::Panic(msg));
        }

        let _ = web_util::worker_post_message(&"panic".into());
    }
}
