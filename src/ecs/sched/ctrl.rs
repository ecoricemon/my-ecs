use super::{
    comm::{GlobalSignal, ParkingChannel, ParkingReceiver, ParkingSender, SubComm},
    par::FnContext,
    task::{ParTask, SysTask, Task},
};
use crate::{
    ds::prelude::*,
    ecs::{
        cache::{CacheItem, RefreshCacheStorage},
        cmd::Command,
        sys::system::{SystemCycleIter, SystemData, SystemGroup, SystemId},
        wait::WaitQueues,
        worker::{HoldWorkers, Message, PanicMessage, Work, WorkerId},
    },
};
use crossbeam_deque as cb;
use std::{
    any::Any,
    cell::{Cell, UnsafeCell},
    collections::{HashMap, HashSet, VecDeque},
    future::Future,
    hash::BuildHasher,
    marker::PhantomPinned,
    mem,
    pin::Pin,
    sync::{
        mpsc::{RecvTimeoutError, TryRecvError},
        Arc,
    },
    task::Poll,
    thread::{self, Thread},
    time::Duration,
};

#[derive(Debug)]
pub(crate) struct Scheduler<Wp, S> {
    waits: WaitQueues<S>,

    /// System run record.
    record: ScheduleRecord<S>,

    /// A list holding pending tasks due to data dependency.
    pending: Pending<S>,

    cx: MainContext,

    worker_pool: Wp,
}

impl<Wp, S> Scheduler<Wp, S>
where
    Wp: HoldWorkers + Default + 'static,
    S: BuildHasher + Default + 'static,
{
    pub(crate) fn new(mut worker_pool: Wp) -> Self {
        let num_workers = worker_pool.workers().len();

        let mut this = Self {
            waits: WaitQueues::new(),
            record: ScheduleRecord::new(),
            pending: Pending::new(),
            cx: MainContext::new(num_workers),
            worker_pool,
        };

        // Collects thread handles from sub workers, then initialize
        // main context using the handles.
        let sub_handles = collect_handles(&mut this, num_workers);
        this.cx.initialize(sub_handles);

        return this;

        // === Internal helper functions ===

        fn collect_handles<Wp, S>(this: &mut Scheduler<Wp, S>, num_workers: usize) -> Vec<Thread>
        where
            Wp: HoldWorkers + Default + 'static,
            S: BuildHasher + Default + 'static,
        {
            // Main context and sub contexts are all created newly.
            // So sub workers will send thread handles when we open them
            // at the first time.
            for i in 0..num_workers {
                this.open_worker(i, SubState::Open);
            }

            // Waits for all thread handles to be sent.
            let mut remain = num_workers;
            while remain > 0 {
                if let Ok(msg) = this.cx.recv_msg_timeout() {
                    debug_assert_eq!(
                        mem::discriminant(&msg),
                        mem::discriminant(&Message::Handle(WorkerId::dummy()))
                    );
                    remain -= 1;
                }
            }

            // Returns thread handle vector.
            this.cx
                .sub_cxs
                .iter()
                .map(|sub_cx| unsafe { (*sub_cx.handle.get()).clone() })
                .collect()
        }
    }

    pub(crate) fn has_command(&self) -> bool {
        self.cx.rx_cmd.has()
    }

    pub(crate) fn num_open_workers(&self) -> u32 {
        self.cx.signal.open_count()
    }

    /// Destroys this scheduler and then returns internal worker pool.
    //
    // Main context is reset when worker pool is changed.
    // Schduler is a wrapper of the main context, so it also needs to be reset.
    pub(crate) fn into_worker_pool(self) -> Wp {
        self.worker_pool
    }

    pub(crate) fn get_wait_queues_mut(&mut self) -> &mut WaitQueues<S> {
        &mut self.waits
    }

    pub(crate) fn get_record_mut(&mut self) -> &mut ScheduleRecord<S> {
        &mut self.record
    }

    pub(crate) fn open_workers(&mut self) {
        let num_workers = self.worker_pool.workers().len() as u32;

        // If workers are already open, returns immediately.
        // It can happen due to future task.
        let open_cnt = self.cx.signal.open_count();
        if open_cnt > 0 {
            debug_assert_eq!(open_cnt, num_workers);
            return;
        }

        // Opens all workers. Each sub worker will increase open count by 1.
        for i in 0..num_workers {
            self.open_worker(i as usize, SubState::Open);
        }

        // Waits for all sub workers to be open.
        self.cx.signal.wait_open_count(num_workers);
    }

    fn open_worker(&mut self, i: usize, state: SubState) {
        // Sets sub state first.
        self.cx.sub_cxs[i].as_mut().set_state(state);

        let ptr = self.cx.ptr_sub(i);
        // Safety: The pointer won't be aliased and they will be valid
        // during scheduling.
        let ptr = unsafe {
            let ptr = NonNullExt::new_unchecked(ptr.cast_mut());
            ManagedConstPtr::new(ptr)
        };
        let must_true = self.worker_pool.workers()[i].unpark(ptr);
        assert!(must_true);
    }

    pub(crate) fn close_workers(&mut self) {
        let open_cnt = self.cx.signal.open_count();
        if open_cnt > 0 {
            debug_assert_eq!(open_cnt, self.cx.sub_cxs.len() as u32);

            // If uncompleted future task detected, we cannot close sub workers
            // now.
            if !self.cx.wait_for_idle_sense_future() {
                return;
            }

            // Closes sub workers.
            self.cx.close_subs();

            // Parks workers.
            for worker in self.worker_pool.workers().iter_mut() {
                let must_true = worker.park();
                assert!(must_true);
            }
        }

        #[cfg(debug_assertions)]
        self.validate_clean();
    }

    /// Schedules all system tasks.
    pub(crate) fn execute(
        &mut self,
        sgroup: &mut SystemGroup<S>,
        cache: &mut RefreshCacheStorage<S>,
        dedi: &HashSet<SystemId, S>,
    ) {
        let num_workers = self.worker_pool.workers().len();
        self.pending.limit = num_workers;
        let mut state = MainState::Look;
        let mut cycle = sgroup.get_active_mut().iter_begin();
        let mut panicked = Vec::new();

        loop {
            match state {
                MainState::Look => {
                    state = self.look(&cycle, num_workers);
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
                    self.wait(&mut cycle, cache, &mut panicked);
                    state = MainState::Look;
                }
                MainState::Exit => {
                    self.exit(&mut cycle, cache, &mut panicked);
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

        // Clears system run record.
        self.record.clear();
    }

    pub(crate) fn consume_commands<F>(&self, mut f: F)
    where
        F: FnMut(Box<dyn Command>),
    {
        while let Ok(cmd) = self.cx.try_recv_cmd() {
            f(cmd);
        }
    }

    pub(crate) fn wait_for_idle(&self) {
        self.cx.wait_for_idle();
    }

    fn look(&mut self, cycle: &SystemCycleIter<'_, S>, worker_len: usize) -> MainState {
        let ready_normal_len = self.cx.len_global();
        let is_ready_dedi_empty = self.cx.dedi.is_empty();

        if ready_normal_len > worker_len && !is_ready_dedi_empty {
            MainState::Work
        } else if !cycle.position().is_end() {
            MainState::Pick
        } else if !is_ready_dedi_empty {
            MainState::Work
        } else {
            let is_pending_normal_empty = self.pending.normal.is_occupied_empty();
            let is_pending_dedi_empty = self.pending.dedi.is_occupied_empty();

            if ready_normal_len > 0 || !is_pending_normal_empty || !is_pending_dedi_empty {
                MainState::Wait
            } else {
                MainState::Exit
            }
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
            self.record.insert(sid, RunResult::Injected);
            Self::push_ready_system(&mut self.cx, sdata, cache, is_dedi);
            cycle.next();
            true
        }
        // Data dependency detected, then tries to push it in pending list.
        else if self.pending.try_push(cycle.position(), is_dedi) {
            self.record.insert(sid, RunResult::Injected);
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
            Task::System(task) => {
                let _ = task.execute();
            }
            _ => unreachable!("parallel or async task is not allowed on main worker"),
        }
    }

    fn wait(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
    ) {
        // Waits for message from sub workers.
        if let Ok(msg) = self.cx.recv_msg_timeout() {
            self.handle_message(msg, cycle, cache, panicked);
        }
        // Optimistically consumes messages as many as possible.
        while let Ok(msg) = self.cx.try_recv_msg() {
            self.handle_message(msg, cycle, cache, panicked);
        }
    }

    fn exit(
        &mut self,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
    ) {
        // Waits for all system tasks to be done.
        while self.record.num_injected() > self.record.num_completed() {
            if let Ok(msg) = self.cx.recv_msg_timeout() {
                self.handle_message(msg, cycle, cache, panicked);
            }
        }

        debug_assert_eq!(self.cx.signal.open_count(), self.cx.sub_cxs.len() as u32);

        // If uncompleted future task detected, we cannot close sub workers now.
        if !self.cx.wait_for_idle_sense_future() {
            return;
        }

        // Closes sub workers.
        self.cx.close_subs();
    }

    fn handle_message(
        &mut self,
        msg: Message,
        cycle: &mut SystemCycleIter<'_, S>,
        cache: &mut RefreshCacheStorage<'_, S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
    ) {
        match msg {
            Message::Handle(..) => unreachable!(),
            Message::Fin(_wid, sid) => {
                self.record.insert(sid, RunResult::Finished);
                let cache = cache.get(&sid).unwrap();
                self.waits.dequeue(&cache.get_wait_indices());
            }
            Message::Aborted(_wid, sid) => {
                self.record.insert(sid, RunResult::Aborted);
                let cache = cache.get(&sid).unwrap();
                self.waits.dequeue(&cache.get_wait_indices());
            }
            Message::Panic(msg) => {
                self.record.insert(msg.sid, RunResult::Panicked);
                self.panic_helper(cache, panicked, msg);
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
        // Safety: Scheduler guarantees those pointers will be used in the
        // worker only.
        let task = unsafe {
            let invoker = ManagedMutPtr::new(sdata.task_ptr());
            let buf = ManagedMutPtr::new(cache.request_buffer_ptr());
            let sid = sdata.id();
            Task::System(SysTask::new(invoker, buf, sid))
        };
        cx.push_task(task, is_dedi);
    }

    fn panic_helper(
        &mut self,
        cache: &mut RefreshCacheStorage<S>,
        panicked: &mut Vec<(SystemId, Box<dyn Any + Send>)>,
        msg: PanicMessage,
    ) {
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
            self.open_worker(msg.wid.index(), SubState::Search);
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
        // Validates we have no pending system tasks.
        assert_eq!(0, self.pending.normal.len_occupied());
        assert_eq!(0, self.pending.dedi.len_occupied());

        // Validates we have no waiting requests. It takes O(n).
        assert!(self.waits.is_all_queue_empty());

        // Validates main contexts. Sub contexts, on the other hand, are not
        // validated due to future tasks.
        self.cx.validate_clean();
    }
}

#[derive(Debug)]
pub(crate) struct ScheduleRecord<S> {
    record: HashMap<SystemId, RunResult, S>,
    injected: usize,
    finished: usize,
    panicked: usize,
    aborted: usize,
}

impl<S> ScheduleRecord<S>
where
    S: BuildHasher + Default + 'static,
{
    fn new() -> Self {
        Self {
            record: HashMap::default(),
            injected: 0,
            finished: 0,
            panicked: 0,
            aborted: 0,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.record.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn clear(&mut self) {
        self.record.clear();
        self.injected = 0;
        self.finished = 0;
        self.panicked = 0;
        self.aborted = 0;
    }

    pub(crate) fn contains<Q>(&self, sid: &Q) -> bool
    where
        SystemId: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq + ?Sized,
    {
        self.record.contains_key(sid)
    }

    pub(crate) fn num_injected(&self) -> usize {
        self.injected
    }

    pub(crate) fn num_completed(&self) -> usize {
        self.finished + self.panicked
    }

    fn insert(&mut self, sid: SystemId, state: RunResult) {
        match state {
            RunResult::Injected => self.injected += 1,
            RunResult::Finished => self.finished += 1,
            RunResult::Panicked => self.panicked += 1,
            RunResult::Aborted => self.aborted += 1,
        }
        self.record.insert(sid, state);
    }
}

#[derive(Debug)]
pub(crate) enum RunResult {
    Injected,
    Finished,
    Panicked,
    Aborted,
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
    /// Each sub worker has its own context.
    sub_cxs: Vec<Pin<Box<SubContext>>>,

    signal: Arc<GlobalSignal>,

    /// Ready normal tasks.
    global: Arc<cb::Injector<Task>>,

    /// Ready dedicated tasks.
    dedi: VecDeque<Task>,

    /// Channel receving messages from sub workers.
    rx_msg: ParkingReceiver<Message>,

    /// Channel receving commands from sub workers.
    rx_cmd: ParkingReceiver<Box<dyn Command>>,

    /// Transmit channels will be cloned and distributed to sub workers.
    _tx_msg: ParkingSender<Message>,
    _tx_cmd: ParkingSender<Box<dyn Command>>,
}

impl MainContext {
    const RX_CHANNEL_TIMEOUT: Duration = Duration::from_secs(u64::MAX);

    fn new(sub_len: usize) -> Self {
        // Creates global queue.
        let global = Arc::new(cb::Injector::new());

        // Channels.
        let (tx_msg, rx_msg) = ParkingChannel::channel(thread::current());
        let (tx_cmd, rx_cmd) = ParkingChannel::channel(thread::current());

        // This signal will be replaced at `initialize` with sub worker's
        // handles.
        let dummy_signal = Arc::new(GlobalSignal::new(Vec::new()));

        let comms = SubComm::with_len(&global, &dummy_signal, &tx_msg, &tx_cmd, sub_len);

        // Sub contexts.
        let sub_cxs = comms
            .into_iter()
            .map(|comm| {
                Box::pin(SubContext {
                    // Puts in dummy handle for now. Sub workers will overwrite
                    // their handles at their first execution.
                    handle: UnsafeCell::new(thread::current()),
                    start: SubState::Open,
                    comm,
                    _pin: PhantomPinned,
                })
            })
            .collect();

        Self {
            sub_cxs,
            signal: dummy_signal,
            global,
            dedi: VecDeque::new(),
            rx_msg,
            rx_cmd,
            _tx_msg: tx_msg,
            _tx_cmd: tx_cmd,
        }
    }

    fn initialize(&mut self, sub_handles: Vec<Thread>) {
        self.signal = Arc::new(GlobalSignal::new(sub_handles));

        for sub_cx in self.sub_cxs.iter_mut() {
            sub_cx.as_mut().set_flags(Arc::clone(&self.signal));
        }
    }

    fn recv_msg_timeout(&self) -> Result<Message, RecvTimeoutError> {
        self.rx_msg.recv_timeout(Self::RX_CHANNEL_TIMEOUT)
    }

    fn try_recv_msg(&self) -> Result<Message, TryRecvError> {
        self.rx_msg.try_recv()
    }

    fn try_recv_cmd(&self) -> Result<Box<dyn Command>, TryRecvError> {
        self.rx_cmd.try_recv()
    }

    fn ptr_sub(&self, i: usize) -> *const SubContext {
        let sub_cx = &self.sub_cxs[i];
        sub_cx.as_ref().get_ref() as *const _
    }

    fn len_global(&self) -> usize {
        self.global.len()
    }

    fn push_task(&mut self, task: Task, is_dedi: bool) {
        if is_dedi {
            self.dedi.push_back(task);
        } else {
            self.global.push(task);
            self.signal.sub().notify_one();
        }
    }

    /// Waits until all sub workers to be idle and all future tasks have been
    /// done.
    //
    // Why we care about future tasks?
    // If all sub workers are blocked, in wait state in other words, and there
    // is no future task, they are completely idle. They cannot do anything
    // until main worker does something.
    // However, if we have a remaining future task, it may inject a system task
    // during idle state, in turn, it will wake a worker up. So we cannot
    // guarantee that continued idle state when we have remaining future tasks.
    fn wait_for_idle(&self) {
        let num_workers = self.sub_cxs.len() as u32;
        self.signal.wait_idle_future_counts(num_workers, 0);
    }

    /// Tries to wait for all sub workers to be idle. But, running future task
    /// count may have changed and it's not zero during waiting, then returns
    /// false immediately. If all sub workers successfully become idle, returns
    /// true.
    fn wait_for_idle_sense_future(&self) -> bool {
        // Possible count conditions are as follows.
        //
        // 1. # of idle == # of workers, # of future tasks == 0
        //    All sub workers are in idle states and we have no future tasks.
        //    We are good to return true.
        // 2. # of idle == # of workers, # of future tasks > 0
        //    All sub workers are in idle states and we have some future tasks.
        //    Returns false due to the future tasks.
        // 3. # of idle < # of workers, # of future tasks == 0
        //    Some sub workers are in busy states and we have no future tasks.
        //    But note that future task may be injected anytime by system tasks.
        //    So, waits until all sub workers become idle states, then
        //    follows other instructions according to the new count states.
        // 4. # of idle < # of workers, # of future tasks > 0
        //    Some sub workers are in busy states and we have some future tasks.
        //    Returns false due to the future tasks.

        let num_workers = self.sub_cxs.len() as u32;
        let (mut idle_cnt, mut fut_cnt) = self.signal.idle_future_counts();

        loop {
            if idle_cnt == num_workers {
                if fut_cnt == 0 {
                    // Case 1
                    return true;
                } else {
                    // Case 2
                    return false;
                }
            } else if fut_cnt == 0 {
                // Case 3
                (idle_cnt, fut_cnt) = self
                    .signal
                    .wait_idle_future_counts(num_workers, GlobalSignal::ANY_TARGET);
            } else {
                // Case 4
                return false;
            }
        }
    }

    fn close_subs(&self) {
        // Closes sub workers.
        self.signal.set_exit(true);
        self.signal.sub().notify_all();
        self.signal.wait_open_count(0);
        self.signal.set_exit(false);
    }

    #[cfg(debug_assertions)]
    fn validate_clean(&self) {
        // Is normal ready queue empty?
        assert!(self.global.is_empty());

        // Is dedicated ready queue empty?
        assert!(self.dedi.is_empty());

        // Is close flag in initial state?
        assert!(!self.signal.is_close());

        // Is receiving channel empty?
        match self.rx_msg.try_recv() {
            Err(std::sync::mpsc::TryRecvError::Empty) => {}
            Ok(msg) => panic!("unexpected remaining msg in channel: {msg:?}"),
            Err(err) => panic!("unexpected error from channel: {err:?}"),
        }
    }
}

impl Drop for MainContext {
    fn drop(&mut self) {
        let open_cnt = self.signal.open_count();
        if open_cnt > 0 {
            debug_assert_eq!(open_cnt, self.sub_cxs.len() as u32);

            self.signal.set_abort(true);
            self.signal.sub().notify_all();
            self.signal.wait_open_count(0);
            self.signal.set_abort(false);
        }
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

thread_local! {
    pub(crate) static SUB_CONTEXT: Cell<NonNullExt<SubContext>> = const {
        Cell::new(NonNullExt::dangling())
    };
}

#[derive(Debug)]
pub struct SubContext {
    /// Thread handle.
    handle: UnsafeCell<Thread>,

    /// Starting state.
    start: SubState,

    comm: SubComm,

    _pin: PhantomPinned,
}

impl SubContext {
    /// Use this function in your [`Worker::unpark`] implementation.
    ///
    /// It executes sub context on the current thread, which means it expects
    /// to be executed on a sub worker.  
    /// On the first call, this sends thread handle and returns
    /// immediately.
    /// Main worker may be able to use that thread handle to wake the worker up.
    /// Since then, from next call, this runs to do some tasks until
    /// main worker sends an exit signal.
    ///
    /// [`Worker::unpark`]: crate::prelude::Worker::unpark
    pub fn execute(ptr: ManagedConstPtr<Self>) {
        thread_local! {
            static WORKER_ID: Cell<WorkerId> = const {
                Cell::new(WorkerId::dummy())
            };
        }

        if ptr.comm.worker_id() != WORKER_ID.get() {
            let handle = unsafe { &mut *ptr.handle.get() };
            *handle = thread::current();
            SUB_CONTEXT.set(ptr.inner());
            WORKER_ID.set(ptr.comm.worker_id());
            ptr.comm.send_message(Message::Handle(ptr.comm.worker_id()));
            return;
        }

        let this = {
            #[cfg(not(all(debug_assertions, target_arch = "wasm32")))]
            {
                &*ptr
            }

            // In web and debug mode, drops managed pointer first
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
                    this.comm.signal().add_open_count();
                    state = SubState::Wait;
                }
                SubState::Wait => {
                    this.comm.wait();
                    state = if this.comm.signal().is_abort() {
                        SubState::Abort
                    } else if this.comm.signal().is_close() {
                        SubState::Close
                    } else {
                        SubState::Search
                    };
                }
                SubState::Search => {
                    steal = this.comm.search();
                    state = if steal.is_success() {
                        SubState::Work
                    } else {
                        SubState::Wait
                    };
                }
                SubState::Work => {
                    this.work(&mut steal);
                    state = SubState::Search;
                }
                SubState::Abort => {
                    this.abort();
                    state = SubState::Close;
                }
                SubState::Close => {
                    // In debug mode, drops managed pointer before
                    // we notify closed status to main thread.
                    #[cfg(all(debug_assertions, not(target_arch = "wasm32")))]
                    let this = ptr.into_ref();

                    this.comm.signal().sub_open_count();
                    break;
                }
            }
        }
    }

    pub(crate) fn comm(&self) -> &SubComm {
        &self.comm
    }

    pub(super) fn work(&self, steal: &mut cb::Steal<Task>) {
        loop {
            match mem::replace(steal, cb::Steal::Empty) {
                cb::Steal::Success(cur) => match cur {
                    Task::System(task) => {
                        self.work_for_system_task(task);
                    }
                    Task::Parallel(task) => {
                        self.work_for_parallel_task(task);
                    }
                    Task::Future(task) => {
                        self.work_for_future_task(task);
                    }
                },
                cb::Steal::Empty => break,
                cb::Steal::Retry => {}
            }

            *steal = self.comm.pop();
        }
    }

    fn work_for_system_task(&self, task: SysTask) {
        let sid = task.sid();

        // In web, panic is normally aborted, but we can detect
        // whether or not panic has been happened through panic hook.
        // We write `WorkId` to thread local variable to be used in
        // panic hook in order to identify where the panic occured.
        #[cfg(target_arch = "wasm32")]
        {
            use super::comm::{TaskKind, WorkId, WORK_ID};

            WORK_ID.set(WorkId {
                wid: self.comm.worker_id(),
                sid,
                kind: TaskKind::System,
            });
        }

        let resp = match task.execute() {
            Ok(_) => Message::Fin(self.comm.worker_id(), sid),
            Err(payload) => Message::Panic(PanicMessage {
                wid: self.comm.worker_id(),
                sid,
                payload,
                unrecoverable: false,
            }),
        };

        self.comm.send_message(resp);
    }

    fn work_for_parallel_task(&self, task: ParTask) {
        // Like in `work_for_systask()`, sets `WorkId`.
        // But note that panics in parallel tasks cannot be recovered.
        // It will result in panic in main thread.
        #[cfg(target_arch = "wasm32")]
        {
            use super::comm::{TaskKind, WorkId, WORK_ID};

            WORK_ID.set(WorkId {
                wid: self.comm.worker_id(),
                sid: SystemId::dummy(),
                kind: TaskKind::Parallel,
            });
        }

        task.execute(FnContext::MIGRATED);
    }

    fn work_for_future_task(&self, task: UnsafeFuture) {
        // Like in `work_for_systask()`, sets `WorkId`.
        #[cfg(target_arch = "wasm32")]
        {
            use super::comm::{TaskKind, WorkId, WORK_ID};

            WORK_ID.set(WorkId {
                wid: self.comm.worker_id(),
                sid: SystemId::dummy(),
                kind: TaskKind::Future,
            });
        }

        // Future task may be one that this worker stole from another worker.
        // In that case, we'd better replace waker with this context pointer.
        // So that the future will wake this worker up at first.
        //
        // Safety: Waker type is the same as the thing we used, which is
        // `UnsafeWaker`.
        unsafe {
            let waker = UnsafeWaker {
                ptr: self as *const _,
            };
            if !task.will_wake(&waker) {
                task.set_waker(waker);
            }
        }

        // Calls poll on the future.
        //
        // Safety: We're constraining future output type to be
        // `Box<dyn Command>`.
        match unsafe { task.poll_unchecked::<Box<dyn Command>>() } {
            Poll::Ready(ready) => {
                // Deallocates the future and takes command out.
                //
                // Safety: We're not calling `UnsafeFuture::destroy` directly.
                let cmd = unsafe { ready.take() };

                // Decreases running future count and sends the command.
                self.comm.signal().sub_future_count();
                self.comm.send_command(cmd);
            }
            Poll::Pending => {}
        }
    }

    fn abort(&self) {
        loop {
            match self.comm.pop() {
                cb::Steal::Success(task) => self.abort_task(task),
                cb::Steal::Empty => {
                    let (_, fut) = self.comm.signal().idle_future_counts();
                    if fut == 0 {
                        // Before escaping the loop, notifies all other sub
                        // wokers, so that they can escape their loops as well.
                        self.comm.signal().sub().notify_all();
                        break;
                    }

                    // This worker may be supposed to be woken by a future task.
                    self.comm.wait();
                }
                cb::Steal::Retry => {}
            }
        }
    }

    fn abort_task(&self, task: Task) {
        match task {
            // To abort system task, drops it and sends Aborted to main worker.
            Task::System(task) => {
                let wid = self.comm.worker_id();
                let sid = task.sid();
                self.comm.send_message(Message::Aborted(wid, sid));
            }
            // Parallel task cannot be aborted. It should be aborted at system
            // task level.
            Task::Parallel(task) => {
                self.work_for_parallel_task(task);
            }
            // To abort future task, destroys it and reduces running future
            // count.
            Task::Future(task) => {
                // Safety: Uncompleted future task is aborted and deallocated
                // in here only.
                unsafe {
                    task.destroy();
                }
                self.comm.signal().sub_future_count();
            }
        }
    }

    fn set_state(self: Pin<&mut Self>, state: SubState) {
        // Safety: We do not move self.
        unsafe {
            let this = self.get_unchecked_mut();
            this.start = state;
        }
    }

    fn set_flags(self: Pin<&mut Self>, flags: Arc<GlobalSignal>) {
        // Safety: We do not move self.
        unsafe {
            let this = self.get_unchecked_mut();
            this.comm.set_signal(flags);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubState {
    Open,
    Wait,
    Search,
    Work,
    Abort,
    Close,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UnsafeWaker {
    ptr: *const SubContext,
}

unsafe impl Send for UnsafeWaker {}
unsafe impl Sync for UnsafeWaker {}

impl WakeSend for UnsafeWaker {
    fn wake_send(&self, handle: UnsafeFuture) {
        // Safety: Scheduler holds sub contexts while it is executing.
        let comm = unsafe { self.ptr.as_ref().unwrap_unchecked().comm() };

        // Pushes the future handle onto local future queue.
        comm.push_future_task(handle);

        // Tries to wake up the worker which called poll() on the future.
        // If it is already awaken, wakes another worker.
        comm.wake_self();
    }
}

pub fn schedule_future<F>(future: F)
where
    F: Future<Output = Box<dyn Command>> + Send + 'static,
{
    // This function must be called on sub worker context.
    let ptr = SUB_CONTEXT.get();
    assert!(!ptr.is_dangling());

    // Allocates memory for the future.
    // Safety: Current worker has valid sub context pointer.
    let comm = unsafe { ptr.as_ref().comm() };
    let waker = UnsafeWaker { ptr: ptr.as_ptr() };
    let handle = UnsafeFuture::new(future, waker);

    // Pushes the future handle onto local future queue.
    comm.push_future_task(handle);

    // Increases number of future count.
    // Main worker will check this out whenever it needs.
    comm.signal().add_future_count();

    // If current worker's local queue is not empty, current worker cannot
    // do the future task promptly, so wakes another worker to steal it.
    if !comm.is_local_empty() {
        comm.signal().sub().notify_one();
    }
}
