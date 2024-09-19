use super::{ParTask, ParTaskHolder, Task, SUB_CONTEXT};
use rayon::iter::{
    plumbing::{Consumer, Folder, Producer, ProducerCallback, Reducer},
    IndexedParallelIterator,
};

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/rayon-core/src/lib.rs#L851
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub(super) struct FnContext {
    migrated: bool,
}

impl FnContext {
    pub(super) const MIGRATED: Self = Self { migrated: true };
    pub(super) const NOT_MIGRATED: Self = Self { migrated: false };
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/src/iter/plumbing/mod.rs#L255C1-L255C18
#[derive(Debug, Clone, Copy)]
struct Splitter {
    splits: usize,
}

impl Splitter {
    fn new() -> Option<Self> {
        let ptr = SUB_CONTEXT.get();
        (!ptr.is_dangling()).then(|| {
            // Safety: `ptr` is a valid pointer.
            let num_workers = unsafe { ptr.as_ref().siblings.len() };
            Self {
                splits: num_workers,
            }
        })
    }

    fn try_split(&mut self, migrated: bool) -> bool {
        // rayon implementation.
        //
        // If a task is migrated, i.e. took it from another worker's local queue,
        // that could mean that some workers are hungry for tasks.
        // Therefore, it would be good for keeping processors busy
        // to split this task into enough small pieces.
        // if migrated {
        //     let num_workers = unsafe { SUB_CONTEXT.get().as_ref().siblings.len() };
        //     self.splits = num_workers.max(self.splits / 2);
        //     true
        // } else {
        //     let res = self.splits > 0;
        //     self.splits /= 2;
        //     res
        // }

        // my implementation.
        //
        // Currently, I need to optimize work distribution.
        // Meanwhile, this could hide poor performance.
        if !migrated {
            self.splits /= 2;
        }
        self.splits > 0
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/src/iter/plumbing/mod.rs#L293
#[derive(Debug, Clone, Copy)]
struct LengthSplitter {
    inner: Splitter,
    min: usize,
}

impl LengthSplitter {
    fn new(min: usize, max: usize, len: usize) -> Option<Self> {
        let mut inner = Splitter::new()?;
        let min_splits = len / max.max(1);
        inner.splits = inner.splits.max(min_splits);

        Some(Self {
            inner,
            min: min.max(1),
        })
    }

    fn try_split(&mut self, len: usize, migrated: bool) -> bool {
        len / 2 >= self.min && self.inner.try_split(migrated)
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/src/iter/plumbing/mod.rs#L350
pub(crate) fn bridge<I, C>(par_iter: I, consumer: C) -> C::Result
where
    I: IndexedParallelIterator,
    C: Consumer<I::Item>,
{
    let len = par_iter.len();
    return par_iter.with_producer(Callback { len, consumer });

    struct Callback<C> {
        len: usize,
        consumer: C,
    }

    impl<C, I> ProducerCallback<I> for Callback<C>
    where
        C: Consumer<I>,
    {
        type Output = C::Result;
        fn callback<P>(self, producer: P) -> C::Result
        where
            P: Producer<Item = I>,
        {
            bridge_producer_consumer(self.len, producer, self.consumer)
        }
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/src/iter/plumbing/mod.rs#L390
fn bridge_producer_consumer<P, C>(len: usize, producer: P, consumer: C) -> C::Result
where
    P: Producer,
    C: Consumer<P::Item>,
{
    let splitter = LengthSplitter::new(producer.min_len(), producer.max_len(), len).unwrap();
    const MIGRATED: bool = false;
    return helper(len, MIGRATED, splitter, producer, consumer);

    // === Internal helper functions ===

    fn helper<P, C>(
        len: usize,
        migrated: bool,
        mut splitter: LengthSplitter,
        producer: P,
        consumer: C,
    ) -> C::Result
    where
        P: Producer,
        C: Consumer<P::Item>,
    {
        if consumer.full() {
            consumer.into_folder().complete()
        } else if splitter.try_split(len, migrated) {
            let mid = len / 2;
            let (l_producer, r_producer) = producer.split_at(mid);
            let (l_consumer, r_consumer, reducer) = consumer.split_at(mid);
            let (l_result, r_result) = join_context(
                |f_cx: FnContext| helper(mid, f_cx.migrated, splitter, l_producer, l_consumer),
                |f_cx: FnContext| {
                    helper(len - mid, f_cx.migrated, splitter, r_producer, r_consumer)
                },
            );
            reducer.reduce(l_result, r_result)
        } else {
            producer.fold_with(consumer.into_folder()).complete()
        }
    }
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/rayon-core/src/join/mod.rs#L115
fn join_context<L, R, Lr, Rr>(l_f: L, r_f: R) -> (Lr, Rr)
where
    L: FnOnce(FnContext) -> Lr + Send,
    R: FnOnce(FnContext) -> Rr + Send,
    Lr: Send,
    Rr: Send,
{
    let cx = unsafe { SUB_CONTEXT.get().as_ref() };

    // Puts 'Right task' into local queue.
    let r_holder = ParTaskHolder::new(r_f);
    let r_task = unsafe { ParTask::new(&r_holder) };
    let r_task_id = r_task.id();
    cx.local.push(Task::Par(r_task));

    // Nofifies new task to another worker.
    //
    // TODO: Optimize.
    // compare to rayon, too many steal operations take place.
    // The more unnecessary steal operations, the poorer performance.
    // I guess this frequent notification is one of the reasons.
    // Anyway, I mitigated it by reducing split count.
    // See `Splitter::try_split`.
    let mut status = cx.injector.status.lock().unwrap();
    status.has_ready_task = true;
    cx.injector.signal_to_sub.notify_one();
    drop(status);

    // Executes 'Left task'.
    #[cfg(not(target_arch = "wasm32"))]
    let l_res = {
        let executor = std::panic::AssertUnwindSafe(move || l_f(FnContext::NOT_MIGRATED));
        match std::panic::catch_unwind(executor) {
            Ok(l_res) => l_res,
            Err(payload) => {
                // Panicked in `Left task`.
                // But we need to hold `Right task` until it's finished
                // if it was stolen by another worker.
                if let Some(task) = cx.local.pop() {
                    debug_assert_eq!(task.id(), r_task_id);
                } else {
                    while !r_holder.is_executed() {
                        std::thread::yield_now();
                    }
                }
                std::panic::resume_unwind(payload);
            }
        }
    };

    // In web, we don't have a way to hold `Right task` when
    // `Left task` panics.
    #[cfg(target_arch = "wasm32")]
    let l_res = l_f(FnContext::NOT_MIGRATED);

    // If we could find a task from the local queue, it must be 'Right task',
    // because the queue is LIFO fashion.
    if let Some(task) = cx.local.pop() {
        debug_assert_eq!(task.id(), r_task_id);
        r_task.execute(FnContext::NOT_MIGRATED);
    } else {
        // We couldn't find a task from local queue.
        // That means that another worker has stolen 'Right task'.
        // While we wait for 'Right task' to be finished by the another worker,
        // steals some tasks and executes them.
        while !r_holder.is_executed() {
            let mut steal = cx.search_siblings();
            cx.work(&mut steal);
            // TODO: Busy waiting if it failed to steal tasks.
        }
    }

    match unsafe { r_holder.return_or_panic_unchecked() } {
        Ok(r_res) => (l_res, r_res),
        Err(payload) => std::panic::resume_unwind(payload),
    }
}
