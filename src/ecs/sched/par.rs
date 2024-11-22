use super::{
    ctrl::SUB_CONTEXT,
    task::{ParTask, ParTaskHolder, TaskId},
};
use crate::ds;
use rayon::iter::{
    plumbing::{Consumer, Folder, Producer, ProducerCallback, Reducer, UnindexedConsumer},
    IndexedParallelIterator, ParallelIterator,
};
use std::marker::PhantomData;

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/rayon-core/src/lib.rs#L851
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct FnContext {
    migrated: bool,
}

impl FnContext {
    pub(super) const MIGRATED: Self = Self { migrated: true };
    pub(super) const NOT_MIGRATED: Self = Self { migrated: false };
}

// ref: https://github.com/rayon-rs/rayon/blob/7543ed40c9a017dee32b3dc72b3ae819820e8366/src/iter/plumbing/mod.rs#L255C1-L255C18
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
struct Splitter {
    splits: usize,
}

impl Splitter {
    fn new() -> Option<Self> {
        let ptr = SUB_CONTEXT.get();
        (!ptr.is_dangling()).then(|| {
            // Safety: `ptr` is a valid pointer.
            Self {
                splits: unsafe { ptr.as_ref().comm().num_siblings() },
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

    let r_holder = ParTaskHolder::new(r_f);
    let r_task = unsafe { ParTask::new(&r_holder) };
    let r_task_id = TaskId::Parallel(r_task);

    // Puts 'Right task' into local queue and nofifies it to another worker.
    //
    // TODO: Optimize.
    // compare to rayon, too many steal operations take place.
    // The more unnecessary steal operations, the poorer performance.
    // I guess this frequent notification is one of the reasons.
    // Anyway, I mitigated it by reducing split count.
    // See `Splitter::try_split`.
    cx.comm().push_parallel_task(r_task);
    cx.comm().signal().sub().notify_one();

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
                if let Some(task) = cx.comm().pop_local() {
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
    if let Some(task) = cx.comm().pop_local() {
        debug_assert_eq!(task.id(), r_task_id);
        r_task.execute(FnContext::NOT_MIGRATED);
    } else {
        // We couldn't find a task from local queue.
        // That means that another worker has stolen 'Right task'.
        // While we wait for 'Right task' to be finished by the another worker,
        // steals some tasks and executes them.
        while !r_holder.is_executed() {
            let mut steal = cx.comm().search();
            cx.work(&mut steal);
            // TODO: Busy waiting if it failed to steal tasks.
        }
    }

    match unsafe { r_holder.return_or_panic_unchecked() } {
        Ok(r_res) => (l_res, r_res),
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// Wrapper of rayon's parallel iterator.
///
/// rayon's parallel iterator basically uses its own worker registry. It means
/// that rayon will spawn new workers regardless of living workers in ecs, which
/// may not be something you wish.  
/// To use ecs's workers instead, just wrap the iterator in this wrapper.
/// Then, this wrapper will intercept calls to registry and switch it to ecs's.
#[repr(transparent)]
pub struct EcsPar<I>(pub I);

// Implements rayon's traits for iterators.
mod impl_iter {
    use super::*;

    impl<I> ParallelIterator for EcsPar<I>
    where
        I: ParallelIterator + IndexedParallelIterator,
    {
        type Item = I::Item;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            // Intercepts
            bridge(self, consumer)
        }
    }

    impl<I> IndexedParallelIterator for EcsPar<I>
    where
        I: IndexedParallelIterator,
    {
        #[inline]
        fn len(&self) -> usize {
            self.0.len()
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            // Intercepts
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            self.0.with_producer(callback)
        }
    }

    impl<I> Producer for EcsPar<I>
    where
        I: Producer,
    {
        type Item = I::Item;
        type IntoIter = I::IntoIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (l, r) = self.0.split_at(index);
            (Self(l), Self(r))
        }
    }

    impl ParallelIterator for ds::raw::ParRawIter {
        type Item = ds::ptr::SendSyncPtr<u8>;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl IndexedParallelIterator for ds::raw::ParRawIter {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl Producer for ds::raw::ParRawIter {
        type Item = ds::ptr::SendSyncPtr<u8>;
        type IntoIter = ds::raw::RawIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let l_cur = self.cur;
            let l_end = unsafe { self.cur.add(index * self.stride) };
            let r_cur = l_end;
            let r_end = self.end;

            // Safety: Splitting is safe.
            let (l, r) = unsafe {
                (
                    ds::raw::RawIter::new(l_cur.as_nonnull(), l_end.as_nonnull(), self.stride),
                    ds::raw::RawIter::new(r_cur.as_nonnull(), r_end.as_nonnull(), self.stride),
                )
            };
            (l.into_par(), r.into_par())
        }
    }

    impl<'a, T: Send + Sync> ParallelIterator for ds::raw::ParIter<'a, T> {
        type Item = &'a T;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl<'a, T: Send + Sync> IndexedParallelIterator for ds::raw::ParIter<'a, T> {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl<'a, T: Send + Sync> Producer for ds::raw::ParIter<'a, T> {
        type Item = &'a T;
        type IntoIter = ds::raw::Iter<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (l, r) = self.inner.split_at(index);
            unsafe { (Self::from_raw(l), Self::from_raw(r)) }
        }
    }

    impl<'a, T: Send + Sync> ParallelIterator for ds::raw::ParIterMut<'a, T> {
        type Item = &'a mut T;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl<'a, T: Send + Sync> IndexedParallelIterator for ds::raw::ParIterMut<'a, T> {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl<'a, T: Send + Sync> Producer for ds::raw::ParIterMut<'a, T> {
        type Item = &'a mut T;
        type IntoIter = ds::raw::IterMut<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (l, r) = self.inner.split_at(index);
            (
                Self {
                    inner: l,
                    _marker: PhantomData,
                },
                Self {
                    inner: r,
                    _marker: PhantomData,
                },
            )
        }
    }

    impl ParallelIterator for ds::raw::ParFlatRawIter {
        type Item = ds::ptr::SendSyncPtr<u8>;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl IndexedParallelIterator for ds::raw::ParFlatRawIter {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl Producer for ds::raw::ParFlatRawIter {
        type Item = ds::ptr::SendSyncPtr<u8>;
        type IntoIter = ds::raw::FlatRawIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (
                ds::raw::RawIter {
                    cur: ml, end: mr, ..
                },
                mi,
                off,
            ) = unsafe { (self.fn_find)(self.this.as_nonnull(), self.off + index) };
            let mm = unsafe { ml.add(off * self.stride) };

            // Basic idea to split is somthing like so,
            //
            // Left chunk      Mid chunk         Right chunk
            //      li              mi                ri
            // [**********] .. [**********]  ..  [**********]
            // ^          ^    ^     ^    ^      ^          ^
            // ll         lr   ml    mm   mr     rl         rr
            // |          |    |     ||    \     |          |
            // [**********] .. [*****][*****] .. [**********]
            // |---- Left child -----||---- Right child ----|
            //
            // But, we must consider something like
            // - Imagine that mid chunk is left chunk, but not splitted
            //   as depectied below.
            //
            // ml              mm   mr
            // v               v    v
            // [********************]
            //              [****]
            //              ^    ^
            //              ll   lr

            let is_left_chunk_cut = mi + 1 == self.li;
            let lchild = if !is_left_chunk_cut {
                ds::raw::FlatRawIter {
                    ll: self.ll,
                    lr: self.lr,
                    rl: ml,
                    rr: mm,
                    this: self.this,
                    li: self.li,
                    ri: mi,
                    fn_iter: self.fn_iter,
                    fn_find: self.fn_find,
                    stride: self.stride,
                    off: self.off,
                    len: index,
                }
            } else {
                ds::raw::FlatRawIter {
                    ll: self.ll,
                    lr: mm,
                    rl: self.ll,
                    rr: mm,
                    this: self.this,
                    li: mi + 1,
                    ri: mi,
                    fn_iter: self.fn_iter,
                    fn_find: self.fn_find,
                    stride: self.stride,
                    off: self.off,
                    len: index,
                }
            };

            let is_right_chunk_cut = mi == self.ri;
            let rchild = if !is_right_chunk_cut {
                ds::raw::FlatRawIter {
                    ll: mm,
                    lr: mr,
                    rl: self.rl,
                    rr: self.rr,
                    this: self.this,
                    li: mi + 1,
                    ri: self.ri,
                    fn_iter: self.fn_iter,
                    fn_find: self.fn_find,
                    stride: self.stride,
                    off: self.off + index,
                    len: self.len - index,
                }
            } else {
                ds::raw::FlatRawIter {
                    ll: mm,
                    lr: self.rr,
                    rl: mm,
                    rr: self.rr,
                    this: self.this,
                    li: mi + 1,
                    ri: mi,
                    fn_iter: self.fn_iter,
                    fn_find: self.fn_find,
                    stride: self.stride,
                    off: self.off + index,
                    len: self.len - index,
                }
            };

            (lchild.into_par(), rchild.into_par())
        }
    }

    impl<'a, T: Send + Sync> ParallelIterator for ds::raw::ParFlatIter<'a, T> {
        type Item = &'a T;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl<'a, T: Send + Sync> IndexedParallelIterator for ds::raw::ParFlatIter<'a, T> {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl<'a, T: Send + Sync> Producer for ds::raw::ParFlatIter<'a, T> {
        type Item = &'a T;
        type IntoIter = ds::raw::FlatIter<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (l, r) = self.inner.split_at(index);
            // Safety: Splitting doesn't affect both type and lifetime.
            unsafe { (Self::from_raw(l), Self::from_raw(r)) }
        }
    }

    impl<'a, T: Send + Sync> ParallelIterator for ds::raw::ParFlatIterMut<'a, T> {
        type Item = &'a mut T;

        #[inline]
        fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where
            C: UnindexedConsumer<Self::Item>,
        {
            bridge(self, consumer)
        }
    }

    impl<'a, T: Send + Sync> IndexedParallelIterator for ds::raw::ParFlatIterMut<'a, T> {
        #[inline]
        fn len(&self) -> usize {
            Self::len(self)
        }

        #[inline]
        fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
            bridge(self, consumer)
        }

        #[inline]
        fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
            callback.callback(self)
        }
    }

    impl<'a, T: Send + Sync> Producer for ds::raw::ParFlatIterMut<'a, T> {
        type Item = &'a mut T;
        type IntoIter = ds::raw::FlatIterMut<'a, T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.into_seq()
        }

        #[inline]
        fn split_at(self, index: usize) -> (Self, Self) {
            let (l, r) = self.inner.split_at(index);
            // Safety: Splitting doesn't affect both type and lifetime.
            unsafe { (Self::from_raw(l), Self::from_raw(r)) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rayon::prelude::*;

    /// Wraps rayon's parallel iterators in an interceptor.
    #[test]
    fn test_ecspar() {
        // Array
        let iter: rayon::array::IntoIter<i32, 2> = [0, 1].into_par_iter();
        EcsPar(iter);
        // Range
        let iter: rayon::range::Iter<i32> = (0..2).into_par_iter();
        EcsPar(iter);
        // Slice
        let iter: &rayon::slice::Iter<i32> = &[0, 1][..].into_par_iter();
        EcsPar(iter);
        // Zip
        let range_iter0: rayon::range::Iter<i32> = (0..2).into_par_iter();
        let range_iter1: rayon::range::Iter<i32> = (0..2).into_par_iter();
        let zip_iter = range_iter0.zip(range_iter1);
        EcsPar(zip_iter);
    }
}
