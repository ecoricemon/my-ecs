#![allow(dead_code)]

use my_ecs::prelude::*;
use rayon::iter::plumbing::*;
use std::{
    cmp,
    marker::PhantomData,
    ptr::NonNull,
    thread,
    time::{Duration, Instant},
};

// const N: u64 = 1000 * 1000 * 10;
const N: u64 = 1000 * 1000;
const CHUNK_SIZE: usize = 4 * 1024;
const MIN_CHUNK_LEN: usize = 8;
const TH_NUM: usize = 2;

fn main() {
    test_ecs_iter();

    // test_my_thread();

    if false {
        for _ in 0..100 {
            println!("-------- test_primitive_iter --------");
            test_primitive_iter();

            println!("-------- normal --------");
            normal();

            std::thread::sleep(Duration::from_millis(1000));
        }
    }
}

fn test_ecs_iter() {
    let mut ecs = Ecs::new();

    // Spawns workers.
    let mut workers = (0..TH_NUM)
        .map(|i| WorkerBuilder::new(&format!("worker{i}")).spawn().unwrap())
        .collect::<Vec<_>>();

    ecs.register_entity_of::<Ent>();
    ecs.append_once_system(0, |ew: EntWrite<Ent>| {
        let mut ew = ew.take();
        for i in 0..N {
            ew.add_entity(Ent { a: Comp::new(i) });
        }
    })
    .unwrap();

    // test_ecs_iter_seq(&mut ecs, &mut workers);
    test_ecs_iter_par(&mut ecs, &mut workers);
}

fn test_ecs_iter_par(ecs: &mut Ecs<std::hash::RandomState, 1>, workers: &mut [Worker]) {
    let live = NonZeroTick::new(1).unwrap();
    ecs.append_system(0, live, true, |r: Read<Fx>| {
        let start = Instant::now();
        let iter = r.take().par_iter().flatten();
        let (low, high, sum) = ParallelIterator::fold(
            iter,
            || (u64::MAX, u64::MIN, 0),
            |(low, high, sum), x| {
                let x = &x.value;
                let low = low.min(*x);
                let high = high.max(*x);
                let sum = sum + *x;
                (low, high, sum)
            },
        )
        .reduce(
            || (u64::MAX, u64::MIN, 0),
            |a, b| {
                let low = a.0.min(b.0);
                let high = a.1.max(b.1);
                let sum = a.2 + b.2;
                (low, high, sum)
            },
        );
        println!(
            "[ECS P]\t\trange: ({low}, {high}), sum: {sum}, took: {:?}",
            start.elapsed().as_micros()
        );
    })
    .unwrap();

    ecs.with_worker(workers).operate(&mut |x| x.schedule());
}

fn test_ecs_iter_seq(ecs: &mut Ecs<std::hash::RandomState, 1>, workers: &mut [Worker]) {
    let live = NonZeroTick::new(1).unwrap();
    ecs.append_system(0, live, true, |r: Read<Fx>| {
        let start = Instant::now();
        let (mut low, mut high, mut sum) = (u64::MAX, u64::MIN, 0);

        for getter in r.take().iter() {
            let iter = getter.iter();
            for comp in iter {
                low = low.min(comp.value);
                high = high.max(comp.value);
                sum += comp.value;
            }
        }

        println!(
            "[ECS]\t\trange: ({low}, {high}), sum: {sum}, took: {:?}",
            start.elapsed().as_micros()
        );
    })
    .unwrap();

    ecs.with_worker(workers).operate(&mut |x| x.schedule());
}

fn test_my_thread() {
    let cont = Container::new(N);
    let start = Instant::now();
    let (low, high, sum) = cont
        .par_iter()
        .fold(
            || (u64::MAX, u64::MIN, 0),
            |(low, high, sum), x| {
                let low = low.min(*x);
                let high = high.max(*x);
                let sum = sum + *x;
                (low, high, sum)
            },
        )
        .reduce(
            || (u64::MAX, u64::MIN, 0),
            |a, b| {
                let low = a.0.min(b.0);
                let high = a.1.max(b.1);
                let sum = a.2 + b.2;
                (low, high, sum)
            },
        );
    println!(
        "[xxx]\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

// ===================== sequential

struct Data<T>(T);

struct Container<T> {
    v: Vec<Data<T>>,
}
impl Container<u64> {
    fn new(n: u64) -> Self {
        Self {
            v: (0..n).map(Data).collect(),
        }
    }
}
impl<T> Container<T> {
    fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }

    fn par_iter(&self) -> ParIter<T> {
        self.iter().into_par()
    }
}

struct Iter<'a, T: 'a> {
    cur: NonNull<T>,
    end: NonNull<T>,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> Iter<'a, T> {
    fn new(cont: &'a Container<T>) -> Self {
        let cur = NonNull::new(cont.v.as_ptr() as *mut T).unwrap();
        let len = cont.v.len();
        let end = unsafe { cur.add(len) };
        unsafe { Self::from_raw(cur, end) }
    }

    unsafe fn from_raw(cur: NonNull<T>, end: NonNull<T>) -> Self {
        Self {
            cur,
            end,
            _marker: PhantomData,
        }
    }

    #[inline]
    const fn len(&self) -> usize {
        unsafe {
            let diff = self.end.offset_from(self.cur);
            diff as usize
        }
    }

    fn into_par(self) -> ParIter<'a, T> {
        ParIter {
            cur: self.cur,
            end: self.end,
            _marker: PhantomData,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.end {
            unsafe {
                let res = Some(self.cur.as_ref());
                self.cur = self.cur.add(1);
                res
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = Self::len(self);
        (len, Some(len))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        Self::len(self)
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.cur < self.end {
            unsafe {
                self.end = self.end.sub(1);
                let res = Some(self.end.as_ref());
                res
            }
        } else {
            None
        }
    }
}

// ============================== Impl rayon

impl<'data, T: Send + Sync + 'data> IntoParallelRefIterator<'data> for Container<T> {
    type Item = &'data T;
    type Iter = ParIter<'data, T>;

    fn par_iter(&'data self) -> Self::Iter {
        self.par_iter()
    }
}

// ============================== Parallel Iterator

struct ParIter<'a, T: 'a> {
    cur: NonNull<T>,
    end: NonNull<T>,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> ParIter<'a, T> {
    fn into_seq(self) -> Iter<'a, T> {
        Iter {
            cur: self.cur,
            end: self.end,
            _marker: PhantomData,
        }
    }
}

unsafe impl<'a, T> Send for ParIter<'a, T> {}

impl<'a, T: Send + Sync> ParallelIterator for ParIter<'a, T> {
    type Item = &'a T; // Enforces Sync.

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        println!("main::ParIter::drive_unindexed");
        bridge(self, consumer)
    }
}

impl<'a, T: Send + Sync> IndexedParallelIterator for ParIter<'a, T> {
    fn len(&self) -> usize {
        unsafe { self.end.offset_from(self.cur) as usize }
    }

    fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
        println!("main::ParIter::drive");
        bridge(self, consumer)
    }

    fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
        println!("main::ParIter::with_producer");
        let producer = unsafe { ParIterProd::from_raw(self.cur, self.end) };
        callback.callback(producer)
    }
}

// ============================== Parallel Iterator Producer

struct ParIterProd<'a, T: 'a> {
    cur: NonNull<T>,
    end: NonNull<T>,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> ParIterProd<'a, T> {
    unsafe fn from_raw(cur: NonNull<T>, end: NonNull<T>) -> Self {
        Self {
            cur,
            end,
            _marker: PhantomData,
        }
    }
}

unsafe impl<'a, T> Send for ParIterProd<'a, T> {}

impl<'a, T> Producer for ParIterProd<'a, T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            cur: self.cur,
            end: self.end,
            _marker: PhantomData,
        }
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let l_cur = self.cur;
        let l_end = unsafe { self.cur.add(index) };
        let r_cur = l_end;
        let r_end = self.end;

        unsafe { (Self::from_raw(l_cur, l_end), Self::from_raw(r_cur, r_end)) }
    }
}

// struct ParIterMut<'a, T>(ParIter<'a, T>);

// impl<'a, T: Send + Sync> ParallelIterator for ParIterMut<'a, T> {
//     type Item = &'a mut T;
//     fn drive_unindexed<C>(self, consumer: C) -> C::Result
//     where
//         C: UnindexedConsumer<Self::Item>
//     {
//         bridge()
//         self.0.b
//     }
// }

// fn my_bridge<I, C>(par_iter: I, consumer: C) -> C::Result
// where
//     I: IndexedParallelIterator,
//     C: Consumer<I::Item>,
// {
//     let len = par_iter.len();
//     return par_iter.with_producer(Callback { len, consumer });

//     struct Callback<C> {
//         len: usize,
//         consumer: C,
//     }

//     impl<C, I> ProducerCallback<I> for Callback<C>
//     where
//         C: Consumer<I>,
//     {
//         type Output = C::Result;
//         fn callback<P>(self, producer: P) -> C::Result
//         where
//             P: Producer<Item = I>,
//         {
//             my_bridge_producer_consumer(self.len, producer, self.consumer)
//         }
//     }
// }

// fn my_bridge_producer_consumer<P, C>(len: usize, producer: P, consumer: C) -> C::Result
// where
//     P: Producer,
//     C: Consumer<P::Item>,
// {
//     let splitter = LengthSplitter::new(producer.min_len(), producer.max_len(), len);
//     return helper(len, false, splitter, producer, consumer);

//     fn helper<P, C>(
//         len: usize,
//         migrated: bool,
//         mut splitter: LengthSplitter,
//         producer: P,
//         consumer: C,
//     ) -> C::Result
//     where
//         P: Producer,
//         C: Consumer<P::Item>,
//     {
//         if consumer.full() {
//             consumer.into_folder().complete()
//         } else if splitter.try_split(len, migrated) {
//             let mid = len / 2;
//             let (left_producer, right_producer) = producer.split_at(mid);
//             let (left_consumer, right_consumer, reducer) = consumer.split_at(mid);
//             let (left_result, right_result) = join_context(
//                 |context| {
//                     helper(
//                         mid,
//                         context.migrated(),
//                         splitter,
//                         left_producer,
//                         left_consumer,
//                     )
//                 },
//                 |context| {
//                     helper(
//                         len - mid,
//                         context.migrated(),
//                         splitter,
//                         right_producer,
//                         right_consumer,
//                     )
//                 },
//             );
//             reducer.reduce(left_result, right_result)
//         } else {
//             producer.fold_with(consumer.into_folder()).complete()
//         }
//     }
// }

fn test_primitive_iter() {
    test_vec();
    test_any();
    test_any_par();
    test_chunk_any();
    test_chunk_any_par();
}

fn test_vec() {
    let vec: Vec<u64> = (0..N).collect();

    // === iter
    let (mut low, mut high, mut sum) = (u64::MAX, u64::MIN, 0);
    let start = Instant::now();
    for x in vec.iter() {
        low = low.min(*x);
        high = high.max(*x);
        sum += *x;
    }

    println!(
        "[Vec]\t\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

fn test_any() {
    let tinfo = tinfo!(u64);
    let mut any = AnyVec::new(tinfo);
    for i in 0..N {
        any.push(i);
    }

    let (mut low, mut high, mut sum) = (u64::MAX, u64::MIN, 0);
    let start = Instant::now();
    let iter = any.iter_of::<u64>();
    for x in iter {
        low = low.min(*x);
        high = high.max(*x);
        sum += *x;
    }

    println!(
        "[AnyVec]\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

fn test_any_par() {
    let tinfo = tinfo!(u64);
    let mut any = AnyVec::new(tinfo);
    for i in 0..N {
        any.push(i);
    }
    let start = Instant::now();
    let iter = any.par_iter_of::<u64>();
    let (low, high, sum) = ParallelIterator::fold(
        iter,
        || (u64::MAX, u64::MIN, 0),
        |(low, high, sum), x| {
            let low = low.min(*x);
            let high = high.max(*x);
            let sum = sum + *x;
            (low, high, sum)
        },
    )
    .reduce(
        || (u64::MAX, u64::MIN, 0),
        |a, b| {
            let low = a.0.min(b.0);
            let high = a.1.max(b.1);
            let sum = a.2 + b.2;
            (low, high, sum)
        },
    );
    println!(
        "[AnyVec P]\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

fn test_chunk_any() {
    let tinfo = tinfo!(u64);
    let chunk_len = (CHUNK_SIZE / tinfo.size).next_power_of_two();
    let chunk_len = cmp::max(chunk_len, MIN_CHUNK_LEN);

    let mut chunk_any = ChunkAnyVec::new(tinfo, chunk_len);
    for i in 0..N {
        chunk_any.push(i);
    }

    let (mut low, mut high, mut sum) = (u64::MAX, u64::MIN, 0);
    let start = Instant::now();

    for x in chunk_any.iter_of::<u64>() {
        low = low.min(*x);
        high = high.max(*x);
        sum += *x;
    }

    println!(
        "[ChunkAnyVec]\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

fn test_chunk_any_par() {
    let tinfo = tinfo!(u64);
    let chunk_len = (CHUNK_SIZE / tinfo.size).next_power_of_two();
    let chunk_len = cmp::max(chunk_len, MIN_CHUNK_LEN);

    let mut chunk_any = ChunkAnyVec::new(tinfo, chunk_len);
    for i in 0..N {
        chunk_any.push(i);
    }

    let start = Instant::now();

    let iter = chunk_any.par_iter_of::<u64>();
    let (low, high, sum) = ParallelIterator::fold(
        iter,
        || (u64::MAX, u64::MIN, 0),
        |(low, high, sum), x| {
            let low = low.min(*x);
            let high = high.max(*x);
            let sum = sum + *x;
            (low, high, sum)
        },
    )
    .reduce(
        || (u64::MAX, u64::MIN, 0),
        |a, b| {
            let low = a.0.min(b.0);
            let high = a.1.max(b.1);
            let sum = a.2 + b.2;
            (low, high, sum)
        },
    );

    println!(
        "[ChunkAnyVec P]\trange: ({low}, {high}), sum: {sum}, took: {:?}",
        start.elapsed().as_micros()
    );
}

fn normal() {
    let mut ecs = Ecs::new();

    // Spawns workers.
    let mut workers = (0..TH_NUM)
        .map(|i| WorkerBuilder::new(&format!("worker{i}")).spawn().unwrap())
        .collect::<Vec<_>>();

    let live: NonZeroTick = NonZeroTick::new(5000).unwrap();
    let volatile: bool = true;

    ecs.register_entity_of::<Ea>();
    ecs.register_entity_of::<Eb>();
    ecs.append_once_system(0, insert_ea).unwrap();
    ecs.append_once_system(0, insert_eb).unwrap();
    ecs.append_system(0, live, volatile, inc_ca).unwrap();
    ecs.append_system(0, live, volatile, dec_ca).unwrap();
    ecs.append_system(0, live, volatile, iter_ca).unwrap();
    ecs.append_system(0, live, volatile, iter_ca).unwrap();
    ecs.append_system(0, live, volatile, inc_ca).unwrap();
    ecs.append_system(0, live, volatile, dec_ca).unwrap();
    ecs.append_system(0, live, volatile, iter_ca).unwrap();
    ecs.append_system(0, live, volatile, iter_ca).unwrap();

    #[derive(Resource, Debug)]
    struct Ra(String);
    ecs.register_resource(
        Ra::key(),
        MaybeOwned::A(Box::new(Ra("A".to_owned()))),
        false,
    )
    .unwrap();

    let mut outside = Ra("outside".to_owned());

    let f = move |w: ResWrite<Ra>| {
        let w = w.take();

        outside.0.push('+');
        std::mem::swap(w, &mut outside);
        drop(outside);
    };

    ecs.append_once_system(0, f).unwrap();

    ecs.operate(&mut workers);
}

#[derive(Component, Debug, Clone, Copy)]
struct Ca(i32);
#[derive(Component, Debug, Clone, Copy)]
struct Cb(i32);
#[derive(Entity, Debug)]
struct Ea {
    a: Ca,
}
#[derive(Entity, Debug)]
struct Eb {
    a: Ca,
    b: Cb,
}
filter!(Fa, Target = Ca);
filter!(Fb, Target = Cb);
filter!(CaWithCb, Target = Ca, All = (Ca, Cb));
filter!(CaWithoutCb, Target = Ca, None = Cb);

fn insert_ea(ew: EntWrite<Ea>) {
    let mut ew = ew.take();
    ew.add_entity(Ea { a: Ca(1) });
    ew.add_entity(Ea { a: Ca(2) });
}

fn insert_eb(ew: EntWrite<Eb>) {
    let mut ew = ew.take();
    ew.add_entity(Eb {
        a: Ca(3),
        b: Cb(10),
    });
    ew.add_entity(Eb {
        a: Ca(4),
        b: Cb(20),
    });
}

fn inc_ca(w: Write<Fa>) {
    let mut test = [0; 4];
    let mut i = 0;

    for mut getter in w.take().iter_mut() {
        for ca in getter.iter_mut() {
            ca.0 += 1;

            test[i] = ca.0;
            i += 1;
        }
    }

    test.sort_unstable();
    assert_eq!(test, [2, 3, 4, 5]);
    println!("inc_ca OK on thread {:?}", thread::current().id());
}

fn dec_ca(w: Write<Fa>) {
    let mut test = [0; 4];
    let mut i = 0;

    for mut getter in w.take().iter_mut() {
        for ca in getter.iter_mut() {
            ca.0 -= 1;

            test[i] = ca.0;
            i += 1;
        }
    }

    test.sort_unstable();
    assert_eq!(test, [1, 2, 3, 4]);
    println!("dec_ca OK on thread {:?}", thread::current().id());
}

fn iter_ca(r: Read<Fa>) {
    let mut test = [0; 4];
    let mut i = 0;

    for getter in r.take().iter() {
        for ca in getter.iter() {
            test[i] = ca.0;
            i += 1;
        }
    }

    test.sort_unstable();
    assert_eq!(test, [1, 2, 3, 4]);
    println!("iter_ca OK on thread {:?}", thread::current().id());
}

#[derive(Entity, Debug)]
struct Ent {
    a: Comp,
}
#[derive(Component, Debug)]
#[repr(transparent)]
struct Comp {
    value: u64,
}
impl Comp {
    fn new(value: u64) -> Self {
        Self { value }
    }
}
filter!(Fx, Target = Comp);

// === TEMP BEGIN ===

use rayon::iter::{
    plumbing::{Consumer, Folder, Producer, ProducerCallback, Reducer},
    IndexedParallelIterator,
};

// rayon copy.
pub fn bridge<I, C>(par_iter: I, consumer: C) -> C::Result
where
    I: IndexedParallelIterator,
    C: Consumer<I::Item>,
{
    println!("XXXXXXXXXXXXX par::bridge");
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

pub fn bridge_producer_consumer<P, C>(len: usize, producer: P, consumer: C) -> C::Result
where
    P: Producer,
    C: Consumer<P::Item>,
{
    println!("XXXXXXXXXXXXX par::bridge_producer_consumer");

    // @@@ TODO
    // let splitter = LengthSplitter::new(producer.min_len(), producer.max_len(), len);
    // return helper(len, false, splitter, producer, consumer);

    return helper(len, false, producer, consumer);

    fn helper<P, C>(len: usize, migrated: bool, producer: P, consumer: C) -> C::Result
    where
        P: Producer,
        C: Consumer<P::Item>,
    {
        if consumer.full() {
            consumer.into_folder().complete()
        } else if len > 1 {
            let mid = len / 2;
            let (left_producer, right_producer) = producer.split_at(mid);
            let (left_consumer, right_consumer, reducer) = consumer.split_at(mid);
            let (left_result, right_result) = rayon::join_context(
                |context| helper(mid, context.migrated(), left_producer, left_consumer),
                |context| {
                    helper(
                        len - mid,
                        context.migrated(),
                        right_producer,
                        right_consumer,
                    )
                },
            );
            reducer.reduce(left_result, right_result)
        } else {
            producer.fold_with(consumer.into_folder()).complete()
        }
    }
}

// === TEMP END ===
