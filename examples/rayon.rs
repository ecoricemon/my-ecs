#![allow(dead_code)]

use my_ecs::prelude::*;
use std::time::Instant;

// Declares Entity, Component, and Filter.
#[derive(Entity)]
struct Ea {
    a: Ca,
}
#[derive(Component)]
struct Ca(i64);
filter!(Fa, Target = Ca);

fn main() {
    const START: i64 = 0;
    const END: i64 = 20_000_000;
    const NUM: i64 = END - START + 1;
    const SUM: i64 = (START + END) * NUM / 2;

    let pool = WorkerPool::with_default();
    let num_threads = pool.len();
    let mut ecs = Ecs::default(pool);

    // Puts numbers into ecs storage.
    ecs.register_entity_of::<Ea>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        crate::log!("Inserting numbers...");
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
        crate::log!("Completed insertion.");
    })
    .unwrap();

    // Tests simple summation with sequential iterator.
    ecs.append_once_system(0, |r: Read<Fa>| {
        let start = Instant::now();

        let r = r.take();
        let seq_iter = r.iter().flatten();
        let sum: i64 = seq_iter.map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        crate::log!("Summation took {elapsed:?} with sequential iterator.");
    })
    .unwrap();
    ecs.run_default();

    // Tests simple summation with parallel iterator.
    ecs.append_once_system(0, move |r: Read<Fa>| {
        let start = Instant::now();

        let r = r.take();
        let par_iter = r.par_iter().flatten();
        let sum: i64 = par_iter.map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        crate::log!("Summation took {elapsed:?} with parallel iterator on {num_threads} threads.");
    })
    .unwrap();
    ecs.run_default();
}
