//! This example shows how to do paralell computation in ecs.

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
    const END: i64 = 10_000_000;
    const NUM: i64 = END - START + 1;
    const SUM: i64 = (START + END) * NUM / 2;

    let pool = WorkerPool::with_default();
    let num_workers = pool.len();
    let mut ecs = Ecs::default(pool);

    // Puts in numbers.
    ecs.register_entity_of::<Ea>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        crate::log!("Inserting numbers... It will take some time.");
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
        crate::log!("Completed insertion.");
    })
    .unwrap();

    // Computes in parallel.
    ecs.append_once_system(0, move |r: Read<Fa>| {
        let start = Instant::now();

        // Computes sum using rayon's parallel iterator.
        // Visit the link below to see what rayon is.
        // https://github.com/rayon-rs/rayon
        let r = r.take();
        let par_iter = r.par_iter().flatten();
        let sum: i64 = par_iter.map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        crate::log!("Summation took {elapsed:?} with parallel iterator on {num_workers} workers.");
    })
    .unwrap();
    ecs.run_default();

    // For the sake of comparison, computes in sequential as well.
    ecs.append_once_system(0, |r: Read<Fa>| {
        let start = Instant::now();

        // Computes sum using rust sequential iterator.
        let r = r.take();
        let seq_iter = r.iter().flatten();
        let sum: i64 = seq_iter.map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        crate::log!("Summation took {elapsed:?} with sequential iterator.");
    })
    .unwrap();
    ecs.run_default();
}
