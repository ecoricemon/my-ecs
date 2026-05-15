//! Compare parallel and sequential iteration over ECS component data.
//!
//! The example stores a lot of integers as `Ca` components, sums them once with ECS-aware rayon
//! parallel iteration, then sums the same data again with a normal sequential iterator.
//!
//! The exact timings depend on your machine, but the output shows both the parallel and sequential
//! durations.

use my_ecs::prelude::*;
use std::time::Instant;

// Each entity stores one number. The filter lets systems read those numbers.
#[derive(Entity, Clone, Copy)]
struct Ea {
    a: Ca,
}
#[derive(Component, Clone, Copy)]
struct Ca(i64);
filter!(Fa, Target = Ca);

fn main() {
    const START: i64 = 0;
    const END: i64 = 10_000_000;
    const NUM: i64 = END - START + 1;
    const SUM: i64 = (START + END) * NUM / 2;

    let pool = WorkerPool::with_all_cpus();
    let num_workers = pool.len();
    let mut ecs = Ecs::create(pool, [num_workers]);

    ecs.register_entity_of::<Ea>()
        // Fill the ECS storage with a large range of numbers to make the timing visible.
        .add_once_system(|ew: EntWrite<Ea>| {
            let mut ew = ew.take_recur();
            ew.resize(NUM as usize, Ea { a: Ca(0) });
            let mut col = ew.get_column_mut_of::<Ca>().unwrap();
            for (ca, val) in col.iter_mut().zip(START..=END) {
                ca.0 = val;
            }
        })
        // Sum the same ECS component data with rayon-backed parallel iteration.
        .add_once_system(move |r: Read<Fa>| {
            let start = Instant::now();

            // `into_ecs_par()` adapts rayon's parallel iterator to the ECS worker pool.
            // https://github.com/rayon-rs/rayon
            let mut sum = 0_i64;
            for getter in r.iter() {
                sum += getter.par_iter().into_ecs_par().map(|ca| ca.0).sum::<i64>();
            }
            assert_eq!(sum, SUM);

            println!(
                "Summation took {:?} with parallel iterator on {num_workers} workers.",
                start.elapsed()
            );
        })
        .step();

    // Run a sequential pass afterward so the output gives an easy comparison.
    ecs.add_once_system(|r: Read<Fa>| {
        let start = Instant::now();

        // This reads the same ECS data, but only uses normal single-thread iteration.
        let sum: i64 = r.iter().flatten().map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        println!(
            "Summation took {:?} with sequential iterator.",
            start.elapsed()
        );
    })
    .step();
}
