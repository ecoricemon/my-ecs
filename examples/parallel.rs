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

    let pool = WorkerPool::with_num_cpus();
    let num_workers = pool.len();
    let mut ecs = Ecs::default(pool, [num_workers]);

    // Puts in numbers.
    ecs.register_entity_of::<Ea>().unwrap();
    ecs.add_system(SystemDesc::new().with_once(|mut ew: EntWrite<Ea>| {
        println!("Inserting numbers... It will take some time.");
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
        println!("Completed insertion.");
    }))
    .unwrap();

    // Computes in parallel.
    ecs.add_system(SystemDesc::new().with_once(move |r: Read<Fa>| {
        let start = Instant::now();

        // Computes sum using rayon's parallel iterator. Visit this link to see
        // what rayon is. https://github.com/rayon-rs/rayon
        let sum: i64 = r.take().par_iter().flatten().map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        println!("Summation took {elapsed:?} with parallel iterator on {num_workers} workers.");
    }))
    .unwrap();
    ecs.run().schedule_all();

    // For the sake of comparison, computes in sequential as well.
    ecs.add_system(SystemDesc::new().with_once(|r: Read<Fa>| {
        let start = Instant::now();

        // Computes sum using rust sequential iterator.
        let sum: i64 = r.take().iter().flatten().map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);

        let elapsed = start.elapsed();
        println!("Summation took {elapsed:?} with sequential iterator.");
    }))
    .unwrap();
    ecs.run().schedule_all();
}
