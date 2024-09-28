#![allow(dead_code)]

use my_ecs::prelude::*;

// === Defines `Component` ===
#[derive(Component)]
struct Ca(i32);

#[derive(Component)]
struct Cb(i32);

#[derive(Component)]
struct Cc(i32);

// === Defines `Entity` ===
#[derive(Entity)]
struct Ea {
    a: Ca,
}

#[derive(Entity)]
struct Eb {
    a: Ca,
    b: Cb,
}

#[derive(Entity)]
struct Ec {
    c: Cc,
}

// === Defines `Filter` ===
filter!(Fa, Target = Ca);
filter!(Fb, Target = Cb);

// === Defines `Resource` ===
#[derive(Resource)]
struct Ra(String);

#[derive(Resource)]
struct Rb(String);

const NUM_WORKERS: usize = 10;

fn try_open_close(worker_pool: WorkerPool) -> WorkerPool {
    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    const REPEAT: usize = 10;

    // Opens and closes workers without doing something.
    for _ in 0..REPEAT {
        let _ = ecs.run();
    }

    ecs.take_worker_pool()
}

fn worker_pool() -> WorkerPool {
    WorkerPool::with_len(NUM_WORKERS)
}

fn main() {
    try_open_close(worker_pool());

    use std::time::SystemTime;
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap();
    println!("Done at {now:?}");
}
