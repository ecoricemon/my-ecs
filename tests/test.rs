use async_io::Timer;
use my_ecs::prelude::*;
use std::{
    sync::{Arc, Mutex},
    time::Duration,
};

// === Defines number of workers ===
const NUM_WORKERS: usize = 3;

#[test]
fn test_async_wait() {
    // Creates instance.
    let worker_pool = WorkerPool::with_len(NUM_WORKERS);
    let mut ecs = Ecs::default(worker_pool);

    let state = Arc::new(Mutex::new(0));
    let c_state = state.clone();

    ecs.append_once_system(0, move || {
        let future = async move {
            // state 1: a bit of awaiting.
            *c_state.lock().unwrap() = 1;
            for millis in 1..10 {
                Timer::after(Duration::from_millis(millis)).await;
            }

            // state 2: all awaiting has done.
            *c_state.lock().unwrap() = 2;

            let c2_state = c_state.clone();
            let cmd = move |_: Ecs| {
                // state 3: executing command that the future generated.
                *c2_state.lock().unwrap() = 3;
            };
            cmd.into_boxed()
        };
        schedule_future(future);
    })
    .unwrap();

    // Waits until all tasks are executed completely.
    while !ecs
        .run()
        .call(0, &mut |run| run.schedule())
        .wait_for_idle()
        .is_empty()
    {}

    // Aborts remaining tasks, but we've done all.
    drop(ecs);

    // state must have reached state 3.
    assert_eq!(*state.lock().unwrap(), 3);
}

#[test]
fn test_async_abort() {
    // Creates instance.
    let worker_pool = WorkerPool::with_len(NUM_WORKERS);
    let mut ecs = Ecs::default(worker_pool);

    let state = Arc::new(Mutex::new(0));
    let c_state = state.clone();

    ecs.append_once_system(0, move || {
        let future = async move {
            // state 1: reachable.
            *c_state.lock().unwrap() = 1;
            for millis in 1..10_000 {
                Timer::after(Duration::from_millis(millis)).await;
            }

            // state 2: unreachable due to aborting.
            *c_state.lock().unwrap() = 2;
            (|_: Ecs| {}).into_boxed()
        };
        schedule_future(future);
    })
    .unwrap();

    // Future task may be executed a few times.
    ecs.run_default();

    // Aborts remaining tasks.
    drop(ecs);

    // state must have aborted before state 2.
    assert_eq!(*state.lock().unwrap(), 1);
}
