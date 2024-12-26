use futures::{channel::oneshot, select, FutureExt};
use my_ecs::prelude::*;
use std::{
    thread,
    time::{Duration, Instant},
};

fn main() {
    good_example();
    bad_example();
}

fn good_example() {
    // Creates instance with two groups.
    let mut ecs = Ecs::default(WorkerPool::with_len(2), [1, 1]);

    let (exit_tx, exit_rx) = oneshot::channel();

    // Runs as follows.
    // - Async io tasks in group 0.
    // - Compute tasks in group 1.

    ecs.add_once(move || schedule_future(async_io_server(exit_rx)))
        .add_once(move || schedule_future(async_io_client(exit_tx)))
        .add_system(SystemDesc::new().with_group_index(1).with_once(|| {
            schedule_future(async_compute());
            schedule_future(async_compute());
        }))
        .unwrap();

    print!("[GOOD example] ");
    while !ecs.run().schedule_all().wait_for_idle().is_completed() {}
}

fn bad_example() {
    // Creates instance.
    let mut ecs = Ecs::default(WorkerPool::with_len(2), [2]);

    let (exit_tx, exit_rx) = oneshot::channel();

    // Runs as follows.
    // - Async io tasks in group 0.
    // - Compute tasks in group 0.

    ecs.add_once(move || schedule_future(async_io_server(exit_rx)))
        .add_once(|| {
            schedule_future(async_compute());
            schedule_future(async_compute());
        })
        .add_once(move || {
            schedule_future(async_io_client(exit_tx));
        })
        .unwrap();

    print!("[BAD example] ");
    while !ecs.run().schedule_all().wait_for_idle().is_completed() {}
}

// Function that needs to respond quickly.
async fn async_io_server(exit_rx: oneshot::Receiver<()>) -> EcsResult<()> {
    let mut server = tide::new();
    server.at("/health").get(|_| async { Ok("ok") });

    select! {
        _ = server.listen("127.0.0.1:8080").fuse() => {},
        _ = exit_rx.fuse() => {},
    };
    Ok(())
}

// Function that hopes quick response.
async fn async_io_client(exit_tx: oneshot::Sender<()>) -> EcsResult<()> {
    let start = Instant::now();

    let body = surf::get("http://127.0.0.1:8080/health")
        .await?
        .body_string()
        .await?;
    assert_eq!(&body, "ok");

    let elapsed = start.elapsed();
    println!("GET /health : Took {elapsed:?}");

    drop(exit_tx);
    Ok(())
}

// Function that takes a little bit long.
async fn async_compute() -> EcsResult<()> {
    thread::sleep(Duration::from_secs(1));
    Ok(())
}
