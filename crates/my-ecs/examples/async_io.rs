//! Keep latency-sensitive async I/O separate from slow compute work.
//!
//! This example runs the same tiny HTTP health check twice. In `good_example`, I/O futures and
//! blocking compute futures are posted to separate worker groups, so the health check responds
//! quickly. In `bad_example`, all futures share one worker group, so slow compute work can delay
//! the I/O path.
//!
//! Expected output shape:
//!
//! ```text
//! [GOOD example] GET /health : Took ...
//! [BAD example] GET /health : Took ...
//! ```
//!
//! The exact timings depend on your machine, but the good example should be much faster.

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    native::run();
}

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use futures::{channel::oneshot, select, FutureExt};
    use my_ecs::prelude::*;
    use std::{
        thread,
        time::{Duration, Instant},
    };

    pub(super) fn run() {
        good_example();
        bad_example();
    }

    fn good_example() {
        // Split two worker threads into two groups so I/O and compute work do not block each other.
        let mut ecs = Ecs::create(WorkerPool::with_len(2), [1, 1]);

        let (exit_tx, exit_rx) = oneshot::channel();

        // Group 0 handles the server/client futures. Group 1 handles slow compute futures, so the
        // health check can respond quickly.
        ecs.add_once_systems((
            move |rr: ResRead<Post>| rr.send_future(async_io_server(exit_rx)),
            move |rr: ResRead<Post>| rr.send_future(async_io_client(exit_tx)),
        ))
        .add_system(
            SystemDesc::new()
                .with_group_index(1)
                .with_once(|rr: ResRead<Post>| {
                    rr.send_future(async_compute());
                    rr.send_future(async_compute());
                }),
        )
        .unwrap();

        print!("[GOOD example] ");
        ecs.run(|_| {});
    }

    fn bad_example() {
        // Put both workers in one group so every posted future competes for the same execution
        // slots.
        let mut ecs = Ecs::create(WorkerPool::with_len(2), [2]);

        let (exit_tx, exit_rx) = oneshot::channel();

        // The slow compute futures can delay the I/O future in this setup, which is why the
        // measured health check is slower than in `good_example`.
        ecs.add_once_systems((
            move |rr: ResRead<Post>| rr.send_future(async_io_server(exit_rx)),
            |rr: ResRead<Post>| {
                rr.send_future(async_compute());
                rr.send_future(async_compute());
            },
            move |rr: ResRead<Post>| {
                rr.send_future(async_io_client(exit_tx));
            },
        ))
        .unwrap();

        print!("[BAD example] ");
        ecs.run(|_| {});
    }

    // A tiny server stands in for latency-sensitive async I/O.
    async fn async_io_server(exit_rx: oneshot::Receiver<()>) -> DynResult<()> {
        let mut server = tide::new();
        server.at("/health").get(|_| async { Ok("ok") });

        select! {
            _ = server.listen("127.0.0.1:48080").fuse() => {},
            _ = exit_rx.fuse() => {},
        };
        Ok(())
    }

    // This measures how long the I/O path had to wait for worker time.
    async fn async_io_client(exit_tx: oneshot::Sender<()>) -> DynResult<()> {
        let start = Instant::now();

        let body = surf::get("http://127.0.0.1:48080/health")
            .await?
            .body_string()
            .await?;
        assert_eq!(&body, "ok");

        let elapsed = start.elapsed();
        println!("GET /health : Took {elapsed:?}");

        drop(exit_tx);
        Ok(())
    }

    // Blocking compute work is intentionally slow so the scheduling difference is visible.
    async fn async_compute() -> DynResult<()> {
        thread::sleep(Duration::from_secs(1));
        Ok(())
    }
}

#[cfg(target_arch = "wasm32")]
fn main() {}
