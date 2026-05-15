//! Post async work from a system and apply the result back to the ECS instance.
//!
//! This example starts with a system that posts `register_map()` through the built-in `Post`
//! resource. The async function pretends to load map data, then returns a command. When the future
//! completes, the command stores the map as a resource and queues another system that prints it.
//!
//! This is the basic pattern for async work that produces data ECS systems should use later.
//!
//! Expected output:
//!
//! ```text
//! 01000
//! 01010
//! 01010
//! 01010
//! 00010
//! ```

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    native::run();
}

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use my_ecs::prelude::*;
    use my_ecs::utils::test_utils::TimerFuture;
    use std::time::Duration;

    pub(super) fn run() {
        // The ECS instance owns the worker threads that will poll posted futures.
        let mut ecs = Ecs::create(WorkerPool::with_len(3), [3]);

        // A system can post async work through the built-in `Post` resource.
        ecs.add_once_system(|rr: ResRead<Post>| rr.send_future(register_map()))
            .unwrap();

        // `run` keeps the scheduler alive until the posted future and its command finish.
        ecs.run(|_| {});
    }

    #[derive(Resource)]
    struct Map(Vec<Vec<char>>);

    impl Map {
        fn new(data: &str) -> Self {
            Self(data.lines().map(|line| line.chars().collect()).collect())
        }

        fn print(&self) {
            for row in self.0.iter() {
                for c in row.iter() {
                    print!("{c}");
                }
                println!();
            }
        }
    }

    async fn register_map() -> impl Command {
        // Pretend this delay is async file or network I/O.
        TimerFuture::after(Duration::from_millis(10)).await;

        // The async task has produced data that should be inserted back into ECS.
        let map_data = "\
            01000\n\
            01010\n\
            01010\n\
            01010\n\
            00010"
            .to_owned();

        // Futures cannot directly mutate the ECS instance. They return a command that the scheduler
        // applies on the ECS thread when the future completes.
        let f = move |mut ecs: Ecs| {
            // Store the loaded map as a resource so later systems can read it.
            let map = Map::new(&map_data);
            ecs.add_resource(map)
                .into_result()
                .map_err(EcsError::without_data)?;

            // Queue one more system to prove the resource is available.
            ecs.add_once_system(show_map).into_result()?;
            Ok(())
        };
        Ok(f)
    }

    fn show_map(rr: ResRead<Map>) {
        rr.print();
    }
}

#[cfg(target_arch = "wasm32")]
fn main() {}
