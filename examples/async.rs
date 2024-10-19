use async_io::Timer;
use my_ecs::prelude::*;
use std::time::Duration;

fn main() {
    // Creates instance.
    const NUM_WORKERS: usize = 3;
    let worker_pool = WorkerPool::with_len(NUM_WORKERS);
    let mut ecs = Ecs::default(worker_pool);

    // Schedules a future using once system.
    ecs.append_once_system(0, || {
        let future = register_map();
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
}

async fn register_map() -> Box<dyn Command> {
    // Assumes that we're reading map data from a file using async io function.
    Timer::after(Duration::from_millis(10)).await;

    // Now we got the data.
    let map_data = "\
        01000\n\
        01010\n\
        01010\n\
        01010\n\
        00010"
        .to_owned();

    // Declares a command using the data.
    let cmd = move |mut ecs: Ecs| {
        // Registers map resource.
        let map = Box::new(Map::new(&map_data));
        ecs.register_resource(Map::key(), MaybeOwned::A(map), false)
            .unwrap();

        // Appends a system that uses the map.
        ecs.append_once_system(0, show_map).unwrap();
    };

    // Returns command.
    cmd.into_boxed()
}

fn show_map(rr: ResRead<Map>) {
    let map = rr.take();
    map.print();
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
            println!("");
        }
    }
}
