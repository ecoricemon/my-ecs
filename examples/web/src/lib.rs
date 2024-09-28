#![cfg(target_arch = "wasm32")]

use my_ecs::prelude::*;
use std::panic;
use wasm_bindgen::prelude::*;

// Declares Entity, Component, and Filter.
#[derive(Entity)]
struct Ea {
    a: Ca,
}
#[derive(Component)]
struct Ca(i64);
filter!(Fa, Target = Ca);

#[wasm_bindgen]
pub struct App {
    _m_worker: Option<MainWorker>,
}

#[wasm_bindgen]
impl App {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        // Shows panic messages on browser console.
        panic::set_hook(Box::new(|info| {
            console_error_panic_hook::hook(info);
            web_panic_hook(info);
        }));

        // Spawns main worker and its children.
        let m_worker = MainWorkerBuilder::new().spawn().unwrap();
        let num_workers = web_util::available_parallelism();
        m_worker.spawn_children(num_workers);

        // Tests simple summation with sequential and parallel iterators.
        m_worker.with_worker_pool(|pool| {
            const START: i64 = 0;
            const END: i64 = 2_000_000;
            const NUM: i64 = END - START + 1;
            const SUM: i64 = (START + END) * NUM / 2;

            let num_workers = pool.len();
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
                let start = web_util::now().unwrap();

                let r = r.take();
                let seq_iter = r.iter().flatten();
                let sum: i64 = seq_iter.map(|ca| ca.0).sum();
                assert_eq!(sum, SUM);

                let elapsed = web_util::now().unwrap() - start;
                crate::log!("Summation took {elapsed:?} with sequential iterator.");
            })
            .unwrap();
            ecs.run_default();

            // Tests simple summation with parallel iterator.
            ecs.append_once_system(0, move |r: Read<Fa>| {
                let start = web_util::now().unwrap();

                let r = r.take();
                let par_iter = r.par_iter().flatten();
                let sum: i64 = par_iter.map(|ca| ca.0).sum();
                assert_eq!(sum, SUM);

                let elapsed = web_util::now().unwrap() - start;
                crate::log!(
                    "Summation took {elapsed:?} with parallel iterator on {num_workers} workers."
                );
            })
            .unwrap();
            ecs.run_default();
        });

        Self {
            _m_worker: Some(m_worker),
        }
    }
}
