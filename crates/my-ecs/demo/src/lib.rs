#![cfg(target_arch = "wasm32")]
#![allow(static_mut_refs, dead_code)]

mod mandelbrot_cpu;
mod common;

use mandelbrot_cpu::*;
use common::*;

use my_ecs::prelude::*;
use my_ecs::utils::web::{available_parallelism, worker_post_message};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct App {
    cpu_main: Option<MainWorker>,
}

#[wasm_bindgen]
impl App {
    #[wasm_bindgen(constructor)]
    pub fn new(ty: &str) -> Self {
        std::panic::set_hook(Box::new(|info| {
            console_error_panic_hook::hook(info);
            global::web_panic_hook(info);
        }));

        clear_global();

        let cpu_main = match ty {
            "btnCpu" => Some(Self::init_cpu_worker(available_parallelism())),
            "btnSingleWorker" => Some(Self::init_cpu_worker(1)),
            _ => panic!(),
        };

        Self { cpu_main }
    }

    fn init_cpu_worker(num_workers: usize) -> MainWorker {
        let main = MainWorkerBuilder::new()
            .with_name("cpu-main")
            .spawn()
            .unwrap();
        main.spawn_children(num_workers);
        main.init_app(|pool| {
            let num_workers = pool.len();
            let mut ecs = Ecs::create(pool, [num_workers]);
            ecs.add_system(SystemDesc::new().with_system(|| {
                let mut slot = cpu_slot();
                let args = slot.args;
                calc(&mut slot.buf, args);
            }))
            .unwrap();
            ecs
        });
        main
    }

    #[wasm_bindgen(js_name = "setOnMessage")]
    pub fn set_onmessage(&self, f: &js_sys::Function) {
        if let Some(main) = self.cpu_main.as_ref() {
            let callback = f.clone();
            main.set_on_message(move |_| {
                callback.call0(&JsValue::null()).unwrap();
            });
        }
    }

    #[wasm_bindgen(js_name = "getResult")]
    pub fn get_result(&self, dst: &mut [u8]) -> String {
        if let Ok(mut pool) = POOL.try_lock() {
            match pool.take_ready_data() {
                ReadyData::Ready(buf) => {
                    assert!(dst.len() >= buf.len());
                    dst[..buf.len()].copy_from_slice(&buf[..]);
                    return "ready".to_owned();
                }
                ReadyData::None => {}
            }
        }
        "none".to_owned()
    }

    #[wasm_bindgen(js_name = "calcImageOnCpu")]
    pub fn calc_image_on_cpu(
        &mut self,
        age: u32,
        x_low: f32,
        x_high: f32,
        y_low: f32,
        y_high: f32,
    ) {
        let main = self.cpu_main.as_mut().unwrap();
        main.with_app(move |mut ecs| {
            let mut data = load_to_cpu_slot(age);
            data.args = Arguments::new((x_low, x_high), (y_low, y_high));
            drop(data);
            ecs.step();
            unload_from_cpu_slot();
            worker_post_message(&JsValue::undefined()).unwrap();
        });
    }

    #[wasm_bindgen]
    pub fn destroy(&mut self) {
        self.cpu_main.take();
    }
}
