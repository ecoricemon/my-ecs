#![cfg(target_arch = "wasm32")]
#![allow(static_mut_refs, dead_code)]

mod mandelbrot;
use mandelbrot::*;

use my_ecs::prelude::*;
use wasm_bindgen::prelude::*;

// Currently, it's hard to synchronize b/w JS and Rust using something like
// Mutex because JS window context cannot stop.
static mut ARGS: Args = const { Args::new() };
static mut BUF: Vec<u8> = const { Vec::new() };

#[wasm_bindgen]
pub struct App {
    main: Option<MainWorker>,
    buf: Vec<u8>,
}

#[wasm_bindgen]
impl App {
    #[wasm_bindgen(constructor)]
    pub fn new(num_workers: usize) -> Self {
        std::panic::set_hook(Box::new(|info| {
            console_error_panic_hook::hook(info);
            web_panic_hook(info);
        }));

        let main = MainWorkerBuilder::new().spawn().unwrap();
        main.spawn_children(num_workers);
        main.init_ecs(|pool| {
            let num_workers = pool.len();
            let mut ecs = Ecs::default(pool, [num_workers]);
            ecs.add_system(SystemDesc::new().with_system(|| {
                unsafe { calc(ARGS, &mut BUF) };
            }))
            .unwrap();
            ecs.into_raw()
        });

        Self {
            main: Some(main),
            buf: Vec::new(),
        }
    }

    #[wasm_bindgen(js_name = "setOnMessage")]
    pub fn set_onmessage(&self, f: &js_sys::Function) {
        let f = f.clone();
        if let Some(main) = self.main.as_ref() {
            main.set_onmessage(move |_| {
                f.call0(&JsValue::null()).unwrap();
            });
        }
    }

    #[wasm_bindgen(js_name = "getResult")]
    pub fn get_result(&self, dest: &mut [u8]) {
        let buf = unsafe { &BUF };
        assert!(dest.len() >= buf.len());
        dest[..buf.len()].copy_from_slice(&buf[..]);
    }

    #[wasm_bindgen(js_name = "calcImage")]
    pub fn calc_image(
        &mut self,
        width: u32,
        height: u32,
        x_low: f64,
        x_high: f64,
        y_low: f64,
        y_high: f64,
    ) {
        let args = unsafe { &mut ARGS };
        let buf = unsafe { &mut BUF };
        args.set_size(width, height);
        args.set_plot_range((x_low, x_high), (y_low, y_high));
        buf.resize((width * height * 4) as usize, 0);

        if let Some(main) = self.main.as_mut() {
            main.with_ecs(|mut ecs| {
                ecs.schedule_all();
                web_util::worker_post_message(&JsValue::undefined()).unwrap();
            });
        }
    }

    #[wasm_bindgen]
    pub fn destroy(&mut self) {
        self.main.take();
    }
}
