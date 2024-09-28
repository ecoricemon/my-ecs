#![allow(dead_code)]

use my_ecs::prelude::*;

// === Defines number of workers ===
const NUM_WORKERS: usize = 5;

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

// === Defines test primitives ===

/// Systems can have five types of parameters, which are
/// 1. Read<Filter>
/// 2. Write<Filter>
/// 3. ResRead<Resource>
/// 4. ResWrite<Resource>
/// 5. EntWrite<Entity>
///
/// Tests if we're able to register those parameter combinations.
#[rustfmt::skip]
fn try_register_fn_system(worker_pool: WorkerPool) -> WorkerPool {
    use paste::paste;

    let mut ecs = Ecs::default(worker_pool);

    const LIVE: NonZeroTick = NonZeroTick::MAX;
    const VOLATILE: bool = true;

    // Registers resources and entities.
    ecs.register_resource(
        Ra::key(),
        MaybeOwned::A(Box::new(Ra("A".to_owned()))),
        false,
    )
    .unwrap();
    ecs.register_resource(
        Rb::key(),
        MaybeOwned::A(Box::new(Ra("A".to_owned()))),
        false,
    )
    .unwrap();
    ecs.register_entity_of::<Ec>();

    let s = String::new();

    macro_rules! test {
        (
            $(r=$r:ident)? 
            $(w=$w:ident)? 
            $(rr=$rr:ident)? 
            $(rw=$rw:ident)? 
            $(ew=$ew:ident)?
        ) => {
            paste! {
                ecs.append_system(0, LIVE, VOLATILE,
                    |
                        $([<_ $r>]: Read<Fa>,)? 
                        $([<_ $w>]: Write<Fb>,)? 
                        $([<_ $rr>]: ResRead<Ra>,)? 
                        $([<_ $rw>]: ResWrite<Rb>,)? 
                        $([<_ $ew>]: EntWrite<Ec>,)?
                    | {}
                ).unwrap();

                let c_s = s.clone();
                ecs.append_once_system(0,
                    move |
                        $([<_ $r>]: Read<Fa>,)? 
                        $([<_ $w>]: Write<Fb>,)? 
                        $([<_ $rr>]: ResRead<Ra>,)? 
                        $([<_ $rw>]: ResWrite<Rb>,)? 
                        $([<_ $ew>]: EntWrite<Ec>,)?
                    | { drop(c_s); }
                ).unwrap();
            }
        };
    }

    // o, o, o, o, o
    test!();
    // R, o, o, o, o
    test!(r=r);
    // o, W, o, o, o
    test!(w=w);
    // R, W, o, o, o
    test!(r=r w=w);
    // o, o, RR, o, o
    test!(rr=rr);
    // R, o, RR, o, o
    test!(r=r rr=rr);
    // o, W, RR, o, o
    test!(w=w rr=rr);
    // R, W, RR, o, o
    test!(r=r w=w rr=rr);
    // o, o, o, RW, o
    test!(rw=rw);
    // R, o, o, RW, o
    test!(r=r rw=rw);
    // o, W, o, RW, o
    test!(w=w rw=rw);
    // R, W, o, RW, o
    test!(r=r w=w rw=rw);
    // o, o, RR, RW, o
    test!(rr=rr rw=rw);
    // R, o, RR, RW, o
    test!(r=r rr=rr rw=rw);
    // o, W, RR, RW, o
    test!(w=w rr=rr rw=rw);
    // R, W, RR, RW, o
    test!(r=r w=w rr=rr rw=rw);
    // o, o, o, o, EW
    test!(ew=ew);
    // R, o, o, o, EW
    test!(r=r ew=ew);
    // o, W, o, o, EW
    test!(w=w ew=ew);
    // R, W, o, o, EW
    test!(r=r w=w ew=ew);
    // o, o, RR, o, EW
    test!(rr=rr ew=ew);
    // R, o, RR, o, EW
    test!(r=r rr=rr ew=ew);
    // o, W, RR, o, EW
    test!(w=w rr=rr ew=ew);
    // R, W, RR, o, EW
    test!(r=r w=w rr=rr ew=ew);
    // o, o, o, RW, EW
    test!(rw=rw ew=ew);
    // R, o, o, RW, EW
    test!(r=r rw=rw ew=ew);
    // o, W, o, RW, EW
    test!(w=w rw=rw ew=ew);
    // R, W, o, RW, EW
    test!(r=r w=w rw=rw ew=ew);
    // o, o, RR, RW, EW
    test!(rr=rr rw=rw ew=ew);
    // R, o, RR, RW, EW
    test!(r=r rr=rr rw=rw ew=ew);
    // o, W, RR, RW, EW
    test!(w=w rr=rr rw=rw ew=ew);
    // R, W, RR, RW, EW
    test!(r=r w=w rr=rr rw=rw ew=ew);

    ecs.take_worker_pool()
}

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

fn try_schedule(worker_pool: WorkerPool) -> WorkerPool {
    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    // Registers and inserts entities.
    ecs.register_entity_of::<Ea>();
    ecs.register_entity_of::<Eb>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        ew.add_entity(Ea { a: Ca(1) });
        ew.add_entity(Ea { a: Ca(2) });
    })
    .unwrap();
    ecs.append_once_system(0, |mut ew: EntWrite<Eb>| {
        ew.add_entity(Eb {
            a: Ca(3),
            b: Cb(10),
        });
        ew.add_entity(Eb {
            a: Ca(4),
            b: Cb(20),
        });
    })
    .unwrap();

    // Registers resources.
    ecs.register_resource(
        Ra::key(),
        MaybeOwned::A(Box::new(Ra("A".to_owned()))),
        false,
    )
    .unwrap();
    ecs.register_resource(
        Rb::key(),
        MaybeOwned::A(Box::new(Ra("A".to_owned()))),
        false,
    )
    .unwrap();

    // Test.
    let live = NonZeroTick::MAX;
    let volatile: bool = true;
    ecs.append_system(0, live, volatile, inc_ca).unwrap();
    ecs.append_system(0, live, volatile, inc_cb).unwrap();
    ecs.append_system(0, live, volatile, dec_ca).unwrap();
    ecs.append_system(0, live, volatile, dec_cb).unwrap();
    ecs.append_system(0, live, volatile, iter_ca).unwrap();
    ecs.append_system(0, live, volatile, iter_cb).unwrap();
    ecs.append_system(0, live, volatile, attach_ra).unwrap();
    ecs.append_system(0, live, volatile, detach_ra).unwrap();

    ecs.run_default();

    assert!(ecs.collect_poisoned_systems().is_empty());

    return ecs.take_worker_pool();

    // === Internal struct and functions ===

    /// Increases `Ca` by 1.
    fn inc_ca(w: Write<Fa>) {
        let mut w = w.take();
        w.iter_mut().flatten().for_each(|ca| ca.0 += 1);

        let mut vals: Vec<i32> = w.iter().flatten().map(|ca| ca.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [2, 3, 4, 5]);
    }

    /// Decreases `Ca` by 1.
    fn dec_ca(w: Write<Fa>) {
        let mut w = w.take();
        w.iter_mut().flatten().for_each(|ca| ca.0 -= 1);

        let mut vals: Vec<i32> = w.iter().flatten().map(|ca| ca.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [1, 2, 3, 4]);
    }

    // Iterates over `Ca`.
    fn iter_ca(r: Read<Fa>) {
        let r = r.take();
        let mut vals: Vec<i32> = r.iter().flatten().map(|ca| ca.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [1, 2, 3, 4]);
    }

    /// Increases `Cb` by 1.
    fn inc_cb(w: Write<Fb>) {
        let mut w = w.take();
        w.iter_mut().flatten().for_each(|cb| cb.0 += 1);

        let mut vals: Vec<i32> = w.iter().flatten().map(|cb| cb.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [11, 21]);
    }

    /// Decreases `Cb` by 1.
    fn dec_cb(w: Write<Fb>) {
        let mut w = w.take();
        w.iter_mut().flatten().for_each(|cb| cb.0 -= 1);

        let mut vals: Vec<i32> = w.iter().flatten().map(|cb| cb.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [10, 20]);
    }

    // Iterates over `Cb`.
    fn iter_cb(r: Read<Fb>) {
        let r = r.take();
        let mut vals: Vec<i32> = r.iter().flatten().map(|cb| cb.0).collect();
        vals.sort_unstable();
        assert_eq!(vals, [10, 20]);
    }

    // Attaches a letter to `Ra`.
    fn attach_ra(w: ResWrite<Ra>) {
        let w = w.take();
        w.0.push('A');
        assert_eq!(w.0, "AA");
    }

    // Detaches a letter from `Ra`.
    fn detach_ra(w: ResWrite<Ra>) {
        let w = w.take();
        w.0.pop();
        assert_eq!(w.0, "A");
    }
}

fn try_command(worker_pool: WorkerPool) -> WorkerPool {
    use std::sync::{Arc, Mutex};

    const REPEAT: usize = 5;

    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    // Counts number of system execution appended by a command.
    let count = Arc::new(Mutex::new(0));
    let c_count = Arc::clone(&count);

    // Puts a command in a system.
    ecs.append_once_system(0, move || {
        // Command will append a system at the end of cycle.
        cmd::put_command(|mut ecs: Ecs| {
            ecs.append_system(0, NonZeroTick::MAX, true, move || {
                let mut c = c_count.lock().unwrap();
                *c += 1;
            })
            .unwrap();
        });
    })
    .unwrap();

    // Repeats running.
    for _ in 0..REPEAT {
        ecs.run_default();
    }

    // Why REPEAT - 1?
    //
    // In the first run, the system was not registered yet.
    assert_eq!(*count.lock().unwrap(), REPEAT - 1);

    ecs.take_worker_pool()
}

fn try_parallel_task(worker_pool: WorkerPool) -> WorkerPool {
    const START: i32 = 0;
    const END: i32 = 10_000;
    const NUM: i32 = END - START + 1;
    const SUM: i32 = ((START as i64 + END as i64) * NUM as i64 / 2) as i32;

    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    // Registers and inserts entities.
    ecs.register_entity_of::<Ea>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
    })
    .unwrap();

    // Test.
    ecs.append_once_system(0, |r: Read<Fa>| {
        let r = r.take();
        let par_iter = r.par_iter().flatten();
        let sum = par_iter
            .fold(|| 0_i32, |sum, ca| sum + ca.0)
            .reduce(|| 0_i32, |sum_a, sum_b| sum_a + sum_b);
        assert_eq!(sum, SUM);
    })
    .unwrap();

    ecs.run_default();

    assert!(ecs.collect_poisoned_systems().is_empty());

    ecs.take_worker_pool()
}

fn try_recover_from_panic(worker_pool: WorkerPool) -> (WorkerPool, i32) {
    const START: i32 = 0;
    const END: i32 = 10;
    const NUM: i32 = END - START + 1;
    const SUM: i32 = ((START as i64 + END as i64) * NUM as i64 / 2) as i32;

    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    // Registers and inserts entities.
    ecs.register_entity_of::<Ea>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
    })
    .unwrap();

    // Registers resources.
    ecs.register_resource(Ra::key(), MaybeOwned::A(Box::new(Ra("".to_owned()))), false)
        .unwrap();

    // Registers systems.
    const LIVE: NonZeroTick = NonZeroTick::MAX;
    const VOLATILE: bool = true;

    let ok_sys = |r: Read<Fa>, rw: ResWrite<Ra>| {
        let rw = rw.take();
        rw.0.push('x');
        let r = r.take();
        let sum: i32 = r.iter().flatten().map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);
    };
    let fail_sys = |_w: Write<Fa>| panic!("Panics on purpose");

    let sid_ok_a = ecs.append_system(0, LIVE, VOLATILE, ok_sys).unwrap();
    let sid_fail = ecs.append_system(0, LIVE, VOLATILE, fail_sys).unwrap();
    let sid_ok_b = ecs.append_system(0, LIVE, VOLATILE, ok_sys).unwrap();

    ecs.run_default();
    let poisoned = ecs.collect_poisoned_systems();

    assert_eq!(poisoned.len(), 1);
    assert_eq!(sid_fail, poisoned[0].0.id());

    ecs.run_default();

    // TODO: check system len.

    assert!(ecs.inactivate_system(0, &sid_ok_a).is_ok());
    assert!(ecs.inactivate_system(0, &sid_ok_b).is_ok());

    ecs.append_once_system(0, |rr: ResRead<Ra>| {
        let rr = rr.take();
        assert_eq!(rr.0.len(), 4);
    })
    .unwrap();

    const NUM_EXPECTED_PANICS: i32 = 1;
    (ecs.take_worker_pool(), NUM_EXPECTED_PANICS)
}

fn try_recover_from_panic_in_parallel_task(worker_pool: WorkerPool) -> (WorkerPool, i32) {
    const START: i32 = 0;
    const END: i32 = 10_000;
    const NUM: i32 = END - START + 1;
    const SUM: i32 = ((START as i64 + END as i64) * NUM as i64 / 2) as i32;

    // Creates instance.
    let mut ecs = Ecs::default(worker_pool);

    // Registers and inserts entities.
    ecs.register_entity_of::<Ea>();
    ecs.append_once_system(0, |mut ew: EntWrite<Ea>| {
        for val in START..=END {
            ew.add_entity(Ea { a: Ca(val) });
        }
    })
    .unwrap();

    // Registers resources.
    ecs.register_resource(Ra::key(), MaybeOwned::A(Box::new(Ra("".to_owned()))), false)
        .unwrap();

    // Registers systems.
    const LIVE: NonZeroTick = NonZeroTick::MAX;
    const VOLATILE: bool = true;

    let ok_sys = |r: Read<Fa>, rw: ResWrite<Ra>| {
        let rw = rw.take();
        rw.0.push('x');
        let r = r.take();
        let sum: i32 = r.iter().flatten().map(|ca| ca.0).sum();
        assert_eq!(sum, SUM);
    };
    let fail_sys = |r: Read<Fa>| {
        let r = r.take();
        let par_iter = r.par_iter().flatten();
        let sum = par_iter
            .fold(
                || 0_i32,
                |sum, ca| {
                    if ca.0 == START + END / 2 {
                        panic!("Panic on purpose");
                    }
                    sum + ca.0
                },
            )
            .reduce(|| 0_i32, |sum_a, sum_b| sum_a + sum_b);
        assert_eq!(sum, SUM);
    };

    let sid_ok_a = ecs.append_system(0, LIVE, VOLATILE, ok_sys).unwrap();
    let sid_fail = ecs.append_system(0, LIVE, VOLATILE, fail_sys).unwrap();
    let sid_ok_b = ecs.append_system(0, LIVE, VOLATILE, ok_sys).unwrap();

    ecs.run_default();
    let poisoned = ecs.collect_poisoned_systems();

    assert_eq!(poisoned.len(), 1);
    assert_eq!(sid_fail, poisoned[0].0.id());

    ecs.run_default();

    // TODO: check system len.

    assert!(ecs.inactivate_system(0, &sid_ok_a).is_ok());
    assert!(ecs.inactivate_system(0, &sid_ok_b).is_ok());

    ecs.append_once_system(0, |rr: ResRead<Ra>| {
        let rr = rr.take();
        assert_eq!(rr.0.len(), 4);
    })
    .unwrap();

    const NUM_EXPECTED_PANICS: i32 = 1;
    (ecs.take_worker_pool(), NUM_EXPECTED_PANICS)
}

// === Non-web tests ===

#[cfg(not(target_arch = "wasm32"))]
mod non_web_test {
    use super::*;

    #[test]
    fn test_register_fn_system() {
        try_register_fn_system(worker_pool());
    }

    #[test]
    fn test_open_close() {
        try_open_close(worker_pool());
    }

    #[test]
    fn test_schedule() {
        try_schedule(worker_pool());
    }

    #[test]
    fn test_parallel_task() {
        try_parallel_task(worker_pool());
    }

    #[test]
    fn test_recover_from_panic() {
        try_recover_from_panic(worker_pool());
        try_recover_from_panic_in_parallel_task(worker_pool());
    }

    #[test]
    fn test_command() {
        try_command(worker_pool());
    }

    fn worker_pool() -> WorkerPool {
        WorkerPool::with_len(NUM_WORKERS)
    }
}

// === Web tests ===

#[cfg(target_arch = "wasm32")]
mod web_test {
    use super::*;
    use js_sys::JsString;
    use std::panic;
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen]
    pub struct Tester {
        m_worker: Option<MainWorker>,
    }

    #[wasm_bindgen]
    impl Tester {
        #[wasm_bindgen(constructor)]
        pub fn new() -> Self {
            // Shows panic messages on browser console.
            panic::set_hook(Box::new(|info| {
                console_error_panic_hook::hook(info);
                web_panic_hook(info);
            }));

            // Spawns main worker and its children.
            let mut m_worker = MainWorkerBuilder::new().spawn().unwrap();

            // Sends "complete" event once it recieved response from main worker.
            // Then JS module will destroy this struct and notify end of test
            // to playwright.
            const COMPLETE: &str = "complete";
            m_worker.set_onmessage(|data: JsValue| {
                if let Some(s) = data.dyn_ref::<JsString>() {
                    if s == COMPLETE || s == "panic" {
                        let ev = web_sys::CustomEvent::new(COMPLETE).unwrap();
                        let window = web_sys::window().unwrap();
                        window.dispatch_event(&ev).unwrap();
                        return;
                    }
                }
                panic!("unexpected response from main worker");
            });

            // Does all success tests.
            m_worker.spawn_children(NUM_WORKERS);
            m_worker.with_worker_pool(|worker_pool| {
                let mut total_panics = 0;

                let worker_pool = try_register_fn_system(worker_pool);
                Self::print_ok_with(&try_register_fn_system);

                let worker_pool = try_open_close(worker_pool);
                Self::print_ok_with(&try_open_close);

                let worker_pool = try_schedule(worker_pool);
                Self::print_ok_with(&try_schedule);

                let worker_pool = try_command(worker_pool);
                Self::print_ok_with(&try_command);

                let worker_pool = try_parallel_task(worker_pool);
                Self::print_ok_with(&try_parallel_task);

                let (_worker_pool, num_panics) = try_recover_from_panic(worker_pool);
                total_panics += num_panics;
                Self::print_ok_with(&try_recover_from_panic);

                // TODO: Test 'should panic' in web environment.
                // try_recover_from_panic_in_parallel_task();

                // Printing out a message that starts with "playwright"
                // is something like command to playwright.
                crate::log!("playwright:expectedPanics:{total_panics}");
                web_util::worker_post_message(&COMPLETE.into()).unwrap();
            });

            Self {
                m_worker: Some(m_worker),
            }
        }

        #[wasm_bindgen]
        pub fn destroy(&mut self) {
            self.m_worker.take();
        }

        fn print_ok_with<T: ?Sized>(_t: &T) {
            crate::log!("test {} ... ok", my_ecs::type_name!(_t));
        }
    }
}
