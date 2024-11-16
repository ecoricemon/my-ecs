use async_io::Timer;
use my_ecs::prelude::*;
use std::{
    hint,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
    thread,
    time::Duration,
};

macro_rules! decl_default_ent_comp_res_filter {
    () => {
        // Entities.
        #[allow(dead_code)]
        #[derive(Entity)]
        struct Ea {
            a: Ca,
            b: Cb,
        }

        #[allow(dead_code)]
        #[derive(Entity)]
        struct Eb {
            c: Cc,
        }

        // Components.
        #[allow(dead_code)]
        #[derive(Component)]
        struct Ca {
            val: i32,
        }

        #[allow(dead_code)]
        #[derive(Component)]
        struct Cb {
            val: i32,
        }

        #[allow(dead_code)]
        #[derive(Component)]
        struct Cc {
            val: i32,
        }

        // Resources.
        #[allow(dead_code)]
        #[derive(Resource)]
        struct Ra {
            val: i32,
        }

        #[allow(dead_code)]
        #[derive(Resource)]
        struct Rb {
            val: i32,
        }

        // Filters.
        filter!(Fa, Target = Ca);
        filter!(Fb, Target = Cb);
    };
}

#[test]
fn test_system_with_unknown() {
    decl_default_ent_comp_res_filter!();

    let mut ecs = Ecs::default(WorkerPool::with_len(1), [1]);

    // `Fa` is unknown, but it can be registered later.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Read<Fa>| {}));
    assert!(res.is_ok());

    // `Fa` is unknown, but it can be registered later.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<Fa>| {}));
    assert!(res.is_ok());

    // `Ra` is unknown. It should be `EcsError::UnknownResource`.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: ResRead<Ra>| {}));
    assert!(
        matches!(res, Err(EcsError::UnknownResource(..))),
        "{res:?} is not a EcsError::UnknownResource"
    );

    // `Ra` is unknown. It should be `EcsError::UnknownResource`.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: ResWrite<Ra>| {}));
    assert!(
        matches!(res, Err(EcsError::UnknownResource(..))),
        "{res:?} is not a EcsError::UnknownResource"
    );

    // `Ea` is unknown. It should be `EcsErrror::UnknownEntity`.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: EntWrite<Ea>| {}));
    assert!(
        matches!(res, Err(EcsError::UnknownEntity(..))),
        "{res:?} is not a EcsError::UnknownEntity"
    );
}

#[test]
fn test_async_wait() {
    // Creates instance.
    let mut ecs = Ecs::default(WorkerPool::with_len(3), [3]);

    let state = Arc::new(Mutex::new(0));
    let c_state = state.clone();

    ecs.add_system(SystemDesc::new().with_once(move || {
        schedule_future(async move {
            // state 1: A bit of awaiting.
            *c_state.lock().unwrap() = 1;
            for millis in 1..10 {
                Timer::after(Duration::from_millis(millis)).await;
            }

            // state 2: All awaiting has done.
            *c_state.lock().unwrap() = 2;

            let c2_state = c_state.clone();
            Ok(move |_: Ecs| {
                // state 3: Executing command that the future generated.
                *c2_state.lock().unwrap() = 3;
            })
        });
    }))
    .unwrap();

    // Waits until all tasks are executed completely.
    while !ecs.run().schedule_all().wait_for_idle().is_completed() {}
    drop(ecs);

    // `state` must have reached state 3.
    assert_eq!(*state.lock().unwrap(), 3);
}

#[test]
fn test_async_abort() {
    // Creates instance.
    let mut ecs = Ecs::default(WorkerPool::with_len(3), [3]);

    let state = Arc::new(Mutex::new(0));
    let c_state = state.clone();

    ecs.add_system(SystemDesc::new().with_once(move || {
        schedule_future(async move {
            // state 1: reachable.
            *c_state.lock().unwrap() = 1;
            for millis in 1..10_000 {
                Timer::after(Duration::from_millis(millis)).await;
            }

            // state 2: unreachable due to aborting.
            *c_state.lock().unwrap() = 2;
            Ok(())
        });
    }))
    .unwrap();

    // Future task may be executed a few times.
    ecs.run().schedule_all();

    // Aborts remaining tasks.
    drop(ecs);

    // `state` must be 1 due to aborting.
    assert_eq!(*state.lock().unwrap(), 1);
}

#[test]
fn test_request_lock() {
    const COUNT: u64 = 1000;

    // Creates instance.
    let mut ecs = Ecs::default(WorkerPool::with_len(3), [3]);

    // Registers a shared resource.
    #[derive(Resource)]
    struct Counter(i32);
    let mut cnt = Counter(0);
    let desc = unsafe { ResourceDesc::new().with_ptr(&mut cnt as *mut _) };
    ecs.register_resource(desc).unwrap();

    // An atomic variable to see exclusive access to the resource.
    let is_async = Arc::new(AtomicBool::new(false));
    let c_is_async = Arc::clone(&is_async);

    // A synchronous system writing something on the resource.
    ecs.add_system(
        SystemDesc::new()
            .with_activation(NonZeroTick::new(COUNT).unwrap(), InsertPos::Back)
            .with_system(move |rw: ResWrite<Counter>| {
                // Because of locking, even sync tasks cannot get executed while
                // the lock is alive.
                assert!(!is_async.load(Ordering::Relaxed));
                let rw = rw.take();
                rw.0 += 2;
            }),
    )
    .unwrap();

    // An asynchronous system locking the resource.
    ecs.add_system(SystemDesc::new().with_once(|| {
        schedule_future(async move {
            request!(Req, ResWrite = (Counter));
            let mut guard = request_lock::<Req>().await?;

            // We lock the resource for a little long. During the locking, the
            // sync task cannot get access to the resource.
            c_is_async.store(true, Ordering::Relaxed);
            thread::sleep(Duration::from_millis(100));
            let mut dec = || guard.res_write.0 -= 1;
            for _ in 0..COUNT {
                hint::black_box(dec());
            }
            c_is_async.store(false, Ordering::Relaxed);

            Ok(())
        });
    }))
    .unwrap();

    while !ecs.run().schedule_all().is_completed() {
        thread::yield_now();
    }

    // Sync task has increased the counter by 2 * COUNT.
    // While async task has decreased the counter by COUNT.
    assert_eq!(cnt.0, COUNT as i32);
}
