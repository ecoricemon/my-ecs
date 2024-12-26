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

#[test]
#[rustfmt::skip]
fn test_validate_request() {
    // Selectors and filters must be disjoint to each other in a request.
    // Such that invalid requests must be denied.
    // Disjoint conditions are as follows.
    // 1. X's Target is different from Y's Target.
    // 2. X's All intersects Y's None or vice versa.
    // 3. X's Any is a subset of Y's None or vice versa.

    #[derive(Component)] struct Ca;
    #[derive(Component)] struct Cb;
    #[derive(Component)] struct Cc;
    #[derive(Component)] struct Cd;
    #[derive(Component)] struct Ce;
    #[derive(Component)] struct Cf;
    #[derive(Component)] struct Cx;
    #[derive(Component)] struct Cy;

    let mut ecs = Ecs::default(WorkerPool::with_len(1), [1]);

    // 1. X's Target is different from Y's Target.
    filter!(A0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(A1, Target = Cy, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(A0, A1)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(A0, A1)>| {})).unwrap();

    // 2. X's All intersects Y's None or vice versa.
    filter!(B0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(B1, Target = Cx, None = Ca);
    filter!(B2, Target = Cx, None = Cb);
    filter!(B3, Target = Cx, None = (Ca, Cc));
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(B0, B1)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(B0, B2)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(B0, B3)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(B0, B1)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(B0, B2)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(B0, B3)>| {})).unwrap();

    // 3. X's Any is a subset of Y's None or vice versa.
    filter!(C0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(C1, Target = Cx, Any = Cc);
    filter!(C2, Target = Cx, Any = Cd);
    filter!(C3, Target = Cx, Any = (Cc, Cd));
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(C0, C1)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(C0, C2)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(C0, C3)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(C0, C1)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(C0, C2)>| {})).unwrap();
    ecs.add_system(SystemDesc::new().with_once(|_: Write<(C0, C3)>| {})).unwrap();

    // Wrong 1. X and Y are the same.
    // Expected behavior: Read is Ok, while Write is Error.
    filter!(D0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(D1, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(D2, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    // Read is Ok.
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(D0, D1)>| {})).unwrap();
    // Error in a single Write.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<(D0, D1)>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    // Error in Read, EntWrite or Write, EntWrite.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Read<D0>, _: EntWrite<D2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<D0>, _: EntWrite<D2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));

    // Wrong 2. X's All doesn't intersect Y's None or vice versa.
    filter!(E0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(E1, Target = Cx, None = (Cc, Cd));
    filter!(E2, None = (Cc, Cd));
    // Read is Ok.
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(E0, E1)>| {})).unwrap();
    // Error in a single Write.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<(E0, E1)>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    // Error in Read, EntWrite or Write, EntWrite.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Read<E0>, _: EntWrite<E2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<E0>, _: EntWrite<E2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));

    // Wrong 3. X's Any is not a subset of Y's None or vice versa.
    filter!(F0, Target = Cx, All = (Ca, Cb), None = (Cc, Cd), Any = (Ce, Cf));
    filter!(F1, Target = Cx, None = (Cc, Ce));
    filter!(F2, None = (Cc, Ce));
    // Read is Ok.
    ecs.add_system(SystemDesc::new().with_once(|_: Read<(F0, F1)>| {})).unwrap();
    // Error in a single Write.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<(F0, F1)>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    // Error in Read, EntWrite or Write, EntWrite.
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Read<F0>, _: EntWrite<F2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
    let res = ecs.add_system(SystemDesc::new().with_once(|_: Write<F0>, _: EntWrite<F2>| {})).take();
    assert!(matches!(res, Err(EcsError::InvalidRequest(..))));
}

#[test]
#[rustfmt::skip]
fn test_mixed_reg_unreg_entity_resource() {
    // Declares components, entities, resources, selectors, and filter.

    #[derive(Component, Debug, PartialEq)] struct Ca(i32);
    #[derive(Component, Debug, PartialEq)] struct Cb(i32);
    #[derive(Component, Debug, PartialEq)] struct Cc(i32);
    #[derive(Component, Debug, PartialEq)] struct Cd(i32);
    #[derive(Entity)] struct Ea { ca: Ca }
    #[derive(Entity)] struct Eb { cb: Cb }
    #[derive(Entity)] struct Eac { ca: Ca, cc: Cc }
    #[derive(Resource)] struct Ra(i32);
    #[derive(Resource)] struct Rb(i32);
    filter!(Sa, Target = Ca);
    filter!(Sb, Target = Cb);
    filter!(Fbd, All = (Cb, Cd));

    // Declares run counter and tracking variables.

    let c = Arc::new(Mutex::new([0; 5]));
    let (c0, c1, c2, c3, c4) = (
        Arc::clone(&c), Arc::clone(&c), Arc::clone(&c), Arc::clone(&c), Arc::clone(&c),
    );

    let (r_val, w_val) = (Arc::new(Mutex::new((0, 0))), Arc::new(Mutex::new((0, 0))));
    let (rr_val, rw_val) = (Arc::new(Mutex::new(0)), Arc::new(Mutex::new(0)));
    let (ew_val_ac, ew_val_bd) = (Arc::new(Mutex::new((0, 0))), Arc::new(Mutex::new((0, 0))));
    let (c_r_val, c_w_val) = (Arc::clone(&r_val), Arc::clone(&w_val));
    let (c_rr_val, c_rw_val) = (Arc::clone(&rr_val), Arc::clone(&rw_val));
    let (c_ew_val_ac, c_ew_val_bd) = (Arc::clone(&ew_val_ac), Arc::clone(&ew_val_bd));

    // Declares systems.

    let r_sys = move |r: Read<Sa>| {
        c0.lock().unwrap()[0] += 1;
        let sum = r.iter().flatten().map(|ca| ca.0).sum::<i32>();
        let num = r.iter().flatten().count() as i32;
        *c_r_val.lock().unwrap() = (sum, num)
    };
    let w_sys = move |w: Write<Sb>| {
        c1.lock().unwrap()[1] += 1;
        let sum = w.iter().flatten().map(|ca| ca.0).sum::<i32>();
        let num = w.iter().flatten().count() as i32;
        *c_w_val.lock().unwrap() = (sum, num)
    };
    let rr_sys = move |rr: ResRead<Ra>| {
        c2.lock().unwrap()[2] += 1;
        *c_rr_val.lock().unwrap() = rr.0;
    };
    let rw_sys = move |rw: ResWrite<Rb>| {
        c3.lock().unwrap()[3] += 1;
        *c_rw_val.lock().unwrap() = rw.0;
    };
    let ew_sys = move |mut ew: EntWrite<(Eac, Fbd)>| {
        c4.lock().unwrap()[4] += 1;
        if let Some(eac_cont) = ew.0.iter_mut().next() {
            let num = eac_cont.len();
            let sum = (0..num)
                .map(|vi| {
                    let e = eac_cont.get_by_value_index(vi);
                    e.ca.0 + e.cc.0
                })
                .sum::<i32>();
            *c_ew_val_ac.lock().unwrap() = (sum, num as i32);
        }

        let (sum, num) = ew.1.iter_mut().fold((0, 0), |mut acc, cont| {
            let (sum, num) = &mut acc;

            let colb = cont.get_column_of::<Cb>().unwrap();
            *sum += colb.iter().map(|cb| cb.0).sum::<i32>();

            let cold = cont.get_column_of::<Cd>().unwrap();
            *sum += cold.iter().map(|cd| cd.0).sum::<i32>();

            *num = colb.iter().count() as i32;
            assert_eq!(*num, cold.iter().count() as i32);

            acc
        });
        *c_ew_val_bd.lock().unwrap() = (sum, num);
    };

    // Adds systems.
    // Expected behavior:
    // - r_sys(Sa), w_sys(Sb), ew_sys(Eac, Fbd): Success
    // - rr_sys(Ra), rw_sys(Rb): Fail because of not registered resources.

    let mut ecs = Ecs::default(WorkerPool::with_len(1), [1]);

    ecs.add_system(SystemDesc::new().with_system(r_sys)).unwrap();
    ecs.add_system(SystemDesc::new().with_system(w_sys)).unwrap();
    ecs.add_system(SystemDesc::new().with_system(ew_sys)).unwrap();

    let rr_sys = match ecs.add_system(SystemDesc::new().with_system(rr_sys)).take()
    {
        Err(EcsError::UnknownResource(_, data)) => data.take_system(),
        _ => panic!()
    };
    let rw_sys = match ecs.add_system(SystemDesc::new().with_system(rw_sys)).take()
    {
        Err(EcsError::UnknownResource(_, data)) => data.take_system(),
        _ => panic!()
    };

    // Registers resources then adds failed systems again.
    // Expected behavior:
    // - rr_sys(Ra), rw_sys(Rb): Success

    let ra = Ra(10);
    ecs.register_resource(ResourceDesc::new().with_owned(ra)).unwrap();
    ecs.add_system(SystemDesc::new().with_system(rr_sys)).unwrap();
        
    let rb = Rb(20);
    ecs.register_resource(ResourceDesc::new().with_owned(rb)).unwrap();
    ecs.add_system(SystemDesc::new().with_system(rw_sys)).unwrap();

    // Runs ecs.
    // Expected behavior:
    // - All systems are executed

    reset_vals(&r_val, &w_val, &rr_val, &rw_val, &ew_val_ac, &ew_val_bd);
    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [1, 1, 1, 1, 1]);
    assert_eq!(*rr_val.lock().unwrap(), 10);
    assert_eq!(*rw_val.lock().unwrap(), 20);

    // Unregisters `Ra` and `Rb` then runs ecs.
    // Expected behavior:
    // - rr_sys(Ra), rw_sys(Rb): Inactivated

    ecs.unregister_resource::<Ra>().unwrap();

    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [2, 2, 1, 2, 2]);

    ecs.unregister_resource::<Rb>().unwrap();

    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [3, 3, 1, 2, 3]);

    // Registers and adds `Ea` and `Eb` then runs ecs.
    // Expected behavior:
    // - r_sys(Sa), w_sys(Sb): Put expected (sum, num).

    let ei_a = ecs.register_entity_of::<Ea>().unwrap();
    let eid_a = ecs.add_entity(ei_a, Ea { ca: Ca(1) }).unwrap();
    let ei_b = ecs.register_entity_of::<Eb>().unwrap();
    let eid_b = ecs.add_entity(ei_b, Eb { cb: Cb(2) }).unwrap();

    reset_vals(&r_val, &w_val, &rr_val, &rw_val, &ew_val_ac, &ew_val_bd);
    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [4, 4, 1, 2, 4]);
    assert_eq!(*r_val.lock().unwrap(), (1, 1)); // (sum, num) : [1]
    assert_eq!(*w_val.lock().unwrap(), (2, 1)); // (sum, num) : [2]
    assert_eq!(*ew_val_ac.lock().unwrap(), (0, 0)); // (sum, num) : []
    assert_eq!(*ew_val_bd.lock().unwrap(), (0, 0)); // (sum, num) : []

    // Attaches `Cc` and `Cd` to `Ea` and `Eb` respectively.
    // Now they are (Ca, Cc) and (Cb, Cd).
    // Expected behavior:
    // - ew_sys(Eac, Fbd): Put expected (sum, num).

    ecs.execute_command(|cmdr| cmdr.entity(eid_a).attach(Cc(3)).finish()).unwrap();
    ecs.execute_command(|cmdr| cmdr.entity(eid_b).attach(Cd(4)).finish()).unwrap();

    reset_vals(&r_val, &w_val, &rr_val, &rw_val, &ew_val_ac, &ew_val_bd);
    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [5, 5, 1, 2, 5]);
    assert_eq!(*r_val.lock().unwrap(), (1, 1)); // (sum, num) : [1]
    assert_eq!(*w_val.lock().unwrap(), (2, 1)); // (sum, num) : [2]
    assert_eq!(*ew_val_ac.lock().unwrap(), (4, 1)); // (sum, num) : [(1, 3)]
    assert_eq!(*ew_val_bd.lock().unwrap(), (6, 1)); // (sum, num) : [(2, 4)]

    // Unregisters `Ea` and `Eb`.
    // Expected behavior:
    // - No change

    reset_vals(&r_val, &w_val, &rr_val, &rw_val, &ew_val_ac, &ew_val_bd);
    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [6, 6, 1, 2, 6]);
    assert_eq!(*r_val.lock().unwrap(), (1, 1)); // (sum, num) : [1]
    assert_eq!(*w_val.lock().unwrap(), (2, 1)); // (sum, num) : [2]
    assert_eq!(*ew_val_ac.lock().unwrap(), (4, 1)); // (sum, num) : [(1, 3)]
    assert_eq!(*ew_val_bd.lock().unwrap(), (6, 1)); // (sum, num) : [(2, 4)]

    // Unregisters entity(Ca, Cc) and entity(Cb, Cd).
    // Expected behavior:
    // - r_sys(Sa), w_sys(Sb), ew_sys(Eac, Fbd): Empty iteration.

    ecs.unregister_entity::<(Ca, Cc)>().unwrap();
    ecs.unregister_entity::<(Cb, Cd)>().unwrap();

    reset_vals(&r_val, &w_val, &rr_val, &rw_val, &ew_val_ac, &ew_val_bd);
    ecs.run().schedule_all();
    assert_eq!(*c.lock().unwrap(), [7, 7, 1, 2, 7]);
    assert_eq!(*r_val.lock().unwrap(), (0, 0)); // (sum, num) : []
    assert_eq!(*w_val.lock().unwrap(), (0, 0)); // (sum, num) : []
    assert_eq!(*ew_val_ac.lock().unwrap(), (0, 0)); // (sum, num) : []
    assert_eq!(*ew_val_bd.lock().unwrap(), (0, 0)); // (sum, num) : []

    fn reset_vals(
        r_val: &Arc<Mutex<(i32, i32)>>,
        w_val: &Arc<Mutex<(i32, i32)>>,
        rr_val: &Arc<Mutex<i32>>,
        rw_val: &Arc<Mutex<i32>>,
        ew_val_ac: &Arc<Mutex<(i32, i32)>>,
        ew_val_bd: &Arc<Mutex<(i32, i32)>>,
    ) {
        *r_val.lock().unwrap() = (0, 0);
        *w_val.lock().unwrap() = (0, 0);
        *rr_val.lock().unwrap() = 0;
        *rw_val.lock().unwrap() = 0;
        *ew_val_ac.lock().unwrap() = (0, 0);
        *ew_val_bd.lock().unwrap() = (0, 0);
    }
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
                Ok(())
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
    let pool = WorkerPool::with_len(3);
    let workers = test_request_lock_ok(pool.into());
    test_request_lock_cancelled(workers);
}

fn test_request_lock_ok(workers: Vec<Worker>) -> Vec<Worker> {
    const COUNT: u64 = 1000;

    // Creates instance.
    let num_workers = workers.len();
    let mut ecs = Ecs::default(workers, [num_workers]);

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
            .with_system(move |mut rw: ResWrite<Counter>| {
                // Because of locking, even sync tasks cannot get executed while
                // the lock is alive.
                assert!(!is_async.load(Ordering::Relaxed));
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

    ecs.destroy()
}

fn test_request_lock_cancelled(workers: Vec<Worker>) -> Vec<Worker> {
    // Creates instance.
    let num_workers = workers.len();
    let mut ecs = Ecs::default(workers, [num_workers]);

    // Registers a shared resource.
    #[derive(Resource)]
    struct Counter(i32);
    let mut cnt = Counter(0);
    let desc = unsafe { ResourceDesc::new().with_ptr(&mut cnt as *mut _) };
    ecs.register_resource(desc).unwrap();

    // A synchronous system writing something on the resource.
    ecs.add_system(
        SystemDesc::new().with_system(move |mut rw: ResWrite<Counter>| {
            rw.0 += 1;
        }),
    )
    .unwrap();

    // An asynchronous system locking the resource.
    ecs.add_system(SystemDesc::new().with_once(|| {
        schedule_future(async move {
            request!(Req, ResWrite = (Counter));
            let mut guard = request_lock::<Req>().await?;
            guard.res_write.0 += 1;
            Ok(())
        });
    }))
    .unwrap();

    ecs.run().schedule_all();

    // `request_lock` command or system will be cancelled by destruction of ecs.
    let workers = ecs.destroy();

    // Sync system increased it by 1, while future couldn't have a chance to
    // modity the counter.
    assert_eq!(cnt.0, 1);

    workers
}
