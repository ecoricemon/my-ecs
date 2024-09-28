#![allow(dead_code)]

use my_ecs::prelude::*;

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

fn try_schedule(num_workers: usize) {
    // Creates instance.
    let mut ecs = Ecs::default(WorkerPool::with_len(num_workers));

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

    return;

    // === Internal struct and functions ===

    async fn async_io() {}

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

fn main() {
    const TH_NUM: usize = 10;
    try_schedule(TH_NUM);

    use std::time::SystemTime;
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap();
    println!("Done at {now:?}");
}
