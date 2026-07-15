use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use my_ecs::prelude::*;

const ENTITY_COUNT: usize = 10_000;

#[derive(Component, Clone, Copy)]
#[allow(dead_code)]
struct Position(f64);

#[derive(Component, Clone, Copy)]
#[allow(dead_code)]
struct Velocity(f64);

#[derive(Entity, Clone, Copy)]
struct Resting {
    position: Position,
}

fn spawn(c: &mut Criterion) {
    let mut group = c.benchmark_group("entity/spawn");

    group.throughput(Throughput::Elements(ENTITY_COUNT as u64));
    group.bench_with_input(
        BenchmarkId::from_parameter(ENTITY_COUNT),
        &ENTITY_COUNT,
        |b, &entity_count| {
            b.iter_batched(
                || {
                    let mut ecs = Ecs::create(WorkerPool::with_len(1), [1]);
                    let entity_index = ecs.register_entity_of::<Resting>().unwrap();
                    (ecs, entity_index)
                },
                |(mut ecs, entity_index)| {
                    for value in 0..entity_count {
                        black_box(
                            ecs.add_entity(
                                entity_index,
                                Resting {
                                    position: Position(value as f64),
                                },
                            )
                            .unwrap(),
                        );
                    }
                    ecs
                },
                BatchSize::SmallInput,
            );
        },
    );

    group.finish();
}

fn remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("entity/remove");

    group.throughput(Throughput::Elements(ENTITY_COUNT as u64));
    group.bench_with_input(
        BenchmarkId::from_parameter(ENTITY_COUNT),
        &ENTITY_COUNT,
        |b, &entity_count| {
            b.iter_batched(
                || {
                    let mut ecs = Ecs::create(WorkerPool::with_len(1), [1]);
                    let entity_index = ecs.register_entity_of::<Resting>().unwrap();
                    let entity_ids = (0..entity_count)
                        .map(|value| {
                            ecs.add_entity(
                                entity_index,
                                Resting {
                                    position: Position(value as f64),
                                },
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>();
                    (ecs, entity_ids)
                },
                |(mut ecs, entity_ids)| {
                    for entity_id in entity_ids {
                        ecs.remove_entity(entity_id).unwrap();
                    }
                    ecs
                },
                BatchSize::SmallInput,
            );
        },
    );

    group.finish();
}

fn attach(c: &mut Criterion) {
    let mut group = c.benchmark_group("entity/attach_component");

    group.throughput(Throughput::Elements(ENTITY_COUNT as u64));
    group.bench_with_input(
        BenchmarkId::from_parameter(ENTITY_COUNT),
        &ENTITY_COUNT,
        |b, &entity_count| {
            b.iter_batched(
                || {
                    let mut ecs = Ecs::create(WorkerPool::with_len(1), [1]);
                    let entity_index = ecs.register_entity_of::<Resting>().unwrap();
                    let entity_ids = (0..entity_count)
                        .map(|value| {
                            ecs.add_entity(
                                entity_index,
                                Resting {
                                    position: Position(value as f64),
                                },
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>();
                    (ecs, entity_ids)
                },
                |(mut ecs, entity_ids)| {
                    for entity_id in entity_ids {
                        ecs.execute_command(move |commander| {
                            commander
                                .change_entity(entity_id)
                                .attach(Velocity(1.0))
                                .finish()
                        })
                        .unwrap();
                    }
                    ecs
                },
                BatchSize::SmallInput,
            );
        },
    );

    group.finish();
}

criterion_group!(benches, spawn, remove, attach);
criterion_main!(benches);
