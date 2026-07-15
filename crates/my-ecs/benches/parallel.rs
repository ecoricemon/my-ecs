use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use my_ecs::prelude::*;

const ENTITY_COUNT: usize = 1_000_000;
const WORKER_COUNT: usize = 4;

#[derive(Component, Clone, Copy)]
struct Value(u64);

#[derive(Entity, Clone, Copy)]
struct Number {
    value: Value,
}

filter!(AllValues, Target = Value);

fn make_ecs(entity_count: usize, worker_count: usize) -> EcsApp<Worker> {
    let mut ecs = Ecs::create(WorkerPool::with_len(worker_count), [worker_count]);
    ecs.register_entity_of::<Number>()
        .add_once_system(move |entities: EntWrite<Number>| {
            let mut entities = entities.take_recur();
            entities.resize(entity_count, Number { value: Value(1) });
        })
        .step();
    ecs
}

fn sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel/sequential_iteration");

    group.throughput(Throughput::Elements(ENTITY_COUNT as u64));
    let mut ecs = make_ecs(ENTITY_COUNT, WORKER_COUNT);
    ecs.add_system(|values: Read<AllValues>| {
        let sum = values.iter().flatten().map(|value| value.0).sum::<u64>();
        black_box(sum);
    })
    .unwrap();

    group.bench_function(BenchmarkId::from_parameter(ENTITY_COUNT), move |b| {
        b.iter(|| {
            ecs.step();
        });
    });

    group.finish();
}

fn ecs_parallel(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel/ecs_parallel_iteration");

    group.throughput(Throughput::Elements(ENTITY_COUNT as u64));

    let mut ecs = make_ecs(ENTITY_COUNT, WORKER_COUNT);
    ecs.add_system(|values: Read<AllValues>| {
        let sum = values
            .iter()
            .map(|getter| {
                getter
                    .par_iter()
                    .into_ecs_par()
                    .map(|value| value.0)
                    .sum::<u64>()
            })
            .sum::<u64>();
        black_box(sum);
    })
    .unwrap();

    group.bench_function(
        BenchmarkId::new(format!("{WORKER_COUNT}_workers"), ENTITY_COUNT),
        move |b| {
            b.iter(|| {
                ecs.step();
            });
        },
    );

    group.finish();
}

criterion_group!(benches, sequential, ecs_parallel);
criterion_main!(benches);
