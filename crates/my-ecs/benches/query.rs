#[cfg(not(target_arch = "wasm32"))]
mod native {
    use criterion::{
        black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
    };
    use my_ecs::prelude::*;

    const DENSE_ENTITY_COUNT: usize = 1_000_000;

    #[derive(Component, Clone, Copy)]
    struct Position(f64);

    #[derive(Component, Clone, Copy)]
    struct Velocity;

    #[derive(Entity, Clone, Copy)]
    struct Dense {
        position: Position,
        velocity: Velocity,
    }

    filter!(AllPositions, Target = Position);
    filter!(MovingPositions, Target = Position, All = Velocity);

    fn dense_read(c: &mut Criterion) {
        let mut group = c.benchmark_group("query/dense_read");

        group.throughput(Throughput::Elements(DENSE_ENTITY_COUNT as u64));

        let mut ecs = Ecs::create(WorkerPool::with_len(1), [1]);
        ecs.register_entity_of::<Dense>()
            .add_once_system(|entities: EntWrite<Dense>| {
                entities.take_recur().resize(
                    DENSE_ENTITY_COUNT,
                    Dense {
                        position: Position(1.0),
                        velocity: Velocity,
                    },
                );
            })
            .step()
            .add_system(|positions: Read<AllPositions>| {
                let sum = positions
                    .iter()
                    .flatten()
                    .map(|position| position.0)
                    .sum::<f64>();
                black_box(sum);
            })
            .unwrap();

        group.bench_function(BenchmarkId::from_parameter(DENSE_ENTITY_COUNT), move |b| {
            b.iter(|| {
                ecs.step();
            });
        });

        group.finish();
    }

    fn dense_write(c: &mut Criterion) {
        let mut group = c.benchmark_group("query/dense_write");

        group.throughput(Throughput::Elements(DENSE_ENTITY_COUNT as u64));

        let mut ecs = Ecs::create(WorkerPool::with_len(1), [1]);
        ecs.register_entity_of::<Dense>()
            .add_once_system(|entities: EntWrite<Dense>| {
                entities.take_recur().resize(
                    DENSE_ENTITY_COUNT,
                    Dense {
                        position: Position(0.0),
                        velocity: Velocity,
                    },
                );
            })
            .step()
            .add_system(|mut positions: Write<AllPositions>| {
                for position in positions.iter_mut().flatten() {
                    position.0 += 1.0;
                }
            })
            .unwrap();

        group.bench_function(BenchmarkId::from_parameter(DENSE_ENTITY_COUNT), move |b| {
            b.iter(|| {
                ecs.step();
            });
        });

        group.finish();
    }

    criterion_group!(benches, dense_read, dense_write);
    criterion_main!(benches);

    pub fn run() {
        main();
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    native::run();
}

#[cfg(target_arch = "wasm32")]
fn main() {}
