# my-ecs

[![Crates.io][crates-badge]][crates-url]
[![CI Status][ci-badge]][ci-url]
[![Codecov][codecov-badge]][codecov-url]

[crates-badge]: https://img.shields.io/crates/v/my-ecs.svg
[crates-url]: https://crates.io/crates/my-ecs
[ci-badge]: https://github.com/ecoricemon/my-ecs/actions/workflows/test.yml/badge.svg
[ci-url]: https://github.com/ecoricemon/my-ecs/actions/workflows/test.yml
[codecov-badge]: https://codecov.io/gh/ecoricemon/my-ecs/graph/badge.svg?flag=my-ecs
[codecov-url]: https://app.codecov.io/gh/ecoricemon/my-ecs?flags%5B0%5D=my-ecs

`my-ecs` is an Entity Component System library for Rust with parallel system
execution, built-in async task integration, and `wasm32` support.

## What It Provides

- Parallel scheduling by default.
  Systems can run across multiple worker threads while `my-ecs` enforces data
  access rules for components, entities, and resources.
- Explicit data access.
  Systems declare what they read or write, and the scheduler uses that
  information to order execution safely.
- Async integration.
  Systems can enqueue futures through the built-in posting/execution flow,
  which makes it practical to mix ECS logic with async work.
- Native and web targets.
  The crate supports native workers and includes web-worker support for
  `wasm32-unknown-unknown`.

## Core Concepts

- `Component`: plain data attached to entities.
- `Entity`: a collection of components.
- `System`: logic that reads or writes ECS data.
- `Resource`: unique global data stored once in the world.
- `Filter` / `Select`: type-level queries created with the `filter!` macro.

## Architecture

![my-ecs overview](https://raw.githubusercontent.com/ecoricemon/my-ecs/main/crates/my-ecs/docs/my-ecs-diagram.svg)

## Demo

<table align="center">
  <tr>
    <td>
      <video src="https://github.com/user-attachments/assets/c0e3ded3-5685-4d3b-b012-14192512e7a0" width="400" autoplay muted loop></video>
    </td>
    <td valign="top">
      <h3>my-ecs demo video</h3>
      <p>Rendering the Mandelbrot set with multiple threads using my-ecs</p>
      <p>Try the demo <a href="https://ecoricemon.duckdns.org">here</a></p>
    </td>
  </tr>
</table>

## Quick Start

Add the crate:

```toml
[dependencies]
my-ecs = "0.1"
```

Define components with ordinary Rust types:

```rust
use my_ecs::prelude::*;

#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}
```

Define an entity as a named bundle of components:

```rust
use my_ecs::prelude::*;

#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}

#[derive(Component)]
struct Movable;

#[derive(Entity)]
struct MovableObject {
    pos: Position,
    movable: Movable,
}
```

Define a selector with `filter!`, then read or write matching components from a
system:

```rust
use my_ecs::prelude::*;

#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}

filter!(Fpos, Target = Position);

fn moves(mut w: Write<Fpos>) {
    for Position { x, y } in w.iter_mut().flatten() {
        *x += 10;
        *y += 10;
    }
}
```

Resources are singletons:

```rust
use my_ecs::prelude::*;

#[derive(Resource)]
struct Count(u32);

Ecs::create(WorkerPool::new(), [])
    .add_resource(Count(0))
    .add_once_systems((
        |rw: ResWrite<Count>| rw.take().0 += 1,
        |rr: ResRead<Count>| println!("{}", rr.take().0),
    ))
    .step();
```

## Hello World Example

This example registers two entity types, creates data, mutates one subset, then
prints the result.

```rust
use my_ecs::prelude::*;

#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}

#[derive(Component)]
struct Movable;

#[derive(Entity)]
struct Object {
    pos: Position,
}

#[derive(Entity)]
struct MovableObject {
    pos: Position,
    _m: Movable,
}

filter!(Fpos, Target = Position);
filter!(Fmovpos, Target = Position, All = Movable);

fn main() {
    Ecs::create(WorkerPool::with_len(2), [2])
        .register_entity_of::<Object>()
        .register_entity_of::<MovableObject>()
        .add_once_systems((create, print, moves, print))
        .step();
}

fn create(ew: EntWrite<(Object, MovableObject)>) {
    let (mut obj_container, mut mov_container) = ew.take_recur();

    obj_container.add(Object {
        pos: Position { x: 1, y: 2 },
    });
    mov_container.add(MovableObject {
        pos: Position { x: 3, y: 4 },
        _m: Movable,
    });
}

fn moves(mut w: Write<Fmovpos>) {
    for Position { x, y } in w.iter_mut().flatten() {
        *x += 10;
        *y += 10;
    }
}

fn print(r: Read<Fpos>) {
    for container in r.iter() {
        for Position { x, y } in container.iter() {
            println!("{}: ({x}, {y})", container.entity_name().unwrap());
        }
    }
}
```

## Declaring Access

Parallel execution depends on explicit access declarations. Reads may run
together, while writes are exclusive.

```rust ignore
fn read_components(v: Read<A>) { /* ... */ }
fn write_components(v: Write<B>) { /* ... */ }
fn read_resource(v: ResRead<C>) { /* ... */ }
fn write_resource(v: ResWrite<D>) { /* ... */ }
fn write_entity(v: EntWrite<E>) { /* ... */ }
```

Because systems state their access up front, `my-ecs` can detect dependency
conflicts and schedule safe execution automatically.

## Examples In This Crate

- `examples/parallel.rs`: using `rayon` with ECS-aware parallel iteration.
- `examples/async.rs`: posting futures and applying their results back into the
  ECS world.
- `examples/async_io.rs`: separating async I/O work from compute-heavy work by
  worker group.
- `demo/`: a browser demo that renders the Mandelbrot set with `my-ecs`.

## Prelude

Most applications can start with:

```rust
use my_ecs::prelude::*;
```

The prelude re-exports the main ECS API, derive macros, helper macros, and
`rayon::prelude::*`.
