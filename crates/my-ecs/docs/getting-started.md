# Getting Started With `my-ecs`

This guide explains the small amount of Rust and ECS vocabulary you need to run
the first example and make simple changes to it.

Start with the runnable example:

```bash
cargo run -p my-ecs --example hello_world
```

Expected output:

```text
Object: (1, 2)
MovableObject: (3, 4)
Object: (1, 2)
MovableObject: (13, 14)
```

## The Rust Pieces

`use my_ecs::prelude::*;` imports the common `my-ecs` types and macros. Most
small programs can start with this line.

`struct Position { x: u32, y: u32 }` defines a custom data type. In this
example, `Position` stores two positive whole numbers.

`#[derive(Component)]` asks Rust to generate the code that lets `my-ecs` store
the type as component data.

`#[derive(Entity)]` asks Rust to generate the code that lets `my-ecs` store a
bundle of components as an entity type.

`fn move_objects(...) { ... }` defines a function.

## The ECS Pieces

A component is data attached to an entity.

```rust
#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}
```

An entity can be combined or defined in advance.

```rust
#[derive(Entity)]
struct MovableObject {
    pos: Position,
    _movable: Movable,
}
```

A marker component is an empty component used as a tag.

```rust
#[derive(Component)]
struct Movable;
```

A filter names which entity types should be included in a query. The `filter!`
macro creates a zero-sized marker type and implements the ECS traits for it.
You usually do not write those trait implementations by hand.

```rust
filter!(AllPositions, Target = Position);
filter!(MovablePositions, Target = Position, All = Movable);
```

The first line expands conceptually to something like this:

```rust
struct AllPositions;

impl Filter for AllPositions {
    type All = ();
    type Any = ();
    type None = ();
    type Exact = ();
}

impl Select for AllPositions {
    type Target = Position;
    type Filter = AllPositions;
}
```

The exact generated code is handled by the macro, but the idea is:

- `Filter` says which entities match.
- `Select` says which component type should be read or written from matching
  entities.

When you use `Target = Position`, `filter!` implements both `Filter` and
`Select`, so the type can be used with `Read<...>` and `Write<...>`. Without
`Target`, it implements only `Filter`, which is useful for entity queries such
as `EntWrite<...>`.

`AllPositions` selects every `Position`. `MovablePositions` selects only
`Position` components that belong to entities that also have `Movable`.

You can use `filter!` with these matching rules:

```rust
filter!(WithPosition, All = Position);
filter!(WithPositionOrVelocity, Any = (Position, Velocity));
filter!(WithoutSleeping, None = Sleeping);
filter!(OnlyPositionAndMovable, Exact = (Position, Movable));
```

`All` means the entity must contain every listed component. It is an AND rule.

`Any` means the entity must contain at least one listed component. It is an OR
rule.

`None` means the entity must not contain any listed component.

`Exact` means the entity must contain exactly the listed component set. Use it
when extra components should make the entity not match.

`All`, `Any`, and `None` can be combined:

```rust
filter!(
    MovingVisibleObjects,
    Target = Position,
    All = Visible,
    Any = (Player, Enemy),
    None = Sleeping,
);
```

Read this as: select `Position` from entities that have `Visible`, have either
`Player` or `Enemy`, and do not have `Sleeping`.

`Exact` cannot be combined with `All`, `Any`, or `None`, because it already
describes the full component set:

```rust
filter!(OnlyPositionAndMovable, Target = Position, Exact = (Position, Movable));
```

Use a tuple when listing more than one component, such as `(Player, Enemy)`.
For one component, write just the component type, such as `All = Visible`.

## Access Types

Systems declare their access through their function parameters.

```rust
fn print_positions(positions: Read<AllPositions>) { /* ... */ }
```

`Read<AllPositions>` means the system can read matching `Position` values.
Multiple read-only systems can run at the same time.

```rust
fn move_objects(mut positions: Write<MovablePositions>) { /* ... */ }
```

`Write<MovablePositions>` means the system can change matching `Position`
values. Writes are exclusive, so `my-ecs` can schedule systems safely.

```rust
fn create_objects(ew: EntWrite<(Object, MovableObject)>) { /* ... */ }
```

`EntWrite<(Object, MovableObject)>` means the system can create or edit storage
for those entity types.

Resources are singleton values stored once in the ECS instance.

```rust
#[derive(Resource)]
struct Count(u32);

fn print_count(count: ResRead<Count>) {
    println!("{}", count.take().0);
}
```

Use `ResRead<T>` to read a resource and `ResWrite<T>` to mutate it.

## Running Systems

This creates an ECS instance, registers entity types, adds systems, and runs one
step:

```rust
Ecs::create(WorkerPool::with_len(2), [2])
    .register_entity_of::<Object>()
    .register_entity_of::<MovableObject>()
    .add_once_systems((
        create_objects,
        print_positions,
        move_objects,
        print_positions,
    ))
    .step();
```

Read this as:

- create an ECS instance with two worker threads
- register the entity types you want to store
- add systems that should run once
- call `step()` to execute them

## Try Changing It

Small changes are the fastest way to learn the example:

- Change `Position { x: 3, y: 4 }` to different numbers.
- Change `*x += 10` and `*y += 10` to move by a different amount.
- Add a second `MovableObject` in `create_objects`.
- Remove `_movable: Movable` from `MovableObject` and see how the compiler helps
  you fix the entity definition.

When something does not compile, start from the type named in the error message.
Most `my-ecs` beginner errors come from a component, entity, filter, or system
access type not matching the others yet.
