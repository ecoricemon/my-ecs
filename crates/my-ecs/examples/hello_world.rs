//! A tiny first program for `my-ecs`.
//!
//! This example introduces the core pieces in one small flow:
//!
//! - define component data with `#[derive(Component)]`
//! - define entity bundles with `#[derive(Entity)]`
//! - create entities through `EntWrite`
//! - read all positions with `Read`
//! - move only tagged entities with `Write`
//!
//! Expected output:
//!
//! ```text
//! Object: (1, 2)
//! MovableObject: (3, 4)
//! Object: (1, 2)
//! MovableObject: (13, 14)
//! ```

use my_ecs::prelude::*;

// A component is plain data that can be attached to an entity.
#[derive(Component)]
struct Position {
    x: u32,
    y: u32,
}

// Marker components can be empty. Here it marks entities that should move.
#[derive(Component)]
struct Movable;

// An entity is a bundle of components stored together in the ECS instance.
#[derive(Entity)]
struct Object {
    pos: Position,
}

// This entity has a Position and the Movable marker.
#[derive(Entity)]
struct MovableObject {
    pos: Position,
    _movable: Movable,
}

// Filters describe which components a system wants to read or write.
filter!(AllPositions, Target = Position);

// This filter selects Position only from entities that also have Movable.
filter!(MovablePositions, Target = Position, All = Movable);

fn main() {
    // Create an ECS instance with two worker threads in one worker group.
    Ecs::create(WorkerPool::with_len(2), [2])
        // Register each entity type before creating values of that type.
        .register_entity_of::<Object>()
        .register_entity_of::<MovableObject>()
        // Run these systems once, in order, when step() is called.
        .add_once_systems((
            create_objects,
            print_positions,
            move_objects,
            print_positions,
        ))
        .step();
}

// EntWrite gives this system permission to create or edit entity storage.
fn create_objects(ew: EntWrite<(Object, MovableObject)>) {
    let (mut objects, mut movable_objects) = ew.take_recur();

    objects.add(Object {
        pos: Position { x: 1, y: 2 },
    });

    movable_objects.add(MovableObject {
        pos: Position { x: 3, y: 4 },
        _movable: Movable,
    });
}

// Write gives this system mutable access to the selected Position components.
fn move_objects(mut positions: Write<MovablePositions>) {
    for Position { x, y } in positions.iter_mut().flatten() {
        *x += 10;
        *y += 10;
    }
}

// Read gives this system shared access to every Position component.
fn print_positions(positions: Read<AllPositions>) {
    for container in positions.iter() {
        let entity_name = container.entity_name().unwrap();

        for Position { x, y } in container.iter() {
            println!("{entity_name}: ({x}, {y})");
        }
    }
}
