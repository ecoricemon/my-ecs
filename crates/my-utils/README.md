# my-utils

[![Crates.io][crates-badge]][crates-url]
[![CI Status][ci-badge]][ci-url]
[![Codecov][codecov-badge]][codecov-url]

[crates-badge]: https://img.shields.io/crates/v/my-utils.svg
[crates-url]: https://crates.io/crates/my-utils
[ci-badge]: https://github.com/ecoricemon/my-ecs/actions/workflows/test.yml/badge.svg
[ci-url]: https://github.com/ecoricemon/my-ecs/actions/workflows/test.yml
[codecov-badge]: https://codecov.io/gh/ecoricemon/my-ecs/graph/badge.svg?flag=my-utils
[codecov-url]: https://app.codecov.io/gh/ecoricemon/my-ecs?flags%5B0%5D=my-utils

A utility library providing general-purpose data structures and helpers.

## Data Structures

### `AnyVec`

A type-erased vector that holds values of a single concrete type behind a raw
pointer. This is useful when you need to store vectors of heterogeneous types
in a single variable — for example, in a `Vec<AnyVec>` where each entry holds a
different component type.

Because the concrete type is erased, most operations are `unsafe` and work
through raw pointers. Use the `tinfo!` macro to create a `TypeInfo` value,
which supplies the vector with the type's size, alignment, drop glue, and
optional clone function.

```rust
use my_utils::{tinfo, ds::AnyVec};

let mut v = AnyVec::new(tinfo!(i32));

// Safety: type i32 is correct.
unsafe {
    v.push(1_i32);
    v.push(2_i32);
}

// Iterate with the concrete type.
for x in v.iter_of::<i32>() {
    println!("{x}");
}

// Or borrow the vector as a typed Vec.
{
    let mut tv = v.as_vec_mut::<i32>();
    tv.push(3);
} // Changes are written back to `v` on drop.

// Safety: type i32 is correct.
unsafe {
    assert_eq!(v.pop::<i32>(), Some(3));
}
```

`AnyVec` also supports parallel iteration via [rayon](https://docs.rs/rayon):

```rust
use my_utils::{tinfo, ds::AnyVec};
use rayon::prelude::*;

let mut v = AnyVec::new(tinfo!(i32));
unsafe { v.push(1_i32); v.push(2_i32); v.push(3_i32); }

let sum: i32 = v.par_iter_of::<i32>().sum();
assert_eq!(sum, 6);
```

### `ChunkAnyVec`

A type-erased vector backed by fixed-size chunks rather than a single
contiguous allocation. When the vector grows beyond its current capacity a new
chunk is appended instead of reallocating the entire buffer, making it a better
choice than `AnyVec` when frequent insertion and removal are expected.

The chunk capacity must be a power of two.

```rust
use my_utils::{tinfo, ds::ChunkAnyVec};

let mut v = ChunkAnyVec::new(tinfo!(i32), 4 /* chunk capacity */);

unsafe {
    for i in 0..10_i32 {
        v.push(i);
    }
}

for x in v.iter_of::<i32>() {
    print!("{x} ");
}
```

### `OptVec`

A vector of optional values where slots can be vacant. Removing an item leaves
a vacant slot behind rather than shifting subsequent items, so every occupied
item keeps a stable index for its lifetime. New items are placed into the first
available vacant slot, or appended to the end if none exists.

```rust
use my_utils::ds::OptVec;

let mut v: OptVec<&str> = OptVec::new();

let a = v.add("hello");   // → index 0
let b = v.add("world");   // → index 1

v.take(a);                // slot 0 becomes vacant

let c = v.add("!");       // reuses index 0
assert_eq!(c, 0);

// Iterate occupied values with their indices.
for (index, value) in v.pairs() {
    println!("[{index}] {value}");
}
```

## Type Information: `TypeInfo` and `tinfo!`

`TypeInfo` bundles runtime type metadata — `TypeId`, name, size, alignment, and
type-erased function pointers for drop, clone, and default — into a small
`Copy` struct. It is the foundation that `AnyVec` and `ChunkAnyVec` rely on to
manage values without knowing their concrete type at compile time.

The `tinfo!` macro constructs a `TypeInfo` at compile time and automatically
detects whether the type implements `Send`, `Sync`, `Clone`, and `Default`:

```rust
use my_utils::tinfo;

let info = tinfo!(String);

assert_eq!(info.size, std::mem::size_of::<String>());
assert!(info.is_send);
assert!(info.is_clone);
```
