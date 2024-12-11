pub mod query;
pub mod request;
pub mod select;
pub mod storage;
pub mod system;

pub mod prelude {
    use super::*;

    pub use query::{
        EntQueryMut, EntWrite, Query, QueryMut, Read, ResQuery, ResQueryMut, ResRead, ResWrite,
        Write,
    };
    pub use request::{Request, Response};
    pub use select::Select;
    pub use storage::SystemDesc;
    pub use system::{FnSystem, InsertPos, NonZeroTick, System, SystemBond, SystemState, Tick};
}
