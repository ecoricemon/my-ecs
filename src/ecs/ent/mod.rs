pub mod component;
pub mod entity;
mod sparse_set;
pub mod storage;

pub mod prelude {
    use super::*;

    pub use component::Component;
    pub use entity::{Entity, EntityIndex, EntityKey, EntityKeyKind, EntityName, EntityTypeId};
    pub use storage::{AsEntityDesc, EntityContainer, EntityDesc};
}
