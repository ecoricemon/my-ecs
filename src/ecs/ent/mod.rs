pub mod component;
pub mod entity;
pub mod sparse_set;
pub mod storage;

pub mod prelude {
    use super::*;

    pub use component::Component;
    pub use entity::{
        AddEntity, BorrowComponent, ContainEntity, Entity, EntityIndex, EntityKey, EntityKeyKind,
        EntityName, EntityTypeId, RegisterComponent,
    };
    pub use sparse_set::SparseSet;
    pub use storage::{AsEntityReg, EntityContainer, EntityReg};
}
