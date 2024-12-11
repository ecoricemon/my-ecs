pub mod component;
pub mod entity;
pub mod storage;

pub mod prelude {
    use super::*;

    pub use component::{Component, ComponentKey};
    pub use entity::{
        AddEntity, BorrowComponent, ContainEntity, Entity, EntityId, EntityIndex, EntityKey,
        EntityKeyKind, EntityKeyRef, EntityName, EntityTypeId, RegisterComponent,
    };
    pub use storage::{AsEntityReg, EntityContainer, EntityReg};
}
