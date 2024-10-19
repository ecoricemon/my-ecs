pub mod cache;
pub mod cmd;
pub mod ent;
pub mod manager;
pub mod resource;
pub mod sched;
pub mod sys;
pub mod wait;
pub mod web;
pub mod worker;

pub mod prelude {
    pub use super::ent::prelude::*;
    pub use super::sched::prelude::*;
    pub use super::sys::prelude::*;

    pub use super::cmd::{schedule_command, Command};
    pub use super::manager::{Ecs, EcsApp, EcsEntry, RunningEcs};
    pub use super::resource::{MaybeOwned, Resource, ResourceKey, ResourceKind};
    #[cfg(target_arch = "wasm32")]
    pub use super::web::{set_panic_hook_once, web_panic_hook};
    pub use super::worker::{HoldWorkers, Work};
    pub use super::{EcsError, EcsResult};

    pub use crate::request;
    pub use my_ecs_macros::*;
}

pub type EcsResult<T> = Result<T, EcsError>;

use thiserror::Error;

#[derive(Error, Debug)]
pub enum EcsError {
    #[error("unknown entity `{0}`")]
    UnknownEntity(String),
    #[error("unknown system")]
    UnknownSystem,
    #[error("unknown resourve `{0}`")]
    UnknownResource(String),
    #[error("invalid request `{0}`")]
    InvalidRequest(String),
}
