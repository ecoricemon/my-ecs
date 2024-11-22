pub mod cache;
pub mod cmd;
pub mod ent;
pub mod entry;
pub mod lock;
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

    pub use super::cmd::{schedule_command, Command, CommandObject};
    pub use super::entry::{Ecs, EcsApp, EcsEntry, RawEcsApp, RunningEcs};
    pub use super::lock::request_lock;
    pub use super::resource::{Resource, ResourceDesc, ResourceKey};
    #[cfg(target_arch = "wasm32")]
    pub use super::web::{set_panic_hook_once, web_panic_hook};
    pub use super::worker::Work;
    pub use super::{EcsError, EcsResult};

    pub use crate::request;
    pub use my_ecs_macros::*;
}

use std::error::Error;
use thiserror::Error;

pub type EcsResult<T> = Result<T, Box<dyn Error + Send + Sync + 'static>>;

#[derive(Error, Debug)]
pub enum EcsError {
    #[error("unknown entity `{0}`")]
    UnknownEntity(String),
    #[error("unknown system")]
    UnknownSystem,
    #[error("unknown resourse `{0}`")]
    UnknownResource(String),
    #[error("invalid request `{0}`")]
    InvalidRequest(String),
    #[error("invalid entity `{0}`")]
    InvalidEntity(String),
}
