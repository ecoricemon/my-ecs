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

use std::{error::Error, fmt};
use thiserror::Error;

pub type EcsResult<T> = Result<T, Box<dyn Error + Send + Sync + 'static>>;

#[derive(Error)]
#[repr(C)]
pub enum EcsError<Data = ()> {
    #[error("unknown system `{0}`")]
    UnknownSystem(String, Data),

    #[error("unknown entity `{0}`")]
    UnknownEntity(String, Data),
    #[error("invalid entity `{0}`")]
    InvalidEntity(String, Data),

    #[error("unknown resourse `{0}`")]
    UnknownResource(String, Data),
    #[error("duplicated resource `{0}`")]
    DupResource(String, Data),

    #[error("invalid request `{0}`")]
    InvalidRequest(String, Data),

    #[error("unknown error `{0}`")]
    Unknown(String, Data),
}

impl<Data> fmt::Debug for EcsError<Data> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownSystem(reason, ..) => {
                write!(f, "EcsError::UnknownSystem({reason}, ..)")
            }
            Self::UnknownEntity(reason, ..) => {
                write!(f, "EcsError::UnknownEntity({reason}, ..)")
            }
            Self::InvalidEntity(reason, ..) => {
                write!(f, "EcsError::InvalidEntity({reason}, ..)")
            }
            Self::UnknownResource(reason, ..) => {
                write!(f, "EcsError::UnknownResource({reason}, ..)")
            }
            Self::DupResource(reason, ..) => {
                write!(f, "EcsError::DupResource({reason}, ..)")
            }
            Self::InvalidRequest(reason, ..) => {
                write!(f, "EcsError::InvalidRequest({reason}, ..)")
            }
            Self::Unknown(reason, ..) => {
                write!(f, "EcsError::Unknown({reason}, ..)")
            }
        }
    }
}

impl<Data> EcsError<Data> {
    pub fn reason(&self) -> &str {
        match self {
            Self::UnknownSystem(reason, ..) => reason,
            Self::UnknownEntity(reason, ..) => reason,
            Self::InvalidEntity(reason, ..) => reason,
            Self::UnknownResource(reason, ..) => reason,
            Self::DupResource(reason, ..) => reason,
            Self::InvalidRequest(reason, ..) => reason,
            Self::Unknown(reason, ..) => reason,
        }
    }

    pub fn take_data(self) -> Data {
        match self {
            Self::UnknownSystem(_, data) => data,
            Self::UnknownEntity(_, data) => data,
            Self::InvalidEntity(_, data) => data,
            Self::UnknownResource(_, data) => data,
            Self::DupResource(_, data) => data,
            Self::InvalidRequest(_, data) => data,
            Self::Unknown(_, data) => data,
        }
    }

    pub fn without_data(self) -> EcsError<()> {
        self.with_data(())
    }

    pub fn with_data<To>(self, data: To) -> EcsError<To> {
        self.map_data(|_| data)
    }

    pub fn map_data<F, To>(self, f: F) -> EcsError<To>
    where
        F: FnOnce(Data) -> To,
    {
        match self {
            Self::UnknownSystem(reason, old) => EcsError::UnknownSystem(reason, f(old)),
            Self::UnknownEntity(reason, old) => EcsError::UnknownEntity(reason, f(old)),
            Self::InvalidEntity(reason, old) => EcsError::InvalidEntity(reason, f(old)),
            Self::UnknownResource(reason, old) => EcsError::UnknownResource(reason, f(old)),
            Self::DupResource(reason, old) => EcsError::DupResource(reason, f(old)),
            Self::InvalidRequest(reason, old) => EcsError::InvalidRequest(reason, f(old)),
            Self::Unknown(reason, old) => EcsError::Unknown(reason, f(old)),
        }
    }
}
