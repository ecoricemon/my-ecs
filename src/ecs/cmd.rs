use super::{entry::Ecs, sched::ctrl::SUB_CONTEXT};
use crate::{ds::prelude::*, impl_from_for_enum};
use std::{fmt, ptr::NonNull};

pub trait Command: Send + 'static {
    #[allow(unused_variables)]
    fn command(self, ecs: Ecs<'_>)
    where
        Self: Sized,
    {
    }

    #[allow(unused_variables)]
    fn command_by_boxed(self: Box<Self>, ecs: Ecs<'_>) {}

    /// Guaranteed to be called only once.
    #[allow(unused_variables)]
    fn command_by_mut(&mut self, ecs: Ecs<'_>) {}

    /// Command can be cancelled out when it's not executed before it's dropped.
    fn cancel(&mut self) {}
}

impl fmt::Debug for dyn Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "dyn Command")
    }
}

impl<F> Command for F
where
    F: FnOnce(Ecs) + Send + 'static,
{
    fn command(self, ecs: Ecs<'_>) {
        (self)(ecs)
    }

    fn command_by_boxed(self: Box<Self>, ecs: Ecs<'_>) {
        (self)(ecs)
    }

    fn command_by_mut(&mut self, _ecs: Ecs<'_>) {
        panic!("FnOnce command cannot be called by reference")
    }
}

/// Empty command.
impl Command for () {}

#[derive(Debug)]
pub enum CommandObject {
    /// Trait object.
    Boxed(Box<dyn Command>),

    /// Ready future containing command.
    Future(ReadyFuture),

    Raw(RawCommand),
}

impl_from_for_enum!(CommandObject, Boxed, Box<dyn Command>);
impl_from_for_enum!(CommandObject, Future, ReadyFuture);
impl_from_for_enum!(CommandObject, Raw, RawCommand);

impl CommandObject {
    pub(crate) fn command(self, ecs: Ecs<'_>) {
        match self {
            Self::Boxed(boxed) => boxed.command_by_boxed(ecs),
            Self::Future(future) => {
                // We registered `Command::command` as the consuming function
                // on the future. See `schedule_future`.
                //
                // Safety: Type `Arg` is correct.
                unsafe { future.consume(ecs) }
            }
            Self::Raw(raw) => raw.command(ecs),
        }
    }

    pub(crate) fn cancel(self) {
        match self {
            Self::Boxed(mut boxed) => boxed.cancel(),
            Self::Future(_future) => {}
            Self::Raw(raw) => raw.cancel(),
        }
    }
}

/// Like other commands, RawCommand is also executed only once.
#[derive(Debug)]
pub struct RawCommand {
    data: NonNull<u8>,
    command_by_mut: unsafe fn(NonNull<u8>, Ecs<'_>),
    cancel: unsafe fn(NonNull<u8>),
}

impl RawCommand {
    /// * cancel - Function that is called when this command is not executed.
    pub(crate) unsafe fn new<C: Command>(cmd: &C) -> Self {
        let data = NonNull::new_unchecked((cmd as *const _ as *const u8).cast_mut());

        unsafe fn command_by_mut<C: Command>(data: NonNull<u8>, ecs: Ecs<'_>) {
            let data = data.cast::<C>().as_mut();
            data.command_by_mut(ecs);
        }

        unsafe fn cancel<C: Command>(data: NonNull<u8>) {
            let data = data.cast::<C>().as_mut();
            data.cancel();
        }

        Self {
            data,
            command_by_mut: command_by_mut::<C>,
            cancel: cancel::<C>,
        }
    }

    fn command(self, ecs: Ecs<'_>) {
        // Safety: Calling `self.command_by_mut` is safe because it's guaranteed
        // by owner called new().
        unsafe { (self.command_by_mut)(self.data, ecs) };
    }

    fn cancel(self) {
        // Safety: Calling `self.cancel` is safe because it's guaranteed by
        // owner called new().
        unsafe { (self.cancel)(self.data) };
    }
}

unsafe impl Send for RawCommand {}

// This function must be called on sub worker context.
pub fn schedule_command(cmd: CommandObject) {
    let ptr = SUB_CONTEXT.get();
    assert!(!ptr.is_dangling());

    // Safety: Current worker has valid sub context pointer.
    let comm = unsafe { ptr.as_ref().comm() };
    comm.send_command(cmd);
}
