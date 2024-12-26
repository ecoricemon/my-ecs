use super::{
    ent::{component::Component, entity::EntityId},
    entry::Ecs,
    sched::ctrl::SUB_CONTEXT,
    share::{self, EntMoveStorage, Shared},
    EcsResult,
};
use crate::{ds::prelude::*, impl_from_for_enum};
use std::{fmt, ptr::NonNull, sync::MutexGuard};

pub trait Command: Send + 'static {
    #[allow(unused_variables)]
    fn command(self, ecs: Ecs<'_>) -> EcsResult<()>
    where
        Self: Sized,
    {
        Ok(())
    }

    #[allow(unused_variables)]
    fn command_by_boxed(self: Box<Self>, ecs: Ecs<'_>) -> EcsResult<()> {
        Ok(())
    }

    /// Guaranteed to be called only once.
    #[allow(unused_variables)]
    fn command_by_mut(&mut self, ecs: Ecs<'_>) -> EcsResult<()> {
        Ok(())
    }

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
    F: FnOnce(Ecs) -> EcsResult<()> + Send + 'static,
{
    fn command(self, ecs: Ecs<'_>) -> EcsResult<()> {
        (self)(ecs)
    }

    fn command_by_boxed(self: Box<Self>, ecs: Ecs<'_>) -> EcsResult<()> {
        (self)(ecs)
    }

    fn command_by_mut(&mut self, _ecs: Ecs<'_>) -> EcsResult<()> {
        panic!("FnOnce command cannot be called by reference")
    }
}

/// Empty command.
impl Command for () {}

pub struct Commander<'s> {
    shared: &'s Shared,
}

impl<'s> Commander<'s> {
    pub(crate) const fn new(shared: &'s Shared) -> Self {
        Self { shared }
    }

    pub fn entity(&self, eid: EntityId) -> EntityMoveCommandBuilder<'_, true> {
        let guard = self.shared.lock_entity_move_storage();
        EntityMoveCommandBuilder::with_guard(eid, guard)
    }
}

#[derive(Debug)]
pub enum CommandObject {
    /// Trait object.
    Boxed(Box<dyn Command>),

    /// Ready future containing command.
    Future(ReadyFuture),

    Raw(RawCommand),
}

impl_from_for_enum!("outer" = CommandObject; "var" = Boxed; "inner" = Box<dyn Command>);
impl_from_for_enum!("outer" = CommandObject; "var" = Future; "inner" = ReadyFuture);
impl_from_for_enum!("outer" = CommandObject; "var" = Raw; "inner" = RawCommand);

impl CommandObject {
    pub(crate) fn command(self, ecs: Ecs<'_>) -> EcsResult<()> {
        match self {
            Self::Boxed(boxed) => boxed.command_by_boxed(ecs),
            Self::Future(future) => {
                // Safety: consume() requires correct `Arg` and `CR` types.
                // - `Arg` type is `Ecs<'_>`.
                // - `CR` type is `EcsResult<()>`.
                // We matched the types with `consume_ready_future`.
                unsafe { future.consume::<Ecs<'_>, EcsResult<()>>(ecs) }
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
    command_by_mut: unsafe fn(NonNull<u8>, Ecs<'_>) -> EcsResult<()>,
    cancel: unsafe fn(NonNull<u8>),
}

impl RawCommand {
    pub(crate) unsafe fn new<C: Command>(cmd: &C) -> Self {
        let data = NonNull::new_unchecked((cmd as *const _ as *const u8).cast_mut());

        unsafe fn command_by_mut<C: Command>(data: NonNull<u8>, ecs: Ecs<'_>) -> EcsResult<()> {
            let data = data.cast::<C>().as_mut();
            data.command_by_mut(ecs)
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

    fn command(self, ecs: Ecs<'_>) -> EcsResult<()> {
        // Safety: Calling `self.command_by_mut` is safe because it's guaranteed
        // by owner called new().
        unsafe { (self.command_by_mut)(self.data, ecs) }
    }

    fn cancel(self) {
        // Safety: Calling `self.cancel` is safe because it's guaranteed by
        // owner called new().
        unsafe { (self.cancel)(self.data) };
    }
}

unsafe impl Send for RawCommand {}

pub fn schedule_command(cmd: CommandObject) {
    let ptr = SUB_CONTEXT.get();
    assert!(!ptr.is_dangling());

    // Safety: Current worker has valid sub context pointer.
    let comm = unsafe { ptr.as_ref().get_comm() };
    comm.send_command(cmd);
}

pub fn entity<'g>(eid: EntityId) -> EntityMoveCommandBuilder<'g, false> {
    EntityMoveCommandBuilder::new(eid)
}

pub struct EntityMoveCommandBuilder<'g, const OBJ: bool> {
    eid: EntityId,
    guard: MutexGuard<'g, EntMoveStorage>,
    len: usize,
}

impl EntityMoveCommandBuilder<'_, false> {
    fn new(eid: EntityId) -> Self {
        let shared = share::get_shared();
        let guard = shared.lock_entity_move_storage();
        Self { eid, guard, len: 0 }
    }
}

impl<'g> EntityMoveCommandBuilder<'g, true> {
    const fn with_guard(eid: EntityId, guard: MutexGuard<'g, EntMoveStorage>) -> Self {
        Self { eid, guard, len: 0 }
    }

    pub fn finish(mut self) -> CommandObject {
        assert!(self.len > 0);

        let cmd = self._finish();

        // Drops mutex guard without scheduling command.
        self.len = 0;
        drop(self);

        cmd
    }
}

impl<const OBJ: bool> EntityMoveCommandBuilder<'_, OBJ> {
    pub fn attach<C: Component>(mut self, component: C) -> Self {
        self.guard.insert_addition(self.eid, component);
        self.len += 1;
        self
    }

    pub fn detach<C: Component>(mut self) -> Self {
        self.guard.insert_removal(self.eid, C::key());
        self.len += 1;
        self
    }

    fn _finish(&mut self) -> CommandObject {
        self.guard.set_command_length(self.len);
        // Boxing a ZST command doesn't allocate memory for it.
        CommandObject::Boxed(Box::new(EntityMoveCommand))
    }
}

impl<const OBJ: bool> Drop for EntityMoveCommandBuilder<'_, OBJ> {
    fn drop(&mut self) {
        if self.len > 0 {
            let cmd = self._finish();
            schedule_command(cmd);
        }
    }
}

struct EntityMoveCommand;

impl Command for EntityMoveCommand {
    fn command_by_boxed(self: Box<Self>, ecs: Ecs<'_>) -> EcsResult<()> {
        let shared = ecs.get_shared_ptr();
        let shared = unsafe { shared.as_ref() };
        let mut guard = shared.lock_entity_move_storage();
        guard.consume(ecs);
        Ok(())
    }
}
