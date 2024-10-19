use super::{manager::Ecs, sched::ctrl::SUB_CONTEXT};
use std::fmt;

pub trait Command: Send + 'static {
    fn command(self: Box<Self>, ecs: Ecs<'_>);

    fn into_boxed(self) -> Box<dyn Command>
    where
        Self: Sized,
    {
        Box::new(self)
    }
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
    fn command(self: Box<Self>, ecs: Ecs<'_>) {
        (self)(ecs)
    }
}

// This function must be called on sub worker context.
pub fn schedule_command(cmd: impl Command) {
    let ptr = SUB_CONTEXT.get();
    assert!(!ptr.is_dangling());

    // Safety: Current worker has valid sub context pointer.
    let comm = unsafe { ptr.as_ref().comm() };
    comm.send_command(cmd.into_boxed());
}
