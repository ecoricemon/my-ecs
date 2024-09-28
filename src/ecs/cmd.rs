use super::{manager::Ecs, sched::SUB_CONTEXT};
use std::fmt;

pub trait Command: Send + 'static {
    fn command(self: Box<Self>, ecs: Ecs<'_>);
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

pub fn put_command(cmd: impl Command) {
    let cx = unsafe { SUB_CONTEXT.get().as_ref() };
    cx.send_command(Box::new(cmd));
}
