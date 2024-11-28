use super::system::{FnOnceSystem, System, SystemGroup, SystemId};
use crate::ecs::{
    sys::system::{InsertPos, NonZeroTick, SystemBond, SystemData},
    EcsError,
};
use crate::util::prelude::*;
use std::{any::Any, array, fmt, hash::BuildHasher};

/// * `S` - Hasher.
/// * `N` - Number of [`SystemGroup`], which operates in a different configurable way from each other.
#[derive(Debug)]
pub(crate) struct SystemStorage<S, const N: usize> {
    pub(crate) sgroups: Multi<SystemGroup<S>, N>,
}

impl<S, const N: usize> SystemStorage<S, N>
where
    S: BuildHasher + Default + 'static,
{
    pub(crate) fn new() -> Self {
        // For now, group index `gi` below is limited up to u16::MAX - 1 by `SystemId`.
        // Here, we check N in terms of bounds at compile time.
        let _: () = const { assert!(N < SystemId::max_group_index() as usize) };

        let sgroups = array::from_fn(|gi| SystemGroup::new(gi as u16));

        Self {
            sgroups: Multi::new(sgroups),
        }
    }

    pub(crate) fn get_group_mut(&mut self, gi: usize) -> &mut SystemGroup<S> {
        self.sgroups.switch_to(gi)
    }

    pub(crate) fn register(
        &mut self,
        sdata: SystemData,
        volatile: bool,
    ) -> Result<(), EcsError<SystemData>> {
        // Id and flags of the system must be valid here.
        debug_assert!(!sdata.id().is_dummy());
        debug_assert!(!sdata.flags().is_empty());

        self.sgroups
            .switch_to(sdata.id().group_index() as usize)
            .register(sdata, volatile)
    }

    /// Activates the system. If the system is already active, nothing takes place.
    pub(crate) fn activate(
        &mut self,
        target: &SystemId,
        at: InsertPos,
        live: NonZeroTick,
    ) -> Result<(), EcsError> {
        // For better error message.
        #[cfg(debug_assertions)]
        if let InsertPos::After(at) = &at {
            if target.group_index() != at.group_index() {
                let reason = debug_format!(
                    "tried to activate a system after a system belonging to different group"
                );
                return Err(EcsError::UnknownSystem(reason, ()));
            }
        }

        self.sgroups
            .switch_to(target.group_index() as usize)
            .activate(target, at, live)
    }

    pub(crate) fn unregister(&mut self, sid: &SystemId) -> Result<(), EcsError> {
        self.sgroups
            .switch_to(sid.group_index() as usize)
            .unregister(sid)
    }

    pub(crate) fn inactivate(&mut self, sid: &SystemId) -> Result<(), EcsError> {
        self.sgroups
            .switch_to(sid.group_index() as usize)
            .inactivate(sid)
    }

    pub(crate) fn drain_dead(&mut self) -> impl Iterator<Item = SystemData> + '_ {
        self.sgroups
            .iter_mut()
            .flat_map(|sgroup| sgroup.drain_dead())
    }

    pub(crate) fn drain_poisoned(
        &mut self,
    ) -> impl Iterator<Item = (SystemData, Box<dyn Any + Send>)> + '_ {
        self.sgroups
            .iter_mut()
            .flat_map(|sgroup| sgroup.drain_poisoned())
    }
}

pub struct SystemDesc<Sys> {
    /// System itself. Clients cannot put `SystemData` in, which is only allowed
    /// to the crate.
    pub(crate) sys: Or<Sys, SystemData>,

    /// Whether the system is private system or not. Private system is a kind of
    /// systems which is used internally.
    pub(crate) private: bool,

    /// Group index of the system.
    pub group_index: u16,

    /// Whether the system is volatile or not. A volatile system will be
    /// discarded from memory after get executed as much as its lifetime.
    /// Unlike volatile system, non-volatile system will move to inactivate
    /// state instead of being discarded.
    pub volatile: bool,

    /// Lifetime and insert position in an active system cycle.  
    /// - Lifetime(live): Determines how long the system should be executed.
    ///   Whenever client schedules ecs, lifetime of executed system decreases
    ///   by 1 conceptually.
    /// - Insert position: Active systems get executed in an order. Client can
    ///   designate where the system locates. [`InsertPos::Front`] means the
    ///   first position in the order, while [`InsertPos::Back`] means the last
    ///   position in the order. Of course, client can put the system in the
    ///   middle of the order by [`InsertPos::After`].
    pub activation: Option<(NonZeroTick, InsertPos)>,
}

impl<Sys> fmt::Debug for SystemDesc<Sys> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SystemDesc")
            .field("private", &self.private)
            .field("group_index", &self.group_index)
            .field("volatile", &self.volatile)
            .field("activation", &self.activation)
            .finish_non_exhaustive()
    }
}

impl<Sys> SystemDesc<Sys>
where
    Sys: System,
{
    pub fn with_system<T, OutSys>(self, sys: T) -> SystemDesc<OutSys>
    where
        T: Into<SystemBond<OutSys>>,
        OutSys: System,
    {
        let sys: SystemBond<OutSys> = sys.into();

        SystemDesc::<OutSys> {
            sys: Or::A(sys.into_inner()),
            private: self.private,
            group_index: self.group_index,
            volatile: self.volatile,
            activation: self.activation,
        }
    }

    pub fn with_once<T, Req, F>(self, sys: T) -> SystemDesc<FnOnceSystem<Req, F>>
    where
        T: Into<FnOnceSystem<Req, F>>,
        FnOnceSystem<Req, F>: System,
        F: Send,
    {
        let activation = if let Some((_live, pos)) = self.activation {
            Some((NonZeroTick::MIN, pos))
        } else {
            None
        };

        SystemDesc::<FnOnceSystem<Req, F>> {
            sys: Or::A(sys.into()),
            private: self.private,
            group_index: self.group_index,
            volatile: self.volatile,
            activation,
        }
    }

    pub fn with_group_index(self, index: u16) -> Self {
        Self {
            group_index: index,
            ..self
        }
    }

    pub fn with_volatile(self, volatile: bool) -> Self {
        Self { volatile, ..self }
    }

    pub fn with_activation(self, live: NonZeroTick, insert_at: InsertPos) -> Self {
        Self {
            activation: Some((live, insert_at)),
            ..self
        }
    }

    pub(crate) fn with_data(self, sdata: SystemData) -> SystemDesc<()> {
        SystemDesc::<()> {
            sys: Or::B(sdata),
            private: self.private,
            group_index: self.group_index,
            volatile: self.volatile,
            activation: self.activation,
        }
    }

    pub(crate) fn with_private(self, private: bool) -> Self {
        Self { private, ..self }
    }
}

impl SystemDesc<()> {
    pub const fn new() -> Self {
        Self {
            sys: Or::A(()),
            private: false,
            group_index: 0,
            volatile: true,
            activation: Some((NonZeroTick::MAX, InsertPos::Back)),
        }
    }
}

impl Default for SystemDesc<()> {
    fn default() -> Self {
        Self::new()
    }
}
