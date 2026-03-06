use std::{
    num::NonZeroU32,
    sync::atomic::{
        self, AtomicI32, AtomicU32,
        Ordering::{Acquire, Relaxed, Release},
    },
    thread::{self, Thread},
};

const ASLEEP: i32 = -1;
const AWAKE: i32 = 0;
const ALARMED: i32 = 1;

#[derive(Debug)]
pub struct SignalSlot {
    thread: Thread,
    state: AtomicI32,
}

impl SignalSlot {
    pub const fn asleep_slot(thread: Thread) -> Self {
        Self {
            state: AtomicI32::new(ASLEEP),
            thread,
        }
    }

    pub const fn awake_slot(thread: Thread) -> Self {
        Self {
            state: AtomicI32::new(AWAKE),
            thread,
        }
    }
}

#[derive(Debug)]
pub struct Signal {
    slots: Vec<SignalSlot>,
    rng: Xorshift,
}

impl Signal {
    const RNG_SEED: NonZeroU32 = unsafe { NonZeroU32::new_unchecked(0x7A7A_A7A7) };

    pub const fn new(slots: Vec<SignalSlot>) -> Self {
        Self {
            slots,
            rng: Xorshift::new(Self::RNG_SEED),
        }
    }

    pub const fn empty() -> Self {
        Self {
            slots: Vec::new(),
            rng: Xorshift::new(Self::RNG_SEED),
        }
    }

    /// Blocks **current thread**.
    ///
    /// * index - An index to the handle of **current thread** in the vector that was given at
    ///   [`Signal::new`].
    pub fn wait(&self, index: usize) {
        // ALARMED -> AWAKE: Consumes the alarm
        let slot = &self.slots[index];
        if slot.state.fetch_sub(1, Acquire) == ALARMED {
            return;
        }

        // AWAKE -> ASLEEP: Blocks the thread
        loop {
            thread::park();
            if slot
                .state
                .compare_exchange(ALARMED, AWAKE, Relaxed, Relaxed)
                .is_ok()
            {
                break;
            }
        }
        atomic::fence(Acquire);
    }

    /// Tries to wake a thread for the given index.
    ///
    /// If the thread was not parked, then tries to wake other threads. If all failed, then sets a
    /// token to the slot at the given index. It will make the thread won't park at the next
    /// [`Signal::wait`] with consuming the token.
    ///
    /// * index - An index to the handle of a thread in the vector that was given at
    ///   [`Signal::new`].
    ///
    pub fn notify_try(&self, index: usize) {
        let n = self.slots.len();

        // Tries to wake a sleeping thread.
        for slot in self.slots.iter().cycle().skip(index).take(n) {
            if slot
                .state
                .compare_exchange(ASLEEP, ALARMED, Release, Relaxed)
                .is_ok()
            {
                // ASLEEP -> ALARMED: Wakes up.
                slot.thread.unpark();
                return;
            }
        }

        // No sleeping threads at the time, then sets an alarm.
        let slot = &self.slots[index];
        if slot.state.swap(ALARMED, Release) == ASLEEP {
            slot.thread.unpark();
        }
    }

    /// Wakes a thread.
    pub fn notify_one(&self) {
        let index = self.rng.next() as usize % self.slots.len();
        self.notify_try(index);
    }

    /// Wakes all threads.
    pub fn notify_all(&self) {
        for slot in &self.slots {
            if slot.state.swap(ALARMED, Release) == ASLEEP {
                slot.thread.unpark();
            }
        }
    }
}

impl Default for Signal {
    fn default() -> Self {
        Self::empty()
    }
}

/// A random number generator based on 32bits state.
///
/// The genrator can be shared and generate random numbers across workers but it doesn't provide
/// synchronization.
///
/// # Reference
///
/// [Xorshift](https://en.wikipedia.org/wiki/Xorshift)
#[derive(Debug)]
#[repr(transparent)]
pub struct Xorshift {
    state: AtomicU32,
}

impl Xorshift {
    /// Creates a new [`Xorshift`].
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Xorshift;
    /// use std::num::NonZeroU32;
    ///
    /// let generator = Xorshift::new(NonZeroU32::MIN);
    /// ```
    pub const fn new(seed: NonZeroU32) -> Self {
        Self {
            state: AtomicU32::new(seed.get()),
        }
    }

    /// Generates next random number from the current state.
    ///
    /// You can call this method on multiple workers at the same time. The generator is using atomic
    /// variable under the hood, so that it's guaranteed to generate a random number from different
    /// states.
    ///
    /// # Examples
    ///
    /// ```
    /// use my_utils::ds::Xorshift;
    /// use std::{num::NonZeroU32, collections::HashSet};
    ///
    /// let generator = Xorshift::new(NonZeroU32::MIN);
    /// let mut randoms = HashSet::new();
    /// for _ in 0..100 {
    ///     let is_new = randoms.insert(generator.next());
    ///     assert!(is_new);
    /// }
    /// ```
    pub fn next(&self) -> u32 {
        let mut cur = self.state.load(Relaxed);
        loop {
            let mut new = cur;
            new ^= new << 13;
            new ^= new >> 17;
            new ^= new << 5;
            if let Err(slot) = self.state.compare_exchange_weak(cur, new, Relaxed, Relaxed) {
                cur = slot;
            } else {
                return new;
            }
        }
    }
}
