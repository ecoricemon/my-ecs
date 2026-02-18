//! A simple mock of `crossbeam_deque` for miri compatibility.
//!
//! This mock replaces the lock-free data structures with `Mutex<VecDeque<T>>`-based
//! implementations, which miri can reason about.

#![allow(unused)]

use std::{
    collections::VecDeque,
    fmt,
    sync::{Arc, Mutex},
};

/// Outcome of a steal operation.
pub(crate) enum Steal<T> {
    Success(T),
    Empty,
    Retry,
}

impl<T> Steal<T> {
    pub(crate) fn is_success(&self) -> bool {
        matches!(self, Steal::Success(_))
    }

    pub(crate) fn or_else<F: FnOnce() -> Steal<T>>(self, f: F) -> Steal<T> {
        match self {
            Steal::Success(_) => self,
            Steal::Empty => f(),
            Steal::Retry => {
                let other = f();
                if other.is_success() {
                    other
                } else {
                    Steal::Retry
                }
            }
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Steal<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Steal::Success(v) => f.debug_tuple("Success").field(v).finish(),
            Steal::Empty => write!(f, "Empty"),
            Steal::Retry => write!(f, "Retry"),
        }
    }
}

type SharedDeque<T> = Arc<Mutex<VecDeque<T>>>;

/// A work-stealing deque (worker end).
pub(crate) struct Worker<T> {
    inner: SharedDeque<T>,
}

impl<T> Worker<T> {
    pub(crate) fn new_lifo() -> Self {
        Self {
            inner: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub(crate) fn stealer(&self) -> Stealer<T> {
        Stealer {
            inner: Arc::clone(&self.inner),
        }
    }

    pub(crate) fn push(&self, item: T) {
        self.inner.lock().unwrap().push_back(item);
    }

    pub(crate) fn pop(&self) -> Option<T> {
        self.inner.lock().unwrap().pop_back()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }
}

impl<T> fmt::Debug for Worker<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Worker").finish_non_exhaustive()
    }
}

/// A stealer handle to a [`Worker`]'s deque.
pub(crate) struct Stealer<T> {
    inner: SharedDeque<T>,
}

impl<T> Stealer<T> {
    pub(crate) fn steal_batch_and_pop(&self, dest: &Worker<T>) -> Steal<T> {
        let mut src = self.inner.lock().unwrap();
        if src.is_empty() {
            return Steal::Empty;
        }

        // Steal half (at least one).
        let count = (src.len() + 1) / 2;
        let first = src.pop_front();

        let mut dest_q = dest.inner.lock().unwrap();
        for _ in 1..count {
            if let Some(item) = src.pop_front() {
                dest_q.push_back(item);
            }
        }

        match first {
            Some(item) => Steal::Success(item),
            None => Steal::Empty,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }
}

impl<T> Clone for Stealer<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T> fmt::Debug for Stealer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stealer").finish_non_exhaustive()
    }
}

/// A global queue that multiple workers can steal from.
pub(crate) struct Injector<T> {
    inner: SharedDeque<T>,
}

impl<T> Injector<T> {
    pub(crate) fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub(crate) fn push(&self, item: T) {
        self.inner.lock().unwrap().push_back(item);
    }

    pub(crate) fn steal(&self) -> Steal<T> {
        match self.inner.lock().unwrap().pop_front() {
            Some(item) => Steal::Success(item),
            None => Steal::Empty,
        }
    }

    pub(crate) fn steal_batch_and_pop(&self, dest: &Worker<T>) -> Steal<T> {
        let mut src = self.inner.lock().unwrap();
        if src.is_empty() {
            return Steal::Empty;
        }

        // Steal half (at least one).
        let count = (src.len() + 1) / 2;
        let first = src.pop_front();

        let mut dest_q = dest.inner.lock().unwrap();
        for _ in 1..count {
            if let Some(item) = src.pop_front() {
                dest_q.push_back(item);
            }
        }

        match first {
            Some(item) => Steal::Success(item),
            None => Steal::Empty,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }
}

impl<T> fmt::Debug for Injector<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Injector").finish_non_exhaustive()
    }
}
