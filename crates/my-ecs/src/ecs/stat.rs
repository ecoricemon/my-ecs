//! Per-ECS runtime metrics.

use std::sync::Arc;
#[cfg(feature = "stat")]
use std::{
    cell::RefCell,
    sync::atomic::{AtomicU64, Ordering},
};

/// A point-in-time copy of an ECS instance's runtime counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RuntimeMetricsSnapshot {
    /// Number of system executions.
    pub system_executions: u64,
    /// Number of future polls.
    pub future_polls: u64,
    /// Number of ECS-aware parallel iterator executions.
    pub parallel_executions: u64,
}

/// Per-ECS runtime counters.
#[derive(Debug, Default)]
pub struct RuntimeMetrics {
    #[cfg(feature = "stat")]
    system_executions: AtomicU64,
    #[cfg(feature = "stat")]
    future_polls: AtomicU64,
    #[cfg(feature = "stat")]
    parallel_executions: AtomicU64,
}

impl RuntimeMetrics {
    /// Returns a point-in-time copy of the counters.
    ///
    /// Returns an empty snapshot when the `stat` feature is disabled.
    pub fn snapshot(&self) -> RuntimeMetricsSnapshot {
        #[cfg(feature = "stat")]
        {
            RuntimeMetricsSnapshot {
                system_executions: self.system_executions.load(Ordering::Relaxed),
                future_polls: self.future_polls.load(Ordering::Relaxed),
                parallel_executions: self.parallel_executions.load(Ordering::Relaxed),
            }
        }

        #[cfg(not(feature = "stat"))]
        {
            RuntimeMetricsSnapshot::default()
        }
    }

    /// Resets all counters.
    ///
    /// Concurrent increments may occur before or after each individual counter is reset.
    pub fn reset(&self) {
        #[cfg(feature = "stat")]
        {
            self.system_executions.store(0, Ordering::Relaxed);
            self.future_polls.store(0, Ordering::Relaxed);
            self.parallel_executions.store(0, Ordering::Relaxed);
        }
    }

    pub(crate) fn record_system_execution(&self) {
        #[cfg(feature = "stat")]
        self.system_executions.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn record_future_poll(&self) {
        #[cfg(feature = "stat")]
        self.future_polls.fetch_add(1, Ordering::Relaxed);
    }

    #[cfg(feature = "stat")]
    fn record_parallel_execution(&self) {
        self.parallel_executions.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg(feature = "stat")]
thread_local! {
    static CURRENT_METRICS: RefCell<Option<Arc<RuntimeMetrics>>> = const {
        RefCell::new(None)
    };
}

/// Runs `f` with `metrics` registered as the current thread's metrics target.
pub(crate) fn with_current_metrics<R, F>(metrics: &Arc<RuntimeMetrics>, f: F) -> R
where
    F: FnOnce() -> R,
{
    #[cfg(feature = "stat")]
    {
        let old = CURRENT_METRICS.with(|current| current.replace(Some(Arc::clone(metrics))));
        let _guard = CurrentMetricsGuard { old };
        f()
    }

    #[cfg(not(feature = "stat"))]
    {
        let _ = metrics;
        f()
    }
}

#[cfg(feature = "stat")]
struct CurrentMetricsGuard {
    old: Option<Arc<RuntimeMetrics>>,
}

#[cfg(feature = "stat")]
impl Drop for CurrentMetricsGuard {
    fn drop(&mut self) {
        CURRENT_METRICS.with(|current| {
            current.replace(self.old.take());
        });
    }
}

pub(crate) fn record_parallel_execution() {
    #[cfg(feature = "stat")]
    CURRENT_METRICS.with(|current| {
        current
            .borrow()
            .as_deref()
            .expect("runtime metrics scope must be set while executing a parallel iterator")
            .record_parallel_execution();
    });
}
