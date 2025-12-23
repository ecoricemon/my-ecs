//! Utilities for the crate.

pub mod web;

/// Prints out the given string regardless of build target.
///
/// If build target is `wasm32`, this macro calls `web_sys::console::log_1`.
/// Otherwise [`println`] is called.
#[macro_export]
macro_rules! log {
    ($($t:tt)*) => {
        #[cfg(target_arch = "wasm32")]
        {
            $crate::util::web::console_log(format!($($t)*))
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            println!($($t)*)
        }
    }
}

/// A module containing test helper functionalities.
pub use my_ecs_util::call_timeout;
