//! Utilities for the crate.

pub mod web;

/// Prints out the given string regardless of build target.
///
/// If build target is `wasm32`, this macro calls `web_sys::console::log_1`. Otherwise [`println`]
/// is called.
#[macro_export]
macro_rules! log {
    ($($t:tt)*) => {
        #[cfg(target_arch = "wasm32")]
        {
            $crate::utils::web::console_log(format!($($t)*))
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            println!($($t)*)
        }
    }
}

pub(crate) fn get_two_mut<T>(
    slice: &mut [T],
    idx1: usize,
    idx2: usize,
) -> Option<(&mut T, &mut T)> {
    if idx1 == idx2 || idx1 >= slice.len() || idx2 >= slice.len() {
        None
    } else if idx1 < idx2 {
        let (left, right) = slice.split_at_mut(idx2);
        let ref1 = &mut left[idx1];
        let ref2 = &mut right[0];
        Some((ref1, ref2))
    } else {
        let (left, right) = slice.split_at_mut(idx1);
        let ref2 = &mut left[idx2];
        let ref1 = &mut right[0];
        Some((ref1, ref2))
    }
}
