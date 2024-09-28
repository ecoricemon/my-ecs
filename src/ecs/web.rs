#![cfg(target_arch = "wasm32")]

use super::sched::web::web_panic_hook;
use std::{panic, sync::Once};

pub fn set_panic_hook_once() {
    PANIC_HOOK.call_once(|| {
        let old_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            old_hook(info);
            web_panic_hook(info);
        }));
    })
}

static PANIC_HOOK: Once = Once::new();
