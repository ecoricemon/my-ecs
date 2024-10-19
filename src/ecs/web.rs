#![cfg(target_arch = "wasm32")]

use super::{
    sched::{
        comm::{TaskKind, WORK_ID},
        ctrl::SUB_CONTEXT,
    },
    worker::{Message, PanicMessage},
};
use crate::util::prelude::*;
use std::{
    panic::{self, PanicInfo},
    sync::Once,
};

pub fn set_panic_hook_once() {
    static PANIC_HOOK: Once = Once::new();

    PANIC_HOOK.call_once(|| {
        let old_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            old_hook(info);
            web_panic_hook(info);
        }));
    })
}

pub fn web_panic_hook(_info: &PanicInfo<'_>) {
    let ptr = SUB_CONTEXT.get();
    if !ptr.is_dangling() {
        let wid = WORK_ID.get().wid;
        let sid = WORK_ID.get().sid;
        let unrecoverable = WORK_ID.get().kind != TaskKind::System;
        let payload = Box::new("panic in wasm".to_owned());
        let msg = PanicMessage {
            wid,
            sid,
            unrecoverable,
            payload,
        };

        // Safety: Not a dangling pointer, and `SubContext` is not used.
        // The corresponding thread was panicked a bit ago and
        // it's running this function now.
        let cx = unsafe { ptr.as_ref() };
        cx.comm().send_message(Message::Panic(msg));
    }

    let _ = web_util::worker_post_message(&"panic".into());
}
