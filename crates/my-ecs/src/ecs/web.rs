#![cfg(target_arch = "wasm32")]

use super::{
    sched::{
        comm::{TaskKind, WorkId, WORK_ID},
        ctrl::SUB_CONTEXT,
    },
    worker::{Message, PanicMessage},
};
use crate::util::web;
use std::{cell::Cell, panic, sync::Once};

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

// `PanicInfo` has been renamed to `PanicHookInfo` since rust 1.81, but we use old name for the
// MSRV.
#[allow(deprecated)]
pub fn web_panic_hook(_info: &std::panic::PanicInfo<'_>) {
    let ptr = SUB_CONTEXT.with(Cell::get);
    if !ptr.is_dangling() {
        let WorkId { wid, sid, .. } = WORK_ID.with(Cell::get);
        let unrecoverable = WORK_ID.with(Cell::get).kind != TaskKind::System;
        let payload = Box::new("panic in wasm".to_owned());
        let msg = PanicMessage {
            wid,
            sid,
            unrecoverable,
            payload,
        };

        // Safety: Not a dangling pointer, and `SubContext` is not used. The corresponding thread
        // was panicked a bit ago, and it's running this function now.
        let cx = unsafe { ptr.as_ref() };

        // A sub worker was panicked while it was working on a task. That means it was in OPEN &
        // WORK states. In web, however, those states cannot be cancelled and remained as it was.
        // Therefore, we need to cancel it out here.
        cx.get_comm().signal().sub_work_count(1);
        cx.get_comm().signal().sub_open_count(1);

        cx.get_comm().send_message(Message::Panic(msg));
    }

    let _ = web::worker_post_message(&"panic".into());
}
