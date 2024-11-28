#![allow(unexpected_cfgs)]

use my_ecs::prelude::*;
use std::{
    future::Future,
    pin::Pin,
    sync::{
        mpsc::{self, Sender},
        Arc, Condvar, Mutex,
    },
    task::{Context, Poll},
    thread,
};

#[test]
#[cfg(tsan)]
fn test_unsafefuture() {
    _test_unsafefuture();
}

/// Tests if polling to [`UnsafeFuture`] is safe over threads. Here's how the
/// test scenario looks like.
///
/// ```text
///     Timeline of each thread   
/// ---------------------------------
/// Main       | waker   | beholder
/// fut.poll() |         |
///            | wake()  |
///            |         | fut.poll()
/// ```
///
/// `beholder` must be able to see what `Main` have done to the `fut`. This
/// test will fail if data race occurs.
pub fn _test_unsafefuture() {
    let state = Arc::new(Mutex::new(0));

    let (tx, rx) = mpsc::channel::<UnsafeFuture>();
    let c_state = Arc::clone(&state);

    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let c_pair = Arc::clone(&pair);

    let beholder = thread::spawn(move || {
        // `beholder` will be woken up by `waker` thread.
        while let Ok(future) = rx.recv() {
            match unsafe { future.poll() } {
                Poll::Ready(()) => {
                    unsafe { drop(ReadyFuture::new(future)) };
                    break;
                }
                Poll::Pending => {}
            }
        }

        // All is ok, let's finish the test.
        assert_eq!(*c_state.lock().unwrap(), 2);
        let (lock, cvar) = &*c_pair;
        *lock.lock().unwrap() = true;
        cvar.notify_one();
    });

    let c_state = Arc::clone(&state);
    let future = async move {
        // If `beholder` cannot see future's change `Main` made, it will see
        // something that has not changed. Which means that it executes future
        // from the beginning.
        {
            // state: 0 -> 1
            let mut state = c_state.lock().unwrap();
            assert_eq!(*state, 0);
            *state += 1;
        }

        // `After` will spawn `waker` thread which will wake `beholder`.
        After::new(1).await;

        // state: 1 -> 2
        let mut state = c_state.lock().unwrap();
        assert_eq!(*state, 1);
        *state += 1;
    };
    let waker = MyWaker { tx };
    let future = UnsafeFuture::new(future, waker, |(), ()| {});

    // First polling on the future.
    let _ = unsafe { future.poll() };

    // Cleans up.
    let (lock, cvar) = &*pair;
    let mut is_end = lock.lock().unwrap();
    while !*is_end {
        is_end = cvar.wait(is_end).unwrap();
    }
    beholder.join().unwrap();
}

#[derive(Clone)]
struct MyWaker {
    tx: Sender<UnsafeFuture>,
}

impl WakeSend for MyWaker {
    fn wake_send(&self, handle: UnsafeFuture) {
        self.tx.send(handle).unwrap();
    }
}

struct After {
    cnt: u32,
}

impl After {
    fn new(cnt: u32) -> Self {
        Self { cnt }
    }
}

impl Future for After {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.cnt > 0 {
            self.get_mut().cnt -= 1;
            let w = cx.waker().clone();
            // `waker` thread will wake up `beholder` by sending future.
            let _waker = thread::spawn(move || w.wake());
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}
