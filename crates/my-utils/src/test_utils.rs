use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    thread::{self, JoinHandle},
    time::Duration,
};

/// A simple timer future that spawns a thread to sleep and then wakes the waker.
pub struct TimerFuture {
    dur: Duration,
    started: bool,
    handle: Option<JoinHandle<()>>,
}

impl TimerFuture {
    pub fn after(dur: Duration) -> Self {
        Self {
            dur,
            started: false,
            handle: None,
        }
    }
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.started {
            return Poll::Ready(());
        }
        self.started = true;
        let waker = cx.waker().clone();
        let dur = self.dur;

        let handle = thread::Builder::new()
            .name("TimerFuture".to_owned())
            .spawn(move || {
                thread::sleep(dur);
                waker.wake();
            })
            .unwrap();

        self.handle = Some(handle);

        Poll::Pending
    }
}

impl Drop for TimerFuture {
    fn drop(&mut self) {
        if let Some(handle) = self.handle.take() {
            match handle.join() {
                Ok(()) => {}
                Err(_) => {
                    if thread::panicking() {
                        std::process::abort();
                    } else {
                        panic!("failed to join a TimerFuture thread");
                    }
                }
            }
        }
    }
}
