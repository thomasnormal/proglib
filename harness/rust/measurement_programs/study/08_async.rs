use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

async fn answer() -> i32 {
    let value = async { 41i32 }.await;
    value + 1
}

fn no_op(_: *const ()) {}
fn clone(_: *const ()) -> RawWaker { RawWaker::new(std::ptr::null(), &VTABLE) }
static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);

fn block_on(mut future: impl Future<Output = i32>) -> i32 {
    let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) };
    let mut context = Context::from_waker(&waker);
    let mut future = unsafe { Pin::new_unchecked(&mut future) };
    match future.as_mut().poll(&mut context) {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("unexpected pending future"),
    }
}

fn main() {
    assert_eq!(block_on(answer()), 42);
}
