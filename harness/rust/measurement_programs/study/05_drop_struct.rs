use std::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);

struct Token;
impl Drop for Token {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

fn main() {
    {
        let _first = Token;
        let _second = Token;
    }
    assert_eq!(DROPS.load(Ordering::Relaxed), 2);
}
