// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/numbers-arithmetic/i32-sub.rs
//@ run-pass




pub fn main() { let mut x: i32 = -400; x = 0 - x; assert_eq!(x, 400); }
