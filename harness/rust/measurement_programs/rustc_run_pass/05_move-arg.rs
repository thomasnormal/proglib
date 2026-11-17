// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/moves/move-arg.rs
//@ run-pass

fn test(foo: isize) { assert_eq!(foo, 10); }

pub fn main() { let x = 10; test(x); }
