// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/expr/return-in-block-tuple.rs
//! regression test for https://github.com/rust-lang/rust/issues/18110
//@ run-pass
#![allow(unreachable_code)]

fn main() {
    ({ return },);
}
