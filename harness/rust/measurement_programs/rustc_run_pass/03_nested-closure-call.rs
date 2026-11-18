// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/closures/nested-closure-call.rs
//! regression test for https://github.com/rust-lang/rust/issues/24779
//@ run-pass
fn main() {
    assert_eq!((|| || 42)()(), 42);
}
