// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/methods/by-value-self-method-on-int.rs
//! Regression test for <https://github.com/rust-lang/rust/issues/4759>.
//! This used to trigger LLVM assertion.
//@ run-pass

trait U { fn f(self); }
impl U for isize { fn f(self) {} }
pub fn main() { 4.f(); }
