// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/expr/if/if-ret.rs
//@ run-pass

#![allow(unused_parens)]

fn foo() { if (return) { } } //~ WARNING unreachable block in `if`

pub fn main() { foo(); }
