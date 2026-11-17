// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/binding/match-bot-2.rs
//@ run-pass
#![allow(unreachable_code)]
// n.b. This was only ever failing with optimization disabled.

fn a() -> isize { match return 1 { 2 => 3, _ => panic!() } }
pub fn main() { a(); }
