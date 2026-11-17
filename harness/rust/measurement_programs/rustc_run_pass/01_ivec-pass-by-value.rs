// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/array-slice-vec/ivec-pass-by-value.rs
//@ run-pass

fn f(_a: Vec<isize> ) { }
pub fn main() { f(vec![1, 2, 3, 4, 5]); }
