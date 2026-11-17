// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/array-slice-vec/vec-repeat-with-cast.rs
//@ run-pass


pub fn main() { let _a = [0; 1 as usize]; }
