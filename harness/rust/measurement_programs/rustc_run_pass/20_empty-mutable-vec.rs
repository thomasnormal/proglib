// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/array-slice-vec/empty-mutable-vec.rs
//@ run-pass


#![allow(unused_mut)]


pub fn main() { let mut _v: Vec<isize> = Vec::new(); }
