// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/generics/generic-newtype-struct.rs
//@ run-pass

struct S<T>(#[allow(dead_code)] T);

pub fn main() {
    let _s = S(2);
}
