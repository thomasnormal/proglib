// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/binding/let-destruct-ref.rs
//@ run-pass

pub fn main() {
    let x = 3_usize;
    let ref y = x;
    assert_eq!(x, *y);
}
