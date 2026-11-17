// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/binding/multi-let.rs
//@ run-pass

pub fn main() {
    let x = 10;
    let y = x;
    assert_eq!(y, 10);
}
