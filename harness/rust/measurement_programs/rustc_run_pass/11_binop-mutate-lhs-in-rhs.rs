// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/binop/binop-mutate-lhs-in-rhs.rs
//! Regression test for <https://github.com/rust-lang/rust/issues/27054>.
//@ run-pass

fn main() {
    let x = &mut 1;
    assert_eq!(*x + { *x=2; 1 }, 2);
}
