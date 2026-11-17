// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/functions-closures/closure-returning-closure.rs
//@ run-pass
fn main() {
    let f = |_||x, y| x+y;
    assert_eq!(f(())(1, 2), 3);
}
