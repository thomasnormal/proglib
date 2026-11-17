// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/const_prop/const-prop-ice3.rs
//@ run-pass (ensure that const-prop is run)

struct A<T: ?Sized>(T);

fn main() {
    let _x = &(&A([2, 3]) as &A<[i32]>).0 as *const [i32] as *const i32;
}
