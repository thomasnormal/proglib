// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/unsafe/new-unsafe-pointers.rs
//@ run-pass

fn main() {
    let _a: *const isize = 3 as *const isize;
    let _a: *mut isize = 3 as *mut isize;
}
