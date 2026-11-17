#[derive(Clone, Debug, PartialEq, Eq)]
struct Pair {
    left: i32,
    right: i32,
}

fn main() {
    let value = Pair { left: 20, right: 22 };
    let copy = value.clone();
    assert_eq!(value, copy);
    std::hint::black_box(format!("{:?}", copy));
}
