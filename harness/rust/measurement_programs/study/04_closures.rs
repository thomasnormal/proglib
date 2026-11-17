fn main() {
    let base = 7i32;
    let add = |value: i32| base + value;
    let twice = |value: i32| add(value) + add(value);
    assert_eq!(twice(5), 24);
}
