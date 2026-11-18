fn add_one(value: Option<i32>) -> Option<i32> {
    let value = value?;
    Some(value + 1)
}

fn main() {
    assert_eq!(add_one(Some(41)), Some(42));
    assert_eq!(add_one(None), None);
}
