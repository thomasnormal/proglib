fn main() {
    let mut total = 0i32;
    for value in vec![1, 2, 3, 4] {
        total += value;
    }
    assert_eq!(total, 10);
}
