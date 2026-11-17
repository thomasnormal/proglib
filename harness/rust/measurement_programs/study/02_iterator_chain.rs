fn main() {
    let total = (0..12)
        .filter(|value| value % 2 == 0)
        .map(|value| value * 3)
        .fold(0, |acc, value| acc + value);
    assert_eq!(total, 90);
}
