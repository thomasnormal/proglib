trait Score {
    fn score(self) -> i32;
}

impl Score for i32 {
    fn score(self) -> i32 { self * 2 }
}

fn run<T: Score>(value: T) -> i32 {
    value.score()
}

fn main() {
    assert_eq!(run(21i32), 42);
}
