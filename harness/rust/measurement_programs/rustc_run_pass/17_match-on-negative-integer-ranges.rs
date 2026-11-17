// Source: rust-lang/rust tests/ui run-pass
// Revision: 5f4effd579500175af844241eb179e756190f1e7
// Upstream path: tests/ui/match/match-on-negative-integer-ranges.rs
//@ run-pass

fn main() {
    assert_eq!(false, match -50_i8 { -128i8..=-101i8 => true, _ => false, });

    assert_eq!(false, if let -128i8..=-101i8 = -50_i8 { true } else { false });
}
