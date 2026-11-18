#[derive(Clone, Copy)]
enum Token { Byte(u8), End }

fn classify(token: Token) -> u8 {
    match token {
        Token::Byte(0 | 1) if true => 1,
        Token::Byte(_) => 2,
        Token::End => 3,
    }
}

fn main() {
    assert_eq!(classify(Token::Byte(1)), 1);
    assert_eq!(classify(Token::Byte(7)), 2);
    assert_eq!(classify(Token::End), 3);
}
