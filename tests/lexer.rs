use codecrafters_interpreter::lexer::{Lexer, Symbol, Token};

#[test]
fn whitespace() {
    let mut lexer = Lexer::new();

    lexer.lex("{\r\r\r\r}\n {}".lines());

    assert_eq!(
        lexer.tokens(),
        [
            Symbol::new(0, Token::LeftBrace),
            Symbol::new(0, Token::RightBrace),
            Symbol::new(1, Token::LeftBrace),
            Symbol::new(1, Token::RightBrace)
        ]
        .as_slice()
    );

    assert_eq!(lexer.errors(), [].as_slice())
}
