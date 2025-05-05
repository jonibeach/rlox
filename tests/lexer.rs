use codecrafters_interpreter::lexer::{Error as LexerError, Lexer, Symbol, Token};

#[test]
fn whitespace() {
    let mut lexer = Lexer::new();
    let src = "{\r\r\r\r}\n {}";
    lexer.lex(src);

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

#[test]
fn string() {
    let mut lexer = Lexer::new();
    let src = "\"hello\"";
    lexer.lex(src);

    assert_eq!(
        lexer.tokens(),
        [Symbol::new(0, Token::String("hello")),].as_slice()
    );

    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn string_fails() {
    let mut lexer = Lexer::new();
    let src = "\"hel\"lo\"";
    lexer.lex(src);

    assert_eq!(
        lexer.tokens(),
        [Symbol::new(0, Token::String("hel")),].as_slice()
    );

    assert_eq!(
        lexer.errors(),
        [
            Symbol::new(0, LexerError::UnexpectedCharacter('l')),
            Symbol::new(0, LexerError::UnexpectedCharacter('o')),
            Symbol::new(0, LexerError::UnterminatedString)
        ]
        .as_slice()
    )
}

#[test]
fn ue7() {
    let mut lexer = Lexer::new();
    let src = include_str!("ue7.lox");
    lexer.lex(src);
    assert_eq!(
        lexer.tokens(),
        [Symbol::new(0, Token::String("hello")),].as_slice()
    );
}
