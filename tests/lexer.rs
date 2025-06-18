use rlox::lexer::{Error, Keyword, Lexer, Token};

#[test]
fn whitespace() {
    let mut lexer = Lexer::new();
    let src = "{\r\r\r\r}\n {}";
    lexer.lex(src);
    let mut tokens = lexer.tokens().iter();

    assert_eq!(tokens.next().unwrap().token(), Token::LeftBrace);
    assert_eq!(tokens.next().unwrap().token(), Token::RightBrace);
    assert_eq!(tokens.next().unwrap().token(), Token::LeftBrace);
    assert_eq!(tokens.next().unwrap().token(), Token::RightBrace);

    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn string() {
    let mut lexer = Lexer::new();
    let src = "\"helloz\"";
    lexer.lex(src);

    assert_eq!(
        lexer.tokens().first().unwrap().token(),
        Token::String("helloz")
    );

    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn string_fails() {
    let mut lexer = Lexer::new();
    let src = "\"hel\"lo\"";
    lexer.lex(src);

    assert_eq!(
        lexer.tokens().first().unwrap().token(),
        Token::String("hel")
    );

    assert_eq!(
        lexer.tokens().iter().nth(1).unwrap().token(),
        Token::Identifier("lo")
    );

    assert_eq!(
        lexer.errors().first().unwrap().token(),
        Error::UnterminatedString,
    )
}

#[test]
fn unterminated_string() {
    let mut lexer = Lexer::new();
    let src = "\"baz";
    lexer.lex(src);

    assert_eq!(lexer.tokens(), [].as_slice());

    assert_eq!(
        lexer.errors().first().unwrap().token(),
        Error::UnterminatedString
    )
}

#[test]
fn number() {
    let mut lexer = Lexer::new();
    let src = "123.14";
    lexer.lex(src);
    assert_eq!(
        lexer.tokens().first().unwrap().token(),
        Token::Number(123.14.into(), "123.14")
    );
    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn number_invalid_amount_of_decimal_points() {
    let mut lexer = Lexer::new();
    let src = "123.14.1231";
    lexer.lex(src);
    assert_eq!(
        lexer.errors().first().unwrap().token(),
        Error::UnexpectedCharacter('.')
    )
}

#[test]
fn ident() {
    let mut lexer = Lexer::new();
    let src = "_testing_lox_z";
    lexer.lex(src);
    assert_eq!(
        lexer.without_symbols(),
        [Token::Identifier("_testing_lox_z"),].as_slice()
    );
    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn ident_2() {
    let mut lexer = Lexer::new();
    let src = "test=123.123";
    lexer.lex(src);
    assert_eq!(
        lexer.without_symbols(),
        [
            Token::Identifier("test"),
            Token::Equal,
            Token::Number(123.123.into(), "123.123")
        ]
    );
    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn keyword() {
    let mut lexer = Lexer::new();
    let src = "fun test() = class Test";
    lexer.lex(src);
    assert_eq!(
        lexer.without_symbols(),
        vec![
            Token::Keyword(Keyword::Fun),
            Token::Identifier("test"),
            Token::LeftParen,
            Token::RightParen,
            Token::Equal,
            Token::Keyword(Keyword::Class),
            Token::Identifier("Test")
        ]
    );
    assert_eq!(lexer.errors(), [].as_slice())
}

#[test]
fn keyword_2() {
    let mut lexer = Lexer::new();
    let src = "classor class or class";
    lexer.lex(src);
    assert_eq!(
        lexer.without_symbols(),
        [
            Token::Identifier("classor"),
            Token::Keyword(Keyword::Class),
            Token::Keyword(Keyword::Or),
            Token::Keyword(Keyword::Class),
        ]
    );
    assert_eq!(lexer.errors(), [].as_slice())
}
