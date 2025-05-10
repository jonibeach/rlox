use codecrafters_interpreter::{lexer::Lexer, parser::Parser};

#[test]
fn bool() {
    let mut lexer = Lexer::new();
    let src = "true";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn nil() {
    let mut lexer = Lexer::new();
    let src = "nil";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "nil")
}

#[test]
fn unarys() {
    let mut lexer = Lexer::new();
    let src = "(!nil) == true";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn numbers() {
    let mut lexer = Lexer::new();
    let src = "1+2*45";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "91")
}

#[test]
fn neg_number() {
    let mut lexer = Lexer::new();
    let src = "-2";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "-2")
}

#[test]
fn neg_numbers_2() {
    let mut lexer = Lexer::new();
    let src = "1-2*45";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "-89")
}

#[test]
fn string_concat() {
    let mut lexer = Lexer::new();
    let src = "\"hello\"+\"hello\"";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "hellohello")
}

#[test]
fn string_concat_groups() {
    let mut lexer = Lexer::new();
    let src = "(\"quz\" + \"baz\") + (\"quz\" + \"bar\")";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();
    let res = ast.eval().unwrap();

    assert_eq!(res, "quzbazquzbar")
}
