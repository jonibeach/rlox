use codecrafters_interpreter::{lexer::Lexer, parser::Parser};

#[test]
fn group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" +  234.0);";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(group (+ test 234.0))"#
    )
}

#[test]
fn group_in_group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" / (\"hello\" + 555.111));";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(group (/ test (group (+ hello 555.111))))"#
    )
}

#[test]
fn negate_and_not() {
    let mut lexer = Lexer::new();
    let src = "(!(123.0 +-55.03));";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(group (! (group (+ 123.0 (- 55.03)))))"#
    )
}

#[test]
fn basic_expr() {
    let mut lexer = Lexer::new();
    let src = "    82 * 99 / 18;";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(/ (* 82.0 99.0) 18.0)"#,
    )
}

#[test]
fn nested_expr_pretty_basic_still_with_comments() {
    let mut lexer = Lexer::new();
    let src = "// comment is ignored\n(77 * -74 / (87 * 99));";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(group (/ (* 77.0 (- 74.0)) (group (* 87.0 99.0))))"#,
    )
}

#[test]
fn basic_cmps_with_groups() {
    let mut lexer = Lexer::new();
    let src = "(94 != 25) == ((-39 + 86) >= (72 * 19));";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().first().unwrap()),
        r#"(== (group (!= 94.0 25.0)) (group (>= (group (+ (- 39.0) 86.0)) (group (* 72.0 19.0)))))"#,
    )
}

#[test]
fn var() {
    let mut lexer = Lexer::new();
    let src = "var x = 10;\nprint x;";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut declarations = program.declarations().into_iter();

    assert_eq!(
        format!("{}", declarations.next().unwrap()),
        r#"(varDecl x 10.0)"#
    );

    assert_eq!(
        format!("{}", declarations.next().unwrap()),
        r#"(print (varAccess x))"#
    )
}

#[test]
fn empty_print_err() {
    let mut lexer = Lexer::new();
    let src = "print;";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse();
    assert_eq!(
        format!("{}", program.unwrap_err()),
        "[line 1] Error at ';': Expect LEFT_PAREN."
    );
}

#[test]
fn var_assign() {
    let mut lexer = Lexer::new();
    let src = "var a = 2; var b = 3; var c = a = b = 2;";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut declarations = program.declarations().iter();

    assert_eq!(format!("{}", declarations.next().unwrap()), "(varDecl a 2.0)");
    assert_eq!(format!("{}", declarations.next().unwrap()), "(varDecl b 3.0)");
    assert_eq!(format!("{}", declarations.next().unwrap()), "(varDecl c (varAssign a (varAssign b 2.0)))");
}
