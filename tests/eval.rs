use codecrafters_interpreter::{
    eval::{ErrorKind, Executor},
    lexer::{Keyword, Lexer, Symbol, Token},
    parser::Parser,
};

#[test]
fn bool() {
    let mut lexer = Lexer::new();
    let src = "true;";
    lexer.lex(src);

    assert_eq!(
        lexer.tokens(),
        [
            Symbol::new(0, Token::Keyword(Keyword::True)),
            Symbol::new(0, Token::Semicolon)
        ]
        .as_slice()
    );

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.declarations().iter().next().unwrap()),
        "true"
    );
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn nil() {
    let mut lexer = Lexer::new();
    let src = "nil;";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "nil")
}

#[test]
fn unarys() {
    let mut lexer = Lexer::new();
    let src = "(!nil) == true;";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn numbers() {
    let mut lexer = Lexer::new();
    let src = "1+2*45;";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "91")
}

#[test]
fn neg_number() {
    let mut lexer = Lexer::new();
    let src = "-2;";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "-2")
}

#[test]
fn neg_numbers_2() {
    let mut lexer = Lexer::new();
    let src = "1-2*45;";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "-89")
}

#[test]
fn string_concat() {
    let mut lexer = Lexer::new();
    let src = "\"hello\"+\"hello\";";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "hellohello")
}

#[test]
fn string_concat_groups() {
    let mut lexer = Lexer::new();
    let src = "(\"quz\" + \"baz\") + (\"quz\" + \"bar\");";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let res = executor.eval().unwrap();

    assert_eq!(res, "quzbazquzbar")
}

#[test]
fn unary_expected_num() {
    let mut lexer = Lexer::new();
    let src = r#"-"test";"#;
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let err = executor.eval().unwrap_err();

    assert!(matches!(err.kind(), ErrorKind::MustBeNumber))
}

#[test]
fn expect_both_nums_or_strings() {
    let mut lexer = Lexer::new();
    let src = r#"// lol comment here
        "test" + 123.44;"#;
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(&program);
    let err = executor.eval().unwrap_err();

    assert_eq!(err.line(), 1);
    assert!(matches!(err.kind(), ErrorKind::BothMustBeNumbersOrStrings))
}

#[test]
fn print() {
    let mut lexer = Lexer::new();
    let src = r#"
        // lol comment here
        print 123.44;"#;

    lexer.lex(src);
    assert_eq!(
        lexer.tokens(),
        [
            Symbol::new(2, Token::Keyword(Keyword::Print)),
            Symbol::new(2, Token::Number(123.44.into(), "123.44")),
            Symbol::new(2, Token::Semicolon)
        ]
        .as_slice()
    );

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    assert_eq!(
        format!("{}", program.declarations().iter().next().unwrap()),
        "(print 123.44)"
    );

    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(&program, &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    assert_eq!(stdout.lines().next().unwrap(), "123.44");
}

#[test]
fn multiline_with_not_ascii() {
    let mut lexer = Lexer::new();
    let src = r#"
    // This program prints the result of a comparison operation
    // It also tests multi-line strings and non-ASCII characters
    print false != false;

    print "53
    17
    98
    ";

    print "There should be an empty line above this.";

    print "(" + "" + ")";

    print "non-ascii: ॐ";"#;

    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(&program, &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    let mut lines = stdout.lines();

    assert_eq!(lines.next().unwrap(), "false");
    assert_eq!(lines.next().unwrap(), "53");
    assert_eq!(lines.next().unwrap().trim(), "17");
    assert_eq!(lines.next().unwrap().trim(), "98");
    assert_eq!(lines.next().unwrap().trim(), "");
    assert_eq!(
        lines.next().unwrap(),
        "There should be an empty line above this."
    );
    assert_eq!(lines.next().unwrap(), "()");
    assert_eq!(lines.next().unwrap(), "non-ascii: ॐ");
    assert!(lines.next().is_none());
}

#[test]
fn basic_vars() {
    let mut lexer = Lexer::new();
    let src = r#"
    var test = "abc";

    print test;
    print test + test;
    print test + "___" + test;"#;

    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(&program, &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    let mut lines = stdout.lines();

    assert_eq!(lines.next().unwrap(), "abc");
    assert_eq!(lines.next().unwrap(), "abcabc");
    assert_eq!(lines.next().unwrap().trim(), "abc___abc");
    assert!(lines.next().is_none());
}

#[test]
fn basic_string_vars() {
    let mut lexer = Lexer::new();
    let src = r#"
        var baz = 82;
        var world = 82;
        print baz + world;
        var quz = 82;
        print baz + world + quz;"#;

    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(&program, &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    let mut lines = stdout.lines();

    assert_eq!(lines.next().unwrap(), (82 * 2).to_string());
    assert_eq!(lines.next().unwrap(), (82 * 3).to_string());
    assert!(lines.next().is_none());
}

#[test]
fn basic_var_reassignment() {
    let mut lexer = Lexer::new();
    let src = r#"
        var baz = 82;
        print baz;
        baz = baz * 2;
        print baz;
        baz = baz * 2;
        print baz;"#;

    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let mut declrs = program.declarations().iter();

    assert_eq!(format!("{}", declrs.next().unwrap()), "(varDecl baz 82.0)");
    assert_eq!(format!("{}", declrs.next().unwrap()), "(print (varAccess baz))");
    assert_eq!(format!("{}", declrs.next().unwrap()), "(varMut baz (* (varAccess baz) 2.0))");
    assert_eq!(format!("{}", declrs.next().unwrap()), "(print (varAccess baz))");
    assert_eq!(format!("{}", declrs.next().unwrap()), "(varMut baz (* (varAccess baz) 2.0))");
    assert_eq!(format!("{}", declrs.next().unwrap()), "(print (varAccess baz))");

    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(&program, &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    let mut lines = stdout.lines();

    assert_eq!(lines.next().unwrap(), 82.to_string());
    assert_eq!(lines.next().unwrap(), (82 * 2).to_string());
    assert_eq!(lines.next().unwrap(), (82 * 4).to_string());
    assert!(lines.next().is_none());
}
