use codecrafters_interpreter::{
    lexer::Lexer,
    parser::{Ast, BinOp, Parser, UnaryOp},
};

#[test]
fn group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" 234.0)";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::Group(vec![
            Ast::String("test"),
            Ast::Number(234.0.into())
        ])]
    )
}

#[test]
fn group_in_group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" (\"hello\" 555.111))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::Group(vec![
            Ast::String("test"),
            Ast::Group(vec![Ast::String("hello"), Ast::Number(555.111.into())])
        ])]
    )
}

#[test]
fn negate_and_not() {
    let mut lexer = Lexer::new();
    let src = "(!(123 +-55.03))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::Group(vec![Ast::UnaryOp(
            UnaryOp::Not,
            Box::new(Ast::Group(vec![Ast::BinOp(
                Ast::Number(123.0.into()).into(),
                BinOp::Add,
                Ast::UnaryOp(UnaryOp::Neg, Ast::Number(55.03.into()).into()).into()
            )]))
        )])]
    )
}

#[test]
fn basic_expr() {
    let mut lexer = Lexer::new();
    let src = "    82 * 99 / 18";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::BinOp(
            Ast::BinOp(
                Ast::Number(82.0.into()).into(),
                BinOp::Mul,
                Ast::Number(99.0.into()).into()
            )
            .into(),
            BinOp::Div,
            Ast::Number(18.0.into()).into()
        )]
    )
}

#[test]
fn nested_expr_pretty_basic_still_with_comments() {
    let mut lexer = Lexer::new();
    let src = "// comment is ignored\n(77 * -74 / (87 * 99))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::Group(vec![Ast::BinOp(
            Ast::BinOp(
                Ast::Number(77.0.into()).into(),
                BinOp::Mul,
                Ast::UnaryOp(UnaryOp::Neg, Ast::Number(74.0.into()).into()).into()
            )
            .into(),
            BinOp::Div,
            Ast::Group(vec![Ast::BinOp(
                Ast::Number(87.0.into()).into(),
                BinOp::Mul,
                Ast::Number(99.0.into()).into()
            )])
            .into()
        )])]
    )
}
