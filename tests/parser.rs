use codecrafters_interpreter::{
    lexer::Lexer,
    parser::{Cmp, CmpOp, Equality, Expr, Factor, Parser, Primary, Term, TermOp, Unary, UnaryOp},
};

#[test]
fn group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" + / 234.0)";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();
    Expr(Equality::new(Cmp::new(
        Term::new(Factor::new(Unary::primary(Primary::String("test"))))
            .extend(TermOp::Add, Unary::primary(Primary::Number(234.into()))),
    )));

    assert_eq!(
        ast,
        vec![Expr(Equality::new(Cmp::new()))

            Ast::Group(
            Ast::BinOp(
                Ast::String("test").into(),
                BinOp::Div,
                Ast::Number(234.0.into()).into()
            )
            .into()
        )]
    )
}

#[test]
fn group_in_group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" == (\"hello\" == 555.111))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::Group(
            Ast::CmpOp(
                Ast::String("test").into(),
                CmpOp::Eq,
                Ast::Group(
                    Ast::CmpOp(
                        Ast::String("hello").into(),
                        CmpOp::Eq,
                        Ast::Number(555.111.into()).into()
                    )
                    .into()
                )
                .into()
            )
            .into()
        )]
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
        vec![Ast::Group(
            Ast::UnaryOp(
                UnaryOp::Not,
                Ast::Group(
                    Ast::BinOp(
                        Ast::Number(123.0.into()).into(),
                        BinOp::Add,
                        Ast::UnaryOp(UnaryOp::Neg, Ast::Number(55.03.into()).into()).into()
                    )
                    .into()
                )
                .into()
            )
            .into()
        )]
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
        vec![Ast::Group(
            Ast::BinOp(
                Ast::BinOp(
                    Ast::Number(77.0.into()).into(),
                    BinOp::Mul,
                    Ast::UnaryOp(UnaryOp::Neg, Ast::Number(74.0.into()).into()).into()
                )
                .into(),
                BinOp::Div,
                Ast::Group(
                    Ast::BinOp(
                        Ast::Number(87.0.into()).into(),
                        BinOp::Mul,
                        Ast::Number(99.0.into()).into()
                    )
                    .into()
                )
                .into()
            )
            .into()
        )]
    )
}

#[test]
fn basic_cmps_with_groups() {
    let mut lexer = Lexer::new();
    let src = "(94 != 25) == ((-39 + 86) >= (72 * 19))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse();

    assert_eq!(
        ast,
        vec![Ast::CmpOp(
            Ast::Group(
                Ast::CmpOp(
                    Ast::Number(94.0.into()).into(),
                    CmpOp::Neq,
                    Ast::Number(25.0.into()).into()
                )
                .into()
            )
            .into(),
            CmpOp::Eq,
            Ast::Group(
                Ast::CmpOp(
                    Ast::Group(
                        Ast::BinOp(
                            Ast::UnaryOp(UnaryOp::Neg, Ast::Number(39.0.into()).into()).into(),
                            BinOp::Add,
                            Ast::Number(86.0.into()).into()
                        )
                        .into()
                    )
                    .into(),
                    CmpOp::Gte,
                    Ast::Group(
                        Ast::BinOp(
                            Ast::Number(72.0.into()).into(),
                            BinOp::Mul,
                            Ast::Number(19.0.into()).into()
                        )
                        .into()
                    )
                    .into()
                )
                .into()
            )
            .into()
        )]
    )
}
