use codecrafters_interpreter::{
    lexer::Lexer,
    parser::{CmpOp, EqOp, Expr, FactorOp, Parser, Primary, TermOp, UnaryOp},
};

#[test]
fn group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" +  234.0)";
    lexer.lex(src);

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Primary(Primary::Group(
            Expr::Term(
                Expr::Primary(Primary::String("test")).into(),
                TermOp::Add,
                Expr::Primary(Primary::Number(234.0.into())).into()
            )
            .into()
        ))
    )
}

#[test]
fn group_in_group() {
    let mut lexer = Lexer::new();
    let src = "(\"test\" / (\"hello\" + 555.111))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Primary(Primary::Group(
            Expr::Factor(
                Expr::Primary(Primary::String("test")).into(),
                FactorOp::Div,
                Expr::Primary(Primary::Group(
                    Expr::Term(
                        Expr::Primary(Primary::String("hello")).into(),
                        TermOp::Add,
                        Expr::Primary(Primary::Number(555.111.into())).into()
                    )
                    .into()
                ))
                .into()
            )
            .into()
        ))
    )
}

#[test]
fn negate_and_not() {
    let mut lexer = Lexer::new();
    let src = "(!(123 +-55.03))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Primary(Primary::Group(
            Expr::Unary(
                UnaryOp::Not,
                Expr::Primary(Primary::Group(
                    Expr::Term(
                        Expr::Primary(Primary::Number(123.0.into())).into(),
                        TermOp::Add,
                        Expr::Unary(
                            UnaryOp::Neg,
                            Expr::Primary(Primary::Number(55.03.into())).into()
                        )
                        .into()
                    )
                    .into()
                ))
                .into()
            )
            .into()
        ))
    )
}

#[test]
fn basic_expr() {
    let mut lexer = Lexer::new();
    let src = "    82 * 99 / 18";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Factor(
            Expr::Factor(
                Expr::Primary(Primary::Number(82.0.into())).into(),
                FactorOp::Mul,
                Expr::Primary(Primary::Number(99.0.into())).into()
            )
            .into(),
            FactorOp::Div,
            Expr::Primary(Primary::Number(18.0.into())).into()
        )
        .into()
    )
}

#[test]
fn nested_expr_pretty_basic_still_with_comments() {
    let mut lexer = Lexer::new();
    let src = "// comment is ignored\n(77 * -74 / (87 * 99))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Primary(
            Primary::Group(
                Expr::Factor(
                    Expr::Factor(
                        Expr::Primary(Primary::Number(77.0.into())).into(),
                        FactorOp::Mul,
                        Expr::Unary(
                            UnaryOp::Neg,
                            Expr::Primary(Primary::Number(74.0.into())).into()
                        )
                        .into()
                    )
                    .into(),
                    FactorOp::Div,
                    Expr::Primary(
                        Primary::Group(
                            Expr::Factor(
                                Expr::Primary(Primary::Number(87.0.into())).into(),
                                FactorOp::Mul,
                                Expr::Primary(Primary::Number(99.0.into())).into()
                            )
                            .into()
                        )
                        .into()
                    )
                    .into()
                )
                .into()
            )
            .into()
        )
    )
}

#[test]
fn basic_cmps_with_groups() {
    let mut lexer = Lexer::new();
    let src = "(94 != 25) == ((-39 + 86) >= (72 * 19))";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let parser = Parser::new(lexer.tokens());
    let ast = parser.parse().unwrap();

    assert_eq!(
        ast,
        Expr::Equality(
            Expr::Primary(Primary::Group(
                Expr::Equality(
                    Expr::Primary(Primary::Number(94.0.into()).into()).into(),
                    EqOp::Neq,
                    Expr::Primary(Primary::Number(25.0.into()).into()).into()
                )
                .into()
            ))
            .into(),
            EqOp::Eq,
            Expr::Primary(Primary::Group(
                Expr::Cmp(
                    Expr::Primary(
                        Primary::Group(
                            Expr::Term(
                                Expr::Unary(
                                    UnaryOp::Neg,
                                    Expr::Primary(Primary::Number(39.0.into())).into()
                                )
                                .into(),
                                TermOp::Add,
                                Expr::Primary(Primary::Number(86.0.into())).into()
                            )
                            .into()
                        )
                        .into()
                    )
                    .into(),
                    CmpOp::Gte,
                    Expr::Primary(Primary::Group(
                        Expr::Factor(
                            Expr::Primary(Primary::Number(72.0.into())).into(),
                            FactorOp::Mul,
                            Expr::Primary(Primary::Number(19.0.into())).into()
                        )
                        .into()
                    ))
                    .into()
                )
                .into()
            ))
            .into()
        )
    )
}
