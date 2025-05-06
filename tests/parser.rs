use codecrafters_interpreter::{
    lexer::Lexer,
    parser::{Ast, Parser},
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
