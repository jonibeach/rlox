use std::fmt::Display;

use crate::{
    lexer::{Keyword, Symbol, Token},
    util::Number,
};

pub enum Ast<'src> {
    Bool(bool),
    Nil,
    Number(Number),
    String(&'src str),
}

impl Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(bool) => f.write_str(&bool.to_string()),
            Self::Nil => f.write_str("nil"),
            Self::Number(n) => n.fmt(f),
            Self::String(s) => s.fmt(f),
        }
    }
}

pub struct Parser;

impl Parser {
    pub fn new() -> Self {
        Self
    }

    pub fn parse<'src>(
        &mut self,
        tokens: impl IntoIterator<Item = &'src Symbol<Token<'src>>>,
    ) -> Vec<Ast<'src>> {
        let mut ast = Vec::new();

        for t in tokens {
            let ast_node = match t.token() {
                Token::Keyword(Keyword::True) => Ast::Bool(true),
                Token::Keyword(Keyword::False) => Ast::Bool(false),
                Token::Keyword(Keyword::Nil) => Ast::Nil,
                Token::Number(n, _) => Ast::Number(n),
                Token::String(s) => Ast::String(s),
                _ => unimplemented!(),
            };

            ast.push(ast_node);
        }

        ast
    }
}
