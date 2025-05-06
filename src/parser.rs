use std::{cell::Cell, fmt::Display};

use crate::{
    lexer::{Keyword, Symbol, Token},
    util::Number,
};

#[derive(Debug, PartialEq)]
pub enum Ast<'src> {
    Bool(bool),
    Nil,
    Number(Number),
    String(&'src str),
    Group(Vec<Ast<'src>>),
}

impl Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(bool) => f.write_str(&bool.to_string()),
            Self::Nil => f.write_str("nil"),
            Self::Number(n) => n.fmt(f),
            Self::String(s) => s.fmt(f),
            Self::Group(g) => write!(
                f,
                "(group {})",
                g.into_iter()
                    .map(|m| format!("{m}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

#[derive(Debug)]
pub enum Error<'src> {
    InvalidToken(Symbol<Token<'src>>),
    Expected(&'static str),
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parser error")
    }
}

impl<'src> std::error::Error for Error<'src> {}

pub type Result<'src, T = Ast<'src>> = std::result::Result<T, Error<'src>>;

///
/// Grammar
///
///     let program = "value*";
/// 
///     let group = "( value* )";
///
///     let value = "bool | nil | number | string | group";
///
pub struct Parser<'src> {
    tokens: &'src [Symbol<Token<'src>>],
    idx: Cell<usize>,
}

impl<'src> Parser<'src> {
    pub fn new(tokens: &'src [Symbol<Token<'src>>]) -> Self {
        Self {
            tokens,
            idx: 0.into(),
        }
    }

    fn peek(&self) -> Option<&Symbol<Token<'src>>> {
        self.tokens.get(self.idx.get())
    }

    fn next(&self) -> Option<Symbol<Token<'src>>> {
        let token = self.tokens.get(self.idx.get()).copied();
        self.idx.set(self.idx.get() + 1);

        token
    }

    fn accept(&self, token: Token<'src>) -> Option<Symbol<Token<'src>>> {
        eprintln!("accepting {token}");
        if let Some(next) = self.peek() {
            eprintln!("next token is {}", next.token());
            if next.token() == token {
                eprintln!("accepted");
                return Some(self.next().unwrap());
            }
        };

        eprintln!("not accepted");

        None
    }

    /// Accepts a value
    ///
    ///     let value = "bool | nil | number | string | group";
    fn accept_value(&self) -> Option<Ast<'src>> {
        let next = self.peek()?;

        let ast = match next.token() {
            Token::Keyword(Keyword::True) => Ast::Bool(true),
            Token::Keyword(Keyword::False) => Ast::Bool(false),
            Token::Keyword(Keyword::Nil) => Ast::Nil,
            Token::Number(n, _) => Ast::Number(n),
            Token::String(s) => Ast::String(s),
            _ => return self.accept_group(),
        };

        self.next().unwrap();

        Some(ast)
    }

    fn parse_value(&self) -> Result<'src> {
        self.accept_value().ok_or(Error::Expected("value"))
    }

    /// Accepts a
    ///
    ///     let group = "( value* )";
    fn accept_group(&self) -> Option<Ast<'src>> {
        eprintln!("parsing group");
        self.accept(Token::LeftParen)?;

        let mut members = Vec::new();

        loop {
            match self.accept_value() {
                Some(m) => members.push(m),
                None => break,
            }
        }

        self.accept(Token::RightParen)?;

        Some(Ast::Group(members))
    }

    fn _parse_group(&self) -> Result<'src> {
        self.accept_group().ok_or(Error::Expected("group"))
    }

    /// Parser the program, ie.
    /// 
    ///     let program = "value*";
    pub fn parse(&self) -> Vec<Ast<'src>> {
        let mut program = Vec::new();

        while let Ok(g) = self.parse_value() {
            program.push(g);
        }

        program
    }
}
