use std::{cell::Cell, fmt::Display};

use crate::{
    lexer::{Keyword, Symbol, Token},
    util::Number,
};

#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, PartialEq)]
pub enum BinOp {
    Div,
    Mul,
}

#[derive(Debug, PartialEq)]
pub enum Ast<'src> {
    Bool(bool),
    Nil,
    Number(Number),
    String(&'src str),
    Group(Vec<Self>),
    UnaryOp(UnaryOp, Box<Self>),
    BinOp(Box<Self>, BinOp, Box<Self>),
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
                g.iter()
                    .map(|m| format!("{m}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Self::UnaryOp(unary_op, n) => write!(
                f,
                "({} {n})",
                match unary_op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                }
            ),
            Self::BinOp(a, bin_op, b) => write!(
                f,
                "({} {a} {b})",
                match bin_op {
                    BinOp::Div => "/",
                    BinOp::Mul => "*",
                }
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

impl std::error::Error for Error<'_> {}

pub type Result<'src, T = Ast<'src>> = std::result::Result<T, Error<'src>>;

///
/// Grammar
///
///     let program = "value*";
///
///     let expr = "value (*|/) value";
///
///     let group = "( value* )";
///
///     let value = "bool | nil | number | string | group | (!|-)value | expr";
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

    fn get_token(&self, idx: usize) -> Option<Token<'src>> {
        self.tokens.get(idx).map(|t| t.token())
    }

    fn peek(&self) -> Option<Token<'src>> {
        self.get_token(self.idx.get())
    }

    fn next(&self) -> Option<Token<'src>> {
        let token = self.get_token(self.idx.get());
        self.idx.set(self.idx.get() + 1);

        token
    }

    fn accept(&self, token: Token<'src>) -> Option<Token<'src>> {
        if let Some(next) = self.peek() {
            if next == token {
                return Some(self.next().unwrap());
            }
        };

        None
    }

    /// Accepts a value
    ///
    ///     let value = "bool | nil | number | string | group | (!|*)value";
    fn accept_value(&self) -> Option<Ast<'src>> {
        let next = self.peek()?;
        // std::thread::sleep(std::time::Duration::from_millis(100));
        eprintln!("accepting value {next}");

        let ast = match next {
            Token::Keyword(Keyword::True) => Ast::Bool(true),
            Token::Keyword(Keyword::False) => Ast::Bool(false),
            Token::Keyword(Keyword::Nil) => Ast::Nil,
            Token::Number(n, _) => Ast::Number(n),
            Token::String(s) => Ast::String(s),
            _ => {
                return self
                    .accept_group()
                    .or_else(|| self.accept_unary())
                    .or_else(|| self.accept_expr())
            }
        };

        self.next().unwrap();

        Some(ast)
    }

    /// Accepts a
    ///
    ///     let group = "( value* )";
    fn accept_group(&self) -> Option<Ast<'src>> {
        self.accept(Token::LeftParen)?;

        eprintln!("accepting group");

        let mut members = Vec::new();

        while Some(Token::RightParen) != self.peek() {
            if let Some(m) = self.accept_expr() {
                members.push(m);
            }
        }

        self.accept(Token::RightParen)?;

        eprintln!("accepting group DONE");

        Some(Ast::Group(members))
    }

    /// Accepts a
    ///
    ///     let value = "(!|*)value";
    fn accept_unary(&self) -> Option<Ast<'src>> {
        let token = self
            .accept(Token::Bang)
            .or_else(|| self.accept(Token::Minus))?;
        Some(Ast::UnaryOp(
            match token {
                Token::Bang => UnaryOp::Not,
                Token::Minus => UnaryOp::Neg,
                other => unreachable!("{other}"),
            },
            self.accept_value()?.into(),
        ))
    }

    fn accept_expr(&self) -> Option<Ast<'src>> {
        let mut a = self.accept_value()?;
        eprintln!("accepting expr {a}");

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let bin_op = match self.peek() {
                Some(Token::Slash) => BinOp::Div,
                Some(Token::Star) => BinOp::Mul,
                _ => return Some(a),
            };
            self.next().unwrap();
            let b = self.accept_value()?;
            eprintln!("accepted expr {a} {bin_op:?} {b}");
            a = Ast::BinOp(a.into(), bin_op, b.into())
        }

        Some(a)
    }

    fn parse_expr(&self) -> Result<'src> {
        self.accept_expr().ok_or(Error::Expected("expr"))
    }

    /// Parser the program, ie.
    ///
    ///     let program = "value*";
    pub fn parse(&self) -> Vec<Ast<'src>> {
        let mut program = Vec::new();

        while let Ok(g) = self.parse_expr() {
            program.push(g);
        }

        program
    }
}
