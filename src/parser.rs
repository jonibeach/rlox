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

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Not => "!",
                Self::Neg => "-",
            }
        )
    }
}

#[derive(Debug, PartialEq)]
pub enum BinOp {
    Div,
    Mul,
    Add,
    Sub,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Div => "/",
                Self::Mul => "*",
                Self::Add => "+",
                Self::Sub => "-",
            }
        )
    }
}

#[derive(Debug, PartialEq)]
pub enum CmpOp {
    Gt,
    Gte,
    Lt,
    Lte,
    Eq,
    Neq,
}

impl Display for CmpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Gt => ">",
                Self::Gte => ">=",
                Self::Lt => "<",
                Self::Lte => "<=",
                Self::Eq => "==",
                Self::Neq => "!=",
            }
        )
    }
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
    CmpOp(Box<Self>, CmpOp, Box<Self>),
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
            Self::UnaryOp(unary_op, n) => write!(f, "({unary_op} {n})",),
            Self::BinOp(a, bin_op, b) => write!(f, "({bin_op} {a} {b})",),
            Self::CmpOp(a, cmp_op, b) => write!(f, "({cmp_op} {a} {b})"),
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
type AcceptToken<'src> = Option<Token<'src>>;
type AcceptAst<'src> = Option<Ast<'src>>;

/// Parses the lox programming language using a recursive descent approach based on the following grammar rules
///     let program = "term*";
///
///     let cmp = "term ((>|>=|<|<=|==|!=) term)*";
///
///     let term = "factor ((+|-) factor)*";
///
///     let factor = "unary ((*|/) unary)*";
///
///     let unary = "(!|-)? (unary | atom)";
///
///     let group = "( cmp* )";
///
///     let atom =  "number | string | true | false | nil | group | cmp";
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

    fn get_token(&self, idx: usize) -> AcceptToken<'src> {
        self.tokens.get(idx).map(|t| t.token())
    }

    fn peek(&self) -> AcceptToken<'src> {
        self.get_token(self.idx.get())
    }

    fn next(&self) -> AcceptToken<'src> {
        let token = self.get_token(self.idx.get());
        self.idx.set(self.idx.get() + 1);

        token
    }

    fn accept(&self, token: Token<'src>) -> AcceptToken<'src> {
        if let Some(next) = self.peek() {
            if next == token {
                return Some(self.next().unwrap());
            }
        };

        None
    }

    /// Parses the program
    ///     let program = "term*";
    pub fn parse(&self) -> Vec<Ast<'src>> {
        let mut program = Vec::new();

        while let Some(a) = self.accept_cmp() {
            program.push(a);
        }

        program
    }

    fn accept_cmp(&self) -> AcceptAst<'src> {
        let mut a = self.accept_term()?;
        eprintln!("accepting cmp {a}");

        while let Some(
            Token::Greater
            | Token::GreaterEqual
            | Token::Less
            | Token::LessEqual
            | Token::EqualEqual
            | Token::BangEqual,
        ) = self.peek()
        {
            let cmp_op = match self.next().unwrap() {
                Token::Greater => CmpOp::Gt,
                Token::GreaterEqual => CmpOp::Gte,
                Token::Less => CmpOp::Lt,
                Token::LessEqual => CmpOp::Lte,
                Token::EqualEqual => CmpOp::Eq,
                Token::BangEqual => CmpOp::Neq,
                other => unreachable!("{other}"),
            };
            let b = self.accept_term()?;
            eprintln!("accepted add/sub expr {a} {cmp_op:?} {b}");
            a = Ast::CmpOp(a.into(), cmp_op, b.into())
        }

        Some(a)
    }

    fn accept_term(&self) -> AcceptAst<'src> {
        let mut a = self.accept_factor()?;
        eprintln!("accepting term {a}");

        while let Some(Token::Plus | Token::Minus) = self.peek() {
            let bin_op = match self.next().unwrap() {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                other => unreachable!("{other}"),
            };
            let b = self.accept_factor()?;
            eprintln!("accepted term {a} {bin_op:?} {b}");
            a = Ast::BinOp(a.into(), bin_op, b.into())
        }

        Some(a)
    }

    fn accept_factor(&self) -> AcceptAst<'src> {
        let mut a = self.accept_unary()?;
        eprintln!("accepting factor {a}");

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let bin_op = match self.next().unwrap() {
                Token::Slash => BinOp::Div,
                Token::Star => BinOp::Mul,
                other => unreachable!("{other}"),
            };
            let b = self.accept_unary()?;
            eprintln!("accepted factor {a} {bin_op:?} {b}");
            a = Ast::BinOp(a.into(), bin_op, b.into())
        }

        Some(a)
    }

    /// Accepts a unary expression
    fn accept_unary(&self) -> AcceptAst<'src> {
        let unary = self
            .accept(Token::Bang)
            .or_else(|| self.accept(Token::Minus));

        eprintln!("accepting unary {unary:?}");

        if let Some(unary) = unary {
            let unary_op = match unary {
                Token::Bang => UnaryOp::Not,
                Token::Minus => UnaryOp::Neg,
                other => unreachable!("{other}"),
            };

            eprintln!("accepted unary {unary_op} {unary}");

            Some(Ast::UnaryOp(
                unary_op,
                self.accept_atom().or_else(|| self.accept_unary())?.into(),
            ))
        } else {
            eprintln!("not unary");
            self.accept_atom()
        }
    }

    /// Accepts a group
    fn accept_group(&self) -> AcceptAst<'src> {
        self.accept(Token::LeftParen)?;

        eprintln!("accepting group");

        let mut members = Vec::new();

        while Some(Token::RightParen) != self.peek() {
            if let Some(m) = self.accept_cmp() {
                members.push(m);
            }
        }

        self.accept(Token::RightParen)?;

        eprintln!("accepting group DONE");

        Some(Ast::Group(members))
    }

    /// Accepts an atom
    ///     let atom =  "number | string | true | false | nil | term";
    fn accept_atom(&self) -> AcceptAst<'src> {
        let next = self.peek()?;
        eprintln!("accepting atom {next}");

        let ast = match next {
            Token::Number(n, _) => Ast::Number(n),
            Token::String(s) => Ast::String(s),
            Token::Keyword(Keyword::True) => Ast::Bool(true),
            Token::Keyword(Keyword::False) => Ast::Bool(false),
            Token::Keyword(Keyword::Nil) => Ast::Nil,
            _ => return self.accept_group().or_else(|| self.accept_cmp()),
        };

        eprintln!("accepted atom {ast}");

        self.next().unwrap();

        Some(ast)
    }
}
