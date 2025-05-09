use std::{cell::Cell, fmt::Display};

use crate::{
    lexer::{Keyword, Symbol, Token},
    util::Number,
};

macro_rules! impl_op_display {
    ($name:path, $($op:path=>$d:literal,)*) => {
        impl Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{}",
                    match self {
                        $($op=>$d,)*
                    }
                )
            }
        }
    };
}

#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Not,
    Neg,
}

impl_op_display! {
    UnaryOp,
    UnaryOp::Not => "!",
    UnaryOp::Neg => "-",
}

#[derive(Debug, PartialEq)]
pub enum FactorOp {
    Div,
    Mul,
}

impl_op_display! {
    FactorOp,
    FactorOp::Div => "/",
    FactorOp::Mul => "*",
}

#[derive(Debug, PartialEq)]
pub enum TermOp {
    Add,
    Sub,
}

impl_op_display! {
    TermOp,
    TermOp::Add => "+",
    TermOp::Sub => "-",
}

#[derive(Debug, PartialEq)]
pub enum CmpOp {
    Gt,
    Gte,
    Lt,
    Lte,
}

impl_op_display! {
    CmpOp,
    Self::Gt => ">",
    Self::Gte => ">=",
    Self::Lt => "<",
    Self::Lte => "<=",
}

#[derive(Debug, PartialEq)]
pub enum EqOp {
    Eq,
    Neq,
}

impl_op_display! {
    EqOp,
    EqOp::Eq => "==",
    EqOp::Neq => "!=",
}

macro_rules! impl_ast_display {
    ($name:ident) => {
        impl Display for $name<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut d = format!("{}", self.0);

                for (op, n) in &self.1 {
                    d = format!("({op} {d} {n})")
                }

                f.write_str(&d)
            }
        }
    };
}

macro_rules! impl_ast_utils {
    ($name:ident, $op:ident, $child:ident) => {
        impl<'src> $name<'src> {
            pub fn new(child: $child<'src>) -> Self {
                Self(child, Vec::new())
            }

            pub fn extend(mut self, op: $op, member: $child<'src>) -> Self {
                self.1.push((op, member));
                self
            }
        }
    };
}

#[derive(Debug, PartialEq)]
pub struct Equality<'src>(Cmp<'src>, Vec<(EqOp, Cmp<'src>)>);
impl_ast_display!(Equality);
impl_ast_utils! {Equality, EqOp, Cmp}

#[derive(Debug, PartialEq)]
pub struct Cmp<'src>(Term<'src>, Vec<(CmpOp, Term<'src>)>);
impl_ast_display!(Cmp);
impl_ast_utils! {Cmp, CmpOp, Term}

#[derive(Debug, PartialEq)]
pub struct Term<'src>(Factor<'src>, Vec<(TermOp, Factor<'src>)>);
impl_ast_display!(Term);
impl_ast_utils! {Term, TermOp, Factor}

#[derive(Debug, PartialEq)]
pub struct Factor<'src>(Unary<'src>, Vec<(FactorOp, Unary<'src>)>);
impl_ast_display!(Factor);
impl_ast_utils! {Factor, FactorOp, Unary}

#[derive(Debug, PartialEq)]
pub enum Unary<'src> {
    Unary(UnaryOp, Box<Unary<'src>>),
    Primary(Primary<'src>),
}

impl<'src> Unary<'src> {
    pub fn unary(op: UnaryOp, inner: Self) -> Self {
        Self::Unary(op, inner.into())
    }

    pub fn primary(primary: Primary<'src>) -> Self {
        Self::Primary(primary)
    }
}

impl Display for Unary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unary(op, i) => write!(f, "({op} {i}"),
            Self::Primary(i) => write!(f, "{i}"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Primary<'src> {
    Bool(bool),
    Nil,
    Number(Number),
    String(&'src str),
    Group(Box<Expr<'src>>),
}

impl<'src> Primary<'src> {
    pub fn bool(bool: bool) -> Self {
        Self::Bool(bool)
    }

    pub fn nil() -> Self {
        Self::Nil
    }

    pub fn number(num: f64) -> Self {
        Self::Number(num.into())
    }

    pub fn string(s: &'src str) -> Self {
        Self::String(s)
    }

    pub fn group(expr: Expr<'src>) -> Self {
        Self::Group(expr.into())
    }
}

impl Display for Primary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(bool) => f.write_str(&bool.to_string()),
            Self::Nil => f.write_str("nil"),
            Self::Number(n) => n.fmt(f),
            Self::String(s) => s.fmt(f),
            Self::Group(g) => write!(f, "(group {g})",),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expr<'src> {
    Equality(Equality<'src>),
    Cmp(Cmp<'src>),
    Term(Term<'src>),
    Factor(Factor<'src>),
    Unary(Unary<'src>),
    Primary(Primary<'src>),
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equality(i) => i.fmt(f),
            Self::Cmp(i) => i.fmt(f),
            Self::Term(i) => i.fmt(f),
            Self::Factor(i) => i.fmt(f),
            Self::Unary(i) => i.fmt(f),
            Self::Primary(i) => i.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Ast<'src> {
    Expr(Expr<'src>),
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

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;
type AcceptToken<'src> = Option<Token<'src>>;

/// Parses the lox programming language using a recursive descent approach based on Lox's grammar rules
///
/// See https://craftinginterpreters.com/parsing-expressions.html#ambiguity-and-the-parsing-game
///
/// expression     → equality ;
///
/// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
///
/// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
///
/// term           → factor ( ( "-" | "+" ) factor )* ;
///
/// factor         → unary ( ( "/" | "*" ) unary )* ;
///
/// unary          → ( "!" | "-" ) unary
///                | primary ;
///
/// primary        → NUMBER | STRING | "true" | "false" | "nil"
///                | "(" expression ")"
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
    pub fn parse(&self) -> Vec<Expr<'src>> {
        let mut program = Vec::new();

        while let Some(a) = self.accept_expr() {
            program.push(a);
        }

        program
    }

    fn accept_expr(&self) -> Option<Expr<'src>> {
        Some(Expr(self.accept_eq()?))
    }

    fn accept_eq(&self) -> Option<Equality<'src>> {
        let mut a = Equality::new(self.accept_cmp()?);
        eprintln!("accepting eq {a}");

        while let Some(Token::EqualEqual | Token::BangEqual) = self.peek() {
            let op = match self.next().unwrap() {
                Token::EqualEqual => EqOp::Eq,
                Token::BangEqual => EqOp::Neq,
                other => unreachable!("{other}"),
            };
            let b = self.accept_cmp()?;
            eprintln!("accepted eq {a} {op:?} {b}");
            a = a.extend(op, b)
        }

        Some(a)
    }

    fn accept_cmp(&self) -> Option<Cmp<'src>> {
        let mut a = Cmp::new(self.accept_term()?);
        eprintln!("accepting cmp {a}");

        while let Some(Token::Greater | Token::GreaterEqual | Token::Less | Token::LessEqual) =
            self.peek()
        {
            let op = match self.next().unwrap() {
                Token::Greater => CmpOp::Gt,
                Token::GreaterEqual => CmpOp::Gte,
                Token::Less => CmpOp::Lt,
                Token::LessEqual => CmpOp::Lte,
                other => unreachable!("{other}"),
            };
            let b = self.accept_term()?;
            eprintln!("accepted cmp {a} {op:?} {b}");
            a = a.extend(op, b);
        }

        Some(a)
    }

    fn accept_term(&self) -> Option<Term<'src>> {
        let mut a = Term::new(self.accept_factor()?);
        eprintln!("accepting term {a}");

        while let Some(Token::Plus | Token::Minus) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Plus => TermOp::Add,
                Token::Minus => TermOp::Sub,
                other => unreachable!("{other}"),
            };
            let b = self.accept_factor()?;
            eprintln!("accepted term {a} {op:?} {b}");
            a = a.extend(op, b);
        }

        Some(a)
    }

    fn accept_factor(&self) -> Option<Factor<'src>> {
        let mut a = Factor::new(self.accept_unary()?);
        eprintln!("accepting factor {a}");

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Slash => FactorOp::Div,
                Token::Star => FactorOp::Mul,
                other => unreachable!("{other}"),
            };
            let b = self.accept_unary()?;
            eprintln!("accepted factor {a} {op:?} {b}");
            a = a.extend(op, b);
        }

        Some(a)
    }

    /// Accepts a unary expression
    fn accept_unary(&self) -> Option<Unary<'src>> {
        let unary = self
            .accept(Token::Bang)
            .or_else(|| self.accept(Token::Minus));

        eprintln!("accepting unary {unary:?}");

        if let Some(unary) = unary {
            let op = match unary {
                Token::Bang => UnaryOp::Not,
                Token::Minus => UnaryOp::Neg,
                other => unreachable!("{other}"),
            };

            eprintln!("accepted unary {op} {unary}");

            Some(Unary::Unary(op, self.accept_unary()?.into()))
        } else {
            eprintln!("not unary");
            Some(Unary::Primary(self.accept_primary()?))
        }
    }

    /// Accepts a group
    fn accept_group(&self) -> Option<Expr<'src>> {
        self.accept(Token::LeftParen)?;

        eprintln!("accepting group");

        let inner = self.accept_expr()?;

        self.accept(Token::RightParen)?;

        eprintln!("accepting group DONE");

        Some(inner)
    }

    /// Accepts a primary
    fn accept_primary(&self) -> Option<Primary<'src>> {
        let next = self.peek()?;
        eprintln!("accepting primary {next}");

        let ast = match next {
            Token::Number(n, _) => Primary::Number(n),
            Token::String(s) => Primary::String(s),
            Token::Keyword(Keyword::True) => Primary::Bool(true),
            Token::Keyword(Keyword::False) => Primary::Bool(false),
            Token::Keyword(Keyword::Nil) => Primary::Nil,
            _ => Primary::Group(self.accept_group()?.into()),
        };

        eprintln!("accepted primary {ast}");

        self.next().unwrap();

        Some(ast)
    }
}
