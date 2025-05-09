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
    Equality(Box<Self>, EqOp, Box<Self>),
    Cmp(Box<Self>, CmpOp, Box<Self>),
    Term(Box<Self>, TermOp, Box<Self>),
    Factor(Box<Self>, FactorOp, Box<Self>),
    Unary(UnaryOp, Box<Self>),
    Primary(Primary<'src>),
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equality(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Cmp(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Term(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Factor(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Unary(op, i) => write!(f, "({op} {i})"),
            Self::Primary(primary) => primary.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Ast<'src> {
    Expr(Expr<'src>),
}

#[derive(Debug)]
pub enum Expected<'src> {
    Expr,
    Token(Token<'src>),
}

impl Display for Expected<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let i = match self {
            Self::Expr => "expression".into(),
            Self::Token(t) => format!("{}", t.token_type()),
        };

        write!(f, "Expect {i}.")
    }
}

#[derive(Debug)]
pub enum ErrorKind<'src> {
    Expected(Expected<'src>),
}

impl Display for ErrorKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expected(e) => e.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct Error<'src> {
    line: usize,
    token: Option<Token<'src>>,
    kind: ErrorKind<'src>,
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[line {}] Error at '{}': {}",
            self.line + 1,
            if let Some(t) = self.token {
                format!("{}", t.lexeme())
            } else {
                "".to_string()
            },
            self.kind
        )
    }
}

impl<'src> std::error::Error for Error<'src> {}

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;
type AcceptToken<'src> = Option<Token<'src>>;
type AcceptSymbol<'src> = Option<Symbol<Token<'src>>>;
type ParseExpr<'src> = Result<'src, Expr<'src>>;

trait ParserExpectedExt<'src, T> {
    fn expected(self, expected: Expected<'src>, parser: &Parser<'src>) -> Result<'src, T>;
}

impl<'src> ParserExpectedExt<'src, Symbol<Token<'src>>> for Option<Symbol<Token<'src>>> {
    fn expected(
        self,
        expected: Expected<'src>,
        parser: &Parser<'src>,
    ) -> Result<'src, Symbol<Token<'src>>> {
        if let Some(i) = self {
            Ok(i)
        } else {
            Err(Error {
                line: parser.line(),
                token: None,
                kind: ErrorKind::Expected(expected),
            })
        }
    }
}

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

    fn line(&self) -> usize {
        self.peek_symbol()
            .or(self.tokens.last().copied())
            .map(|t| t.line())
            .unwrap_or(0)
    }

    fn get_symbol(&self, idx: usize) -> AcceptSymbol<'src> {
        self.tokens.get(idx).copied()
    }

    fn peek_symbol(&self) -> AcceptSymbol<'src> {
        self.get_symbol(self.idx.get())
    }

    fn get_token(&self, idx: usize) -> AcceptToken<'src> {
        self.get_symbol(idx).map(|s| s.token())
    }

    fn peek(&self) -> AcceptToken<'src> {
        // std::thread::sleep(std::time::Duration::from_millis(100));
        eprintln!("peek {:?}", self.get_token(self.idx.get()));
        self.get_token(self.idx.get())
    }

    fn next(&self) -> AcceptToken<'src> {
        // std::thread::sleep(std::time::Duration::from_millis(100));
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

    fn expect(&self, token: Token<'src>) -> Result<'src, Token<'src>> {
        match self.peek() {
            Some(next) if next == token => {
                self.next().unwrap();
                Ok(next)
            }
            got => Err(Error {
                line: self.line(),
                token: got,
                kind: ErrorKind::Expected(Expected::Token(token)),
            }),
        }
    }

    /// Parses the program
    pub fn parse(&self) -> ParseExpr<'src> {
        self.parse_expr()
    }

    fn parse_expr(&self) -> ParseExpr<'src> {
        self.parse_eq()
    }

    fn parse_eq(&self) -> ParseExpr<'src> {
        let mut a = self.parse_cmp()?;

        eprintln!("accepting eq {a}");

        while let Some(Token::EqualEqual | Token::BangEqual) = self.peek() {
            let op = match self.next().unwrap() {
                Token::EqualEqual => EqOp::Eq,
                Token::BangEqual => EqOp::Neq,
                other => unreachable!("{other}"),
            };
            let b = self.parse_cmp()?;
            eprintln!("accepted eq {a} {op:?} {b}");
            a = Expr::Equality(a.into(), op, b.into())
        }

        Ok(a)
    }

    fn parse_cmp(&self) -> ParseExpr<'src> {
        let mut a = self.parse_term()?;

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
            let b = self.parse_term()?;
            eprintln!("accepted cmp {a} {op:?} {b}");
            a = Expr::Cmp(a.into(), op, b.into());
        }

        Ok(a)
    }

    fn parse_term(&self) -> ParseExpr<'src> {
        let mut a = self.parse_factor()?;
        eprintln!("accepting term {a}");

        while let Some(Token::Plus | Token::Minus) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Plus => TermOp::Add,
                Token::Minus => TermOp::Sub,
                other => unreachable!("{other}"),
            };
            let b = self.parse_factor()?;
            eprintln!("accepted term {a} {op:?} {b}");
            a = Expr::Term(a.into(), op, b.into());
        }

        Ok(a)
    }

    fn parse_factor(&self) -> ParseExpr<'src> {
        let mut a = self.parse_unary()?;

        eprintln!("accepting factor {a}");

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Slash => FactorOp::Div,
                Token::Star => FactorOp::Mul,
                other => unreachable!("{other}"),
            };
            let b = self.parse_unary()?;
            eprintln!("accepted factor {a} {op:?} {b}");
            a = Expr::Factor(a.into(), op, b.into())
        }

        Ok(a)
    }

    /// Accepts a unary expression
    fn parse_unary(&self) -> ParseExpr<'src> {
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

            Ok(Expr::Unary(op, self.parse_unary()?.into()))
        } else {
            eprintln!("not unary");
            self.parse_primary()
        }
    }

    /// Accepts a group
    fn parse_group(&self) -> ParseExpr<'src> {
        self.expect(Token::LeftParen)?;

        eprintln!("accepting group");

        let inner = self.parse_expr()?;

        self.expect(Token::RightParen)?;

        eprintln!("accepting group DONE");

        Ok(Expr::Primary(Primary::Group(inner.into())))
    }

    /// Accepts a primary
    fn parse_primary(&self) -> ParseExpr<'src> {
        let next = self.peek_symbol().expected(Expected::Expr, self)?.token();
        eprintln!("accepting primary {next}");

        let ast = match next {
            Token::Number(n, _) => Primary::Number(n),
            Token::String(s) => Primary::String(s),
            Token::Keyword(Keyword::True) => Primary::Bool(true),
            Token::Keyword(Keyword::False) => Primary::Bool(false),
            Token::Keyword(Keyword::Nil) => Primary::Nil,
            _ => return self.parse_group(),
        };

        self.next().unwrap();
        eprintln!("accepted primary {ast}");

        Ok(Expr::Primary(ast))
    }
}
