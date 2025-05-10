use std::{cell::Cell, fmt::Display, marker::PhantomData};

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
pub enum ExprKind<'src> {
    Equality(Box<Expr<'src>>, EqOp, Box<Expr<'src>>),
    Cmp(Box<Expr<'src>>, CmpOp, Box<Expr<'src>>),
    Term(Box<Expr<'src>>, TermOp, Box<Expr<'src>>),
    Factor(Box<Expr<'src>>, FactorOp, Box<Expr<'src>>),
    Unary(UnaryOp, Box<Expr<'src>>),
    Primary(Primary<'src>),
}

impl Display for ExprKind<'_> {
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

pub type Expr<'src> = AstNode<'src, ExprKind<'src>>;

#[derive(Debug, PartialEq)]
pub struct AstNode<'src, T> {
    line: usize,
    kind: T,
    _p: PhantomData<&'src ()>,
}

impl<T> Display for AstNode<'_, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl<'src, T> AstNode<'src, T> {
    pub fn kind(&self) -> &T {
        &self.kind
    }

    pub fn line(&self) -> usize {
        self.line
    }
}

trait IntoAstNodeExt<'src>: Sized {
    fn into_ast(self, parser: &Parser) -> AstNode<'src, Self> {
        AstNode {
            line: parser.line(),
            kind: self,
            _p: PhantomData,
        }
    }
}

impl<'src> IntoAstNodeExt<'src> for StmtKind<'src> {}
impl<'src> IntoAstNodeExt<'src> for ExprKind<'src> {}

#[derive(Debug, PartialEq)]
pub enum StmtKind<'src> {
    Expr(Expr<'src>),
    Print(Expr<'src>),
}

impl Display for StmtKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expr(i) => i.fmt(f),
            Self::Print(i) => write!(f, "(print {i})"),
        }
    }
}

pub type Stmt<'src> = AstNode<'src, StmtKind<'src>>;

pub struct Program<'src> {
    stmts: Vec<Stmt<'src>>,
}

impl<'src> Program<'src> {
    pub fn stmts(&self) -> &[Stmt<'src>] {
        &self.stmts
    }
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
type ParseStmt<'src> = Result<'src, Stmt<'src>>;

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
/// program        → statement* EOF ;
/// statement      → exprStmt | printStmt ;
///
/// exprStmt       → expression ";" ;
/// printStmt      → "print" expression ";" ;
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
    force_ending_semicolon: bool,
}

impl<'src> Parser<'src> {
    pub fn no_ending_semicolons(tokens: &'src [Symbol<Token<'src>>]) -> Self {
        Self {
            tokens,
            idx: 0.into(),
            force_ending_semicolon: false,
        }
    }
    pub fn new(tokens: &'src [Symbol<Token<'src>>]) -> Self {
        Self {
            tokens,
            idx: 0.into(),
            force_ending_semicolon: true,
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

    pub fn parse(&self) -> Result<'src, Program<'src>> {
        let mut stmts = Vec::new();

        while self.peek().is_some() {
            stmts.push(self.parse_stmt()?);
        }

        assert_eq!(self.next(), None);

        Ok(Program { stmts })
    }

    fn parse_stmt(&self) -> ParseStmt<'src> {
        let mut is_print = false;

        eprintln!("accepting stmt");
        if let Some(Token::Keyword(Keyword::Print)) = self.peek() {
            is_print = true;
            eprintln!("is print stmt");
            self.next().unwrap();
        }

        let expr = self.parse_expr()?;

        let stmt = match is_print {
            true => StmtKind::Print(expr),
            false => StmtKind::Expr(expr),
        };

        if self.force_ending_semicolon {
            self.expect(Token::Semicolon)?;
        }

        eprintln!("accepted stmt {stmt}");

        Ok(stmt.into_ast(self))
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
            a = ExprKind::Equality(a.into(), op, b.into()).into_ast(self);
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
            a = ExprKind::Cmp(a.into(), op, b.into()).into_ast(self);
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
            a = ExprKind::Term(a.into(), op, b.into()).into_ast(self);
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
            a = ExprKind::Factor(a.into(), op, b.into()).into_ast(self)
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

            Ok(ExprKind::Unary(op, self.parse_unary()?.into()).into_ast(self))
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

        Ok(ExprKind::Primary(Primary::Group(inner.into())).into_ast(self))
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

        Ok(ExprKind::Primary(ast).into_ast(self))
    }
}
