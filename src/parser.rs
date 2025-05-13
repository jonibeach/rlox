use std::{borrow::Cow, cell::Cell, fmt::Display};

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

#[derive(Debug, PartialEq, Clone)]
pub enum Primary<'src> {
    Bool(bool),
    Nil,
    Number(Number),
    String(Cow<'src, str>),
}

impl Display for Primary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(bool) => f.write_str(&bool.to_string()),
            Self::Nil => f.write_str("nil"),
            Self::Number(n) => n.fmt(f),
            Self::String(s) => s.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstKind<'src> {
    Block(Vec<AstNode<'src>>),
    VarAssign(&'src str, Box<AstNode<'src>>),
    VarDecl(&'src str, Box<AstNode<'src>>),
    Print(Box<AstNode<'src>>),
    Equality(Box<AstNode<'src>>, EqOp, Box<AstNode<'src>>),
    Cmp(Box<AstNode<'src>>, CmpOp, Box<AstNode<'src>>),
    Term(Box<AstNode<'src>>, TermOp, Box<AstNode<'src>>),
    Factor(Box<AstNode<'src>>, FactorOp, Box<AstNode<'src>>),
    Unary(UnaryOp, Box<AstNode<'src>>),
    Group(Box<AstNode<'src>>),
    VariableAccess(&'src str),
    Primary(Primary<'src>),
}

impl<'src> AstKind<'src> {
    fn into_ast(self, parser: &Parser) -> AstNode<'src> {
        AstNode {
            line: parser.line(),
            kind: self,
        }
    }
}

impl Display for AstKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Block(inners) => {
                write!(f, "(block")?;

                for i in inners {
                    write!(f, " {i}")?
                }

                write!(f, ")")
            }
            Self::VarAssign(ident, val) => write!(f, "(varAssign {ident} {val})"),
            Self::VarDecl(ident, val) => write!(f, "(varDecl {ident} {val})"),
            Self::Print(i) => write!(f, "(print {i})"),
            Self::Equality(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Cmp(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Term(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Factor(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Unary(op, i) => write!(f, "({op} {i})"),
            Self::Group(g) => write!(f, "(group {g})",),
            Self::VariableAccess(ident) => write!(f, "(varAccess {ident})"),
            Self::Primary(primary) => primary.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct AstNode<'src> {
    line: usize,
    kind: AstKind<'src>,
}

impl Display for AstNode<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl<'src> AstNode<'src> {
    pub fn kind(&self) -> &AstKind<'src> {
        &self.kind
    }

    pub fn line(&self) -> usize {
        self.line
    }
}

#[derive(Debug)]
pub struct Program<'src> {
    blocks: Vec<AstNode<'src>>,
}

impl<'src> Program<'src> {
    pub fn blocks(&self) -> &[AstNode<'src>] {
        &self.blocks
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
            Self::Token(t) => format!("'{}'", t.lexeme()),
        };

        write!(f, "Expect {i} .")
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

impl<'src> Error<'src> {
    pub fn new(line: usize, token: Option<Token<'src>>, kind: ErrorKind<'src>) -> Self {
        Self { line, token, kind }
    }
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[line {}] Error at {}: {}",
            self.line + 1,
            if let Some(t) = self.token {
                format!("'{}'", t.lexeme())
            } else {
                "end".into()
            },
            self.kind
        )
    }
}

impl std::error::Error for Error<'_> {}

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;
type AcceptToken<'src> = Option<Token<'src>>;
type AcceptSymbol<'src> = Option<Symbol<Token<'src>>>;
type ParseResult<'src> = Result<'src, AstNode<'src>>;

/// Parses the lox programming language using a recursive descent approach based on Lox's grammar rules
///
/// See https://craftinginterpreters.com/parsing-expressions.html#ambiguity-and-the-parsing-game
///
/// program        → ( block | declaration )* EOF ;
///
/// block          → "{"  declaration*  "}";
///
/// declaration    → varDecl | statement | block;
///
/// varDecl        → "var" IDENTIFIER ( "=" expression )? ";" ;
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
///                | "(" expression ")" | IDENTIFIER "=" expression
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
        eprintln!("peek {:?}", self.get_token(self.idx.get()));
        self.get_token(self.idx.get())
    }

    fn next(&self) -> AcceptToken<'src> {
        let token = self.get_token(self.idx.get());

        if token.is_some() {
            self.idx.set(self.idx.get() + 1);
        }

        token
    }

    fn prev(&self) -> AcceptToken<'src> {
        self.idx.set(self.idx.get() - 1);
        self.get_token(self.idx.get())
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

    fn err(&self, expected: Expected<'src>) -> ParseResult<'src> {
        Err(Error {
            line: self.line(),
            token: None,
            kind: ErrorKind::Expected(expected),
        })
    }

    fn err_expected_token(&self, token: Token<'src>) -> ParseResult<'src> {
        self.err(Expected::Token(token))
    }

    pub fn parse(&self) -> Result<'src, Program<'src>> {
        let mut blocks = Vec::new();

        while let Some(t) = self.peek() {
            let b = match t {
                Token::RightBrace => self.parse_block()?,
                _ => self.parse_decl()?,
            };

            blocks.push(b);
        }

        assert_eq!(self.next(), None);

        Ok(Program { blocks })
    }

    fn parse_block(&self) -> ParseResult<'src> {
        self.expect(Token::LeftBrace)?;

        eprintln!("parsing block");

        let mut decls = Vec::new();

        while !matches!(self.peek(), Some(Token::RightBrace) | None) {
            eprintln!("\nPARSING_BLOCK_MEMBER\n");
            let decl = self.parse_decl()?;
            eprintln!("\nPARSED BLOCK MEMBER: {decl}\n");
            decls.push(decl);
        }

        eprintln!("end of block or file");

        self.expect(Token::RightBrace)?;

        Ok(AstKind::Block(decls).into_ast(self))
    }

    fn parse_decl(&self) -> ParseResult<'src> {
        self.parse_var_decl()
            .or_else(|_| self.parse_stmt())
            .or_else(|_| self.parse_block())
    }

    fn parse_var_decl(&self) -> ParseResult<'src> {
        eprintln!("parsing var decl");

        self.expect(Token::Keyword(Keyword::Var))?;

        let Some(Token::Identifier(ident)) = self.peek() else {
            return self.err_expected_token(Token::Identifier("ANY_IDENT"));
        };

        self.next().unwrap();

        let var_decl = match self.peek() {
            Some(Token::Semicolon) => {
                self.next().unwrap();
                AstKind::VarDecl(ident, AstKind::Primary(Primary::Nil).into_ast(self).into())
            }
            Some(Token::Equal) => {
                self.next().unwrap();
                let value = self.parse_expr()?;
                self.expect(Token::Semicolon)?;

                eprintln!("got decl with value {value}");

                AstKind::VarDecl(ident, value.into())
            }
            _ => return self.err_expected_token(Token::Semicolon),
        };

        Ok(var_decl.into_ast(self))
    }

    fn parse_stmt(&self) -> ParseResult<'src> {
        let mut is_print = false;

        eprintln!("parsing stmt");
        if let Some(Token::Keyword(Keyword::Print)) = self.peek() {
            is_print = true;
            eprintln!("is print stmt");
            self.next().unwrap();
        }

        let expr = self.parse_expr()?;

        let stmt = match is_print {
            true => AstKind::Print(expr.into()),
            false => expr.kind,
        };

        if self.force_ending_semicolon {
            self.expect(Token::Semicolon)?;
        }

        eprintln!("accepted stmt {stmt}");

        Ok(stmt.into_ast(self))
    }

    fn parse_expr(&self) -> ParseResult<'src> {
        self.parse_eq()
    }

    fn parse_eq(&self) -> ParseResult<'src> {
        let mut a = self.parse_cmp()?;

        eprintln!("parsing eq {a}");

        while let Some(Token::EqualEqual | Token::BangEqual) = self.peek() {
            let op = match self.next().unwrap() {
                Token::EqualEqual => EqOp::Eq,
                Token::BangEqual => EqOp::Neq,
                other => unreachable!("{other}"),
            };
            let b = self.parse_cmp()?;
            eprintln!("accepted eq {a} {op:?} {b}");
            a = AstKind::Equality(a.into(), op, b.into()).into_ast(self);
        }

        Ok(a)
    }

    fn parse_cmp(&self) -> ParseResult<'src> {
        let mut a = self.parse_term()?;

        eprintln!("parsing cmp {a}");

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
            a = AstKind::Cmp(a.into(), op, b.into()).into_ast(self);
        }

        Ok(a)
    }

    fn parse_term(&self) -> ParseResult<'src> {
        let mut a = self.parse_factor()?;
        eprintln!("parsing term {a}");

        while let Some(Token::Plus | Token::Minus) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Plus => TermOp::Add,
                Token::Minus => TermOp::Sub,
                other => unreachable!("{other}"),
            };
            let b = self.parse_factor()?;
            eprintln!("accepted term {a} {op:?} {b}");
            a = AstKind::Term(a.into(), op, b.into()).into_ast(self);
        }

        Ok(a)
    }

    fn parse_factor(&self) -> ParseResult<'src> {
        let mut a = self.parse_unary()?;

        eprintln!("parsing factor {a}");

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Slash => FactorOp::Div,
                Token::Star => FactorOp::Mul,
                other => unreachable!("{other}"),
            };
            let b = self.parse_unary()?;
            eprintln!("accepted factor {a} {op:?} {b}");
            a = AstKind::Factor(a.into(), op, b.into()).into_ast(self)
        }

        Ok(a)
    }

    /// Accepts a unary expression
    fn parse_unary(&self) -> ParseResult<'src> {
        let unary = self
            .accept(Token::Bang)
            .or_else(|| self.accept(Token::Minus));

        eprintln!("parsing unary {unary:?}");

        if let Some(unary) = unary {
            let op = match unary {
                Token::Bang => UnaryOp::Not,
                Token::Minus => UnaryOp::Neg,
                other => unreachable!("{other}"),
            };

            eprintln!("accepted unary {op} {unary}");

            Ok(AstKind::Unary(op, self.parse_unary()?.into()).into_ast(self))
        } else {
            eprintln!("not unary");
            self.parse_primary()
        }
    }

    /// Accepts a group
    fn parse_group(&self) -> ParseResult<'src> {
        self.expect(Token::LeftParen)?;

        eprintln!("parsing group");

        let inner = self.parse_expr()?;

        self.expect(Token::RightParen)?;

        eprintln!("parsing group DONE");

        Ok(AstKind::Group(inner.into()).into_ast(self))
    }

    /// Accepts a primary
    fn parse_primary(&self) -> ParseResult<'src> {
        let Some(next) = self.next() else {
            return self.err(Expected::Expr);
        };

        let ast = match next {
            Token::Number(n, _) => Primary::Number(n),
            Token::String(s) => Primary::String(Cow::Borrowed(s)),
            Token::Keyword(Keyword::True) => Primary::Bool(true),
            Token::Keyword(Keyword::False) => Primary::Bool(false),
            Token::Keyword(Keyword::Nil) => Primary::Nil,
            Token::Identifier(i) => {
                if let Some(Token::Equal) = self.peek() {
                    self.next().unwrap();
                    let inner = self.parse_expr()?;

                    return Ok(AstKind::VarAssign(i, inner.into()).into_ast(self));
                } else {
                    return Ok(AstKind::VariableAccess(i).into_ast(self));
                }
            }
            _ => {
                self.prev().unwrap();
                return self.parse_group();
            }
        };

        eprintln!("accepted primary {ast}");

        Ok(AstKind::Primary(ast).into_ast(self))
    }
}
