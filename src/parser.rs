use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::{Debug, Display},
};

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
            Self::Number(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "{s}"),
        }
    }
}

pub type Block<'src> = AstNode<BlockInner<'src>>;
#[derive(Debug)]
pub struct BlockInner<'src> {
    decls: Vec<Decl<'src>>,
}

impl<'src> BlockInner<'src> {
    pub fn decls(&self) -> &[Decl<'src>] {
        &self.decls
    }
}

impl Display for BlockInner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(block")?;

        for decl in &self.decls {
            write!(f, " {decl}")?
        }

        write!(f, ")")
    }
}

#[derive(Debug)]
pub struct VarDecl<'src> {
    pub name: &'src str,
    pub value: Option<Expr<'src>>,
}

impl Display for VarDecl<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(varDecl {}{})",
            self.name,
            if let Some(val) = &self.value {
                format!(" {val}")
            } else {
                "".into()
            }
        )
    }
}

pub type Decl<'src> = AstNode<DeclKind<'src>>;

#[derive(Debug)]
pub struct FunDecl<'src> {
    pub(crate) name: &'src str,
    pub(crate) params: Vec<&'src str>,
    pub(crate) body: Block<'src>,
}

impl Display for FunDecl<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, params, body } = self;
        write!(f, "(funDecl {name}")?;
        for p in params {
            write!(f, " {p}")?;
        }
        write!(f, " {body})")
    }
}

#[derive(Debug)]
pub enum DeclKind<'src> {
    Class {
        name: &'src str,
        parent: Option<&'src str>,
        methods: Vec<FunDecl<'src>>,
    },
    Fun(FunDecl<'src>),
    Var(VarDecl<'src>),
    Stmt(Stmt<'src>),
    Expr(Expr<'src>),
}

impl Display for DeclKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Class {
                name,
                parent,
                methods,
            } => {
                write!(f, "(classDecl {name}")?;
                if let Some(parent) = parent {
                    write!(f, " < {parent}")?;
                }

                write!(f, " (methods")?;
                for m in methods {
                    write!(f, " {m}")?;
                }
                write!(f, "))")
            }
            Self::Fun(fun_decl) => write!(f, "{fun_decl}"),
            Self::Var(v) => write!(f, "{v}"),
            Self::Stmt(s) => write!(f, "{s}"),
            Self::Expr(e) => write!(f, "{e}"),
        }
    }
}

#[derive(Debug)]
pub enum ForBegin<'src> {
    VarDecl(VarDecl<'src>),
    Expr(Expr<'src>),
}

impl Display for ForBegin<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VarDecl(v) => write!(f, "{v}"),
            Self::Expr(e) => write!(f, "{e}"),
        }
    }
}

pub type Stmt<'src> = AstNode<StmtKind<'src>>;

#[derive(Debug)]
pub enum StmtKind<'src> {
    Expr(Expr<'src>),
    For {
        begin: Option<ForBegin<'src>>,
        condition: Option<Expr<'src>>,
        after_iter: Option<Expr<'src>>,
        body: Box<Stmt<'src>>,
    },
    If {
        condition: Expr<'src>,
        body: Box<Stmt<'src>>,
        el: Option<Box<Stmt<'src>>>,
    },
    While {
        condition: Expr<'src>,
        body: Box<Stmt<'src>>,
    },
    Print(Expr<'src>),
    Return(Option<Expr<'src>>),
    Block(Block<'src>),
}

impl Display for StmtKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expr(e) => write!(f, "{e}"),
            Self::If {
                condition,
                body,
                el,
            } => {
                write!(f, "(if {condition} then {body}")?;
                if let Some(el) = el {
                    write!(f, " else {el}")?;
                }

                write!(f, ")")
            }
            Self::For {
                begin,
                condition,
                after_iter,
                body,
            } => write!(
                f,
                "(for ({};{};{};) {body})",
                begin.as_ref().map(|i| format!("{i}")).unwrap_or_default(),
                condition
                    .as_ref()
                    .map(|i| format!("{i}"))
                    .unwrap_or_default(),
                after_iter
                    .as_ref()
                    .map(|i| format!("{i}"))
                    .unwrap_or_default(),
            ),
            Self::While { condition, body } => write!(f, "(while {condition} {body})"),

            Self::Print(i) => write!(f, "(print {i})"),
            Self::Return(expr) => {
                write!(f, "(return")?;
                if let Some(expr) = expr {
                    write!(f, " {expr}")?;
                }

                write!(f, ")")
            }
            Self::Block(b) => write!(f, "{b}"),
        }
    }
}

pub type Expr<'src> = AstNode<ExprKind<'src>>;
#[derive(Debug)]
pub enum ExprKind<'src> {
    Assign {
        call: Option<Box<Expr<'src>>>,
        ident: &'src str,
        val: Box<Expr<'src>>,
    },
    Or(Box<Expr<'src>>, Box<Expr<'src>>),
    And(Box<Expr<'src>>, Box<Expr<'src>>),
    Eq(Box<Expr<'src>>, EqOp, Box<Expr<'src>>),
    Cmp(Box<Expr<'src>>, CmpOp, Box<Expr<'src>>),
    Term(Box<Expr<'src>>, TermOp, Box<Expr<'src>>),
    Factor(Box<Expr<'src>>, FactorOp, Box<Expr<'src>>),
    Unary(UnaryOp, Box<Expr<'src>>),
    Call {
        callee: Box<Expr<'src>>,
        args: Vec<Expr<'src>>,
    },
    Access(Box<Expr<'src>>, &'src str),
    Group(Box<Expr<'src>>),
    Ident(&'src str),
    This,
    Super(&'src str),
    Primary(Primary<'src>),
}

impl Display for ExprKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assign { call, ident, val } => {
                write!(f, "(assign ")?;

                if let Some(call) = call {
                    write!(f, "(access {call} {ident}) {val})")
                } else {
                    write!(f, "{ident} {val})")
                }
            }
            Self::Or(a, b) => write!(f, "(or {a} {b})"),
            Self::And(a, b) => write!(f, "(and {a} {b})"),
            Self::Eq(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Cmp(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Term(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Factor(a, op, b) => write!(f, "({op} {a} {b})"),
            Self::Unary(op, i) => write!(f, "({op} {i})"),
            Self::Call { callee, args } => {
                write!(f, "(call {callee}")?;
                for a in args {
                    write!(f, " {a}")?;
                }
                write!(f, ")")
            }
            Self::Access(l, r) => write!(f, "(access {l} {r})"),
            Self::Group(g) => write!(f, "(group {g})"),
            Self::Ident(i) => write!(f, "(ident {i})"),
            Self::This => f.write_str("this"),
            Self::Super(p) => write!(f, "super.{p}"),
            Self::Primary(p) => write!(f, "{p}"),
        }
    }
}

trait IntoAst: Sized {
    fn into_ast(self, line_pos: (usize, usize)) -> AstNode<Self>;
}

impl<T> IntoAst for T {
    fn into_ast(self, (line, pos): (usize, usize)) -> AstNode<T> {
        AstNode {
            line,
            pos,
            kind: self,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct AstNode<K> {
    line: usize,
    pos: usize,
    kind: K,
}

impl<K: Display> Display for AstNode<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // write!(f, "[line {}] {}", self.line + 1, self.kind)
        self.kind.fmt(f)
    }
}

impl<K> AstNode<K> {
    pub fn kind(&self) -> &K {
        &self.kind
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn pos(&self) -> usize {
        self.pos
    }
}

#[derive(Debug)]
pub struct Program<'src>(Block<'src>);

impl<'src> Program<'src> {
    pub fn decls(&self) -> &[Decl<'src>] {
        &self.0.kind.decls
    }
}

#[derive(Debug)]
pub enum ErrorKind<'src> {
    Custom(String),
    TokenAfter(Token<'src>, &'static str),
    TokenAfterToken(Token<'src>, Token<'src>),
    CantReadLocalVarInOwnInit,
    DuplicateVariable,
    InvalidReturn,
    InvalidAssignmentTarget,
    CannotUseThisOutsideOfClass,
    CannotReturnFromInit,
    CantInherintFromItself,
}

impl Display for ErrorKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Custom(e) => write!(f, "Expect {e}."),
            Self::TokenAfter(t, a) => write!(f, "Expect '{}' after {a}.", t.lexeme()),
            Self::TokenAfterToken(a, b) => {
                write!(f, "Expect '{}' after '{}'.", a.lexeme(), b.lexeme())
            }
            Self::CantReadLocalVarInOwnInit => {
                f.write_str("Can't read local variable in its own initializer.")
            }
            Self::DuplicateVariable => {
                f.write_str("Already a variable with this name in this scope.")
            }
            Self::InvalidReturn => f.write_str("Can't return from top-level code."),
            Self::InvalidAssignmentTarget => f.write_str("Invalid assignment target."),
            Self::CannotUseThisOutsideOfClass => f.write_str("Can't use 'this' outside of class."),
            Self::CannotReturnFromInit => f.write_str("Can't return a value from an initializer."),
            Self::CantInherintFromItself => f.write_str("A class can't inherit from itself"),
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

type Result<'src, T> = std::result::Result<T, Error<'src>>;
type AcceptToken<'src> = Option<Token<'src>>;
type AcceptSymbol<'src> = Option<Symbol<Token<'src>>>;

pub const CONSTRUCTOR_FN_NAME: &'static str = "init";

#[derive(PartialEq)]
enum FnType {
    Fn,
    Method,
}

#[derive(Clone, Copy, PartialEq)]
enum Declaring<'src> {
    Var(&'src str),
    Class,
    InitMethod,
}

/// Parses the lox programming language using a recursive descent approach based on Lox's grammar rules
///
/// See https://craftinginterpreters.com/appendix-i.html
///
pub struct Parser<'src> {
    tokens: &'src [Symbol<Token<'src>>],
    idx: Cell<usize>,
    is_global_scope: bool,
    declaring: RefCell<Vec<Declaring<'src>>>,
    fn_count: usize,
    defined_vars_in_scope: HashSet<&'src str>,
    force_ending_semicolon: bool,
    errors: Vec<Error<'src>>,
}

impl<'src> Parser<'src> {
    pub fn no_ending_semicolons(tokens: &'src [Symbol<Token<'src>>]) -> Self {
        Self {
            tokens,
            idx: 0.into(),
            is_global_scope: true,
            declaring: Vec::new().into(),
            fn_count: 0,
            defined_vars_in_scope: HashSet::new(),
            force_ending_semicolon: false,
            errors: Vec::new(),
        }
    }
    pub fn new(tokens: &'src [Symbol<Token<'src>>]) -> Self {
        Self {
            tokens,
            idx: 0.into(),
            is_global_scope: true,
            fn_count: 0,
            declaring: Vec::new().into(),
            defined_vars_in_scope: HashSet::new(),
            force_ending_semicolon: true,
            errors: Vec::new(),
        }
    }

    fn line(&self) -> usize {
        self.peek_symbol()
            .or(self.tokens.last().copied())
            .map(|t| t.line())
            .unwrap_or(0)
    }

    fn pos(&self) -> usize {
        self.peek_symbol()
            .or(self.tokens.last().copied())
            .map(|t| t.pos())
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
        self.get_token(self.idx.get())
    }

    fn next(&self) -> AcceptToken<'src> {
        let token = self.peek();

        if token.is_some() {
            self.idx.set(self.idx.get() + 1);
        }

        token
    }

    fn prev(&self) -> AcceptToken<'src> {
        self.idx.set(self.idx.get() - 1);

        self.peek()
    }

    fn accept(&self, token: Token<'src>) -> AcceptToken<'src> {
        if let Some(next) = self.peek() {
            if next == token {
                return Some(self.next().unwrap());
            }
        };

        None
    }

    fn expect_custom(
        &self,
        token: Token<'src>,
        msg: impl Into<String>,
    ) -> Result<'src, Token<'src>> {
        self.accept(token)
            .ok_or(self.err_inner(ErrorKind::Custom(msg.into())))
    }

    fn custom_err<E>(&self, msg: impl Into<String>) -> Result<'src, E> {
        Err(self.err_inner(ErrorKind::Custom(msg.into())))
    }

    fn expect_after_token(&self, token: Token<'src>) -> Result<'src, Token<'src>> {
        self.accept(token)
            .ok_or(self.err_inner(ErrorKind::TokenAfterToken(
                token,
                self.tokens[self.idx.get() - 2].token(),
            )))
    }

    fn expect_after(&self, token: Token<'src>, after: &'static str) -> Result<'src, Token<'src>> {
        self.accept(token)
            .ok_or(self.err_inner(ErrorKind::TokenAfter(token, after)))
    }

    fn recover(&self) {
        while !matches!(self.next(), Some(Token::Semicolon) | None) {
            if let Some(Token::Keyword(
                Keyword::Class
                | Keyword::Fun
                | Keyword::Var
                | Keyword::For
                | Keyword::If
                | Keyword::While
                | Keyword::Print
                | Keyword::Return,
            )) = self.peek()
            {
                break;
            }
        }
    }

    fn err_inner(&self, kind: ErrorKind<'src>) -> Error<'src> {
        Error {
            line: self.line(),
            token: self.peek(),
            kind,
        }
    }

    fn err<E>(&self, kind: ErrorKind<'src>) -> Result<'src, E> {
        Err(self.err_inner(kind))
    }

    fn line_pos(&self) -> (usize, usize) {
        (self.line(), self.pos())
    }

    /// program        → declaration* EOF ;
    pub fn parse(&mut self) -> std::result::Result<Program<'src>, &Vec<Error<'src>>> {
        let line_pos = self.line_pos();
        let mut decls = Vec::new();

        while self.peek().is_some() {
            match self.parse_decl() {
                Some(d) => decls.push(d),
                None => continue,
            }
        }

        assert_eq!(self.next(), None);

        if !self.errors.is_empty() {
            Err(&self.errors)
        } else {
            Ok(Program(BlockInner { decls }.into_ast(line_pos)))
        }
    }

    /// statement      → exprStmt
    ///                 | forStmt
    ///                 | ifStmt
    ///                 | printStmt
    ///                 | returnStmt
    ///                 | whileStmt
    ///                 | block ;
    fn parse_stmt(&mut self) -> Result<'src, Stmt<'src>> {
        let line_pos = self.line_pos();
        match self.next() {
            Some(Token::Keyword(Keyword::For)) => self.parse_for_stmt(),
            Some(Token::Keyword(Keyword::If)) => self.parse_if_stmt(),
            Some(Token::Keyword(Keyword::Print)) => {
                // printStmt      → "print" expression ";" ;
                let expr = self.parse_expr()?;
                self.expect_after(Token::Semicolon, "value")?;

                Ok(StmtKind::Print(expr).into_ast(line_pos))
            }
            Some(Token::Keyword(Keyword::Return)) => {
                let idx_at_return = self.pos() - 1;
                // returnStmt     → "return" expression? ";" ;
                if self.fn_count == 0 {
                    self.prev().unwrap();
                    return self.err(ErrorKind::DuplicateVariable);
                }

                let expr = self.parse_expr().ok();
                self.expect_after(Token::Semicolon, "return value")?;
                if expr.is_some()
                    && self
                        .declaring
                        .borrow()
                        .iter()
                        .find(|d| **d == Declaring::InitMethod)
                        .is_some()
                {
                    self.idx.set(idx_at_return);
                    return self.err(ErrorKind::CannotReturnFromInit);
                }

                Ok(StmtKind::Return(expr).into_ast(line_pos))
            }
            Some(Token::Keyword(Keyword::While)) => self.parse_while_stmt(),
            Some(Token::LeftBrace) => {
                Ok(StmtKind::Block(self.parse_block(None)?).into_ast(line_pos))
            }
            _ => {
                self.prev().unwrap();
                Ok(StmtKind::Expr(self.parse_expr_stmt()?).into_ast(line_pos))
            }
        }
    }

    /// exprStmt       → expression ";" ;
    fn parse_expr_stmt(&self) -> Result<'src, Expr<'src>> {
        let expr = self.parse_expr()?;
        if self.force_ending_semicolon {
            self.expect_after(Token::Semicolon, "expression")?;
        }

        Ok(expr)
    }

    /// forStmt        → "for" "(" ( varDecl | exprStmt | ";" )
    ///                        expression? ";"
    ///                        expression? ")" statement ;
    fn parse_for_stmt(&mut self) -> Result<'src, Stmt<'src>> {
        self.with_inner_bloc(None, |s| {
            let line_pos = s.line_pos();
            s.expect_after_token(Token::LeftParen)?;
            let begin = match s.next() {
                Some(Token::Semicolon) => None,
                other => Some(match other {
                    Some(Token::Keyword(Keyword::Var)) => ForBegin::VarDecl(s.parse_var_decl()?),
                    _ => {
                        s.prev().unwrap();
                        ForBegin::Expr(s.parse_expr_stmt()?)
                    }
                }),
            };

            let condition = match (s.parse_expr(), s.next()) {
                (Err(_), Some(Token::Semicolon)) => None,
                (Ok(c), Some(Token::Semicolon)) => Some(c),
                (Ok(_), _) => return s.err(ErrorKind::TokenAfter(Token::Semicolon, "condition")),
                (Err(e), _) => return Err(e),
            };

            let after_iter = s.parse_expr().ok();
            s.expect_after(Token::RightParen, "for clauses")?;

            let body = s.parse_stmt()?.into();

            Ok(StmtKind::For {
                begin,
                condition,
                after_iter,
                body,
            }
            .into_ast(line_pos))
        })
    }

    /// ifStmt         → "if" "(" expression ")" statement
    ///              ( "else" statement )? ;
    fn parse_if_stmt(&mut self) -> Result<'src, Stmt<'src>> {
        let line_pos = self.line_pos();
        self.expect_after_token(Token::LeftParen)?;
        let condition = self.parse_expr()?;
        self.expect_after(Token::RightParen, "if condition")?;
        let body = self.parse_stmt()?.into();
        let mut el = None;

        if let Some(Token::Keyword(Keyword::Else)) = self.peek() {
            self.next().unwrap();
            let else_inner = self.parse_stmt()?;
            el = Some(else_inner.into())
        }

        Ok(StmtKind::If {
            condition,
            body,
            el,
        }
        .into_ast(line_pos))
    }

    /// whileStmt      → "while" "(" expression ")" statement ;
    fn parse_while_stmt(&mut self) -> Result<'src, Stmt<'src>> {
        let line_pos = self.line_pos();
        self.expect_after_token(Token::LeftParen)?;
        let condition = self.parse_expr()?;
        self.expect_after(Token::RightParen, "condition")?;
        let body = self.parse_stmt()?.into();

        Ok(StmtKind::While { condition, body }.into_ast(line_pos))
    }

    // fn with_ast_node<T, R>(&mut self, i: T) -> Result<'src, AstNode<R>>
    // where
    //     T: FnOnce(&mut Self) -> Result<'src, R>,
    // {
    //     let (line, pos) = (self.line(), self.pos());

    //     let inner = i(&mut self)?;

    //     Ok(inner.into_ast(self))
    // }

    fn with_inner_bloc<T, R>(
        &mut self,
        default_declared_vars: Option<HashSet<&'src str>>,
        i: T,
    ) -> Result<'src, R>
    where
        T: FnOnce(&mut Self) -> Result<'src, R>,
    {
        let prev = std::mem::replace(
            &mut self.defined_vars_in_scope,
            default_declared_vars.unwrap_or_else(|| HashSet::new()),
        );
        let prev_global_scope = self.is_global_scope;
        self.is_global_scope = false;

        let res = i(self);

        self.defined_vars_in_scope = prev;
        self.is_global_scope = prev_global_scope;

        res
    }

    /// block          → "{" declaration* "}";
    fn parse_block(
        &mut self,
        default_declared_vars: Option<HashSet<&'src str>>,
    ) -> Result<'src, Block<'src>> {
        let line_pos = self.line_pos();
        self.with_inner_bloc(default_declared_vars, |s| {
            let mut decls = Vec::new();
            while !matches!(s.peek(), Some(Token::RightBrace) | None) {
                match s.parse_decl() {
                    Some(d) => decls.push(d),
                    None => continue,
                }
            }

            s.expect_after(Token::RightBrace, "block")?;

            Ok(BlockInner { decls }.into_ast(line_pos))
        })
    }

    /// declaration    → classDecl | funDecl | varDecl | statement;
    fn parse_decl(&mut self) -> Option<Decl<'src>> {
        let line_pos = self.line_pos();
        let maybe_decl = match self.next() {
            Some(Token::Keyword(Keyword::Class)) => self.parse_class_decl(),
            Some(Token::Keyword(Keyword::Fun)) => self
                .parse_fun_decl(FnType::Fn)
                .map(DeclKind::Fun)
                .map(|d| d.into_ast(line_pos)),
            Some(Token::Keyword(Keyword::Var)) => self
                .parse_var_decl()
                .map(|v| DeclKind::Var(v).into_ast(line_pos)),
            _ => {
                self.prev().unwrap();
                self.parse_stmt()
                    .map(|s| DeclKind::Stmt(s).into_ast(line_pos))
            }
        };

        match maybe_decl {
            Ok(decl) => Some(decl),
            Err(e) => {
                self.errors.push(e);

                self.recover();
                None
            }
        }
    }

    /// "class" IDENTIFIER ( "<" IDENTIFIER )?
    ///     "{" function* "}" ;
    fn parse_class_decl(&mut self) -> Result<'src, Decl<'src>> {
        let line_pos = self.line_pos();
        let Some(Token::Identifier(name)) = self.next() else {
            return self.custom_err("class name");
        };

        let mut parent = None;
        if let Some(Token::Less) = self.peek() {
            self.next().unwrap();
            parent = match self.next() {
                Some(Token::Identifier(i)) => Some(i),
                _ => return self.custom_err("superclass name"),
            };
        }

        if parent.map(|p| p == name).unwrap_or(false) {
            self.prev().unwrap();
            return self.err(ErrorKind::CantInherintFromItself);
        }

        self.expect_custom(Token::LeftBrace, "before class body")?;

        let mut methods = Vec::new();
        self.declaring.borrow_mut().push(Declaring::Class);

        while !matches!(self.peek(), Some(Token::RightBrace) | None) {
            methods.push(self.parse_fun_decl(FnType::Method)?)
        }

        self.declaring.borrow_mut().pop().unwrap();

        self.expect_custom(Token::RightBrace, "after class body")?;

        self.defined_vars_in_scope.insert(name);

        Ok(DeclKind::Class {
            name,
            parent,
            methods,
        }
        .into_ast(line_pos))
    }

    // parameters     → IDENTIFIER ( "," IDENTIFIER )* ;
    fn parse_parameters(&self) -> Result<'src, Vec<&'src str>> {
        let mut params = Vec::new();
        let mut lookup = HashSet::new();

        if let Some(Token::Identifier(p)) = self.peek() {
            self.next().unwrap();
            params.push(p);
            lookup.insert(p);
        }

        while let Some(Token::Comma) = self.peek() {
            self.next().unwrap();

            let Some(Token::Identifier(p)) = self.next() else {
                return self.custom_err("parameter name");
            };

            if lookup.contains(&p) {
                self.prev().unwrap();
                return self.err(ErrorKind::DuplicateVariable);
            }

            params.push(p);
            lookup.insert(p);
        }

        Ok(params)
    }

    /// funDecl        → "fun" function ;
    /// function       → IDENTIFIER "(" parameters? ")" block ;
    fn parse_fun_decl(&mut self, ty: FnType) -> Result<'src, FunDecl<'src>> {
        let Some(Token::Identifier(name)) = self.next() else {
            let name = match ty {
                FnType::Method => "method",
                FnType::Fn => "function",
            };
            return self.custom_err(format!("{name} name"));
        };

        self.expect_after(Token::LeftParen, "function name")?;

        let params = self.parse_parameters()?;

        self.expect_after(Token::RightParen, "parameters")?;
        self.expect_custom(Token::LeftBrace, "before function body")?;
        self.fn_count += 1;
        let is_init_method = ty == FnType::Method && name == CONSTRUCTOR_FN_NAME;
        if is_init_method {
            self.declaring.borrow_mut().push(Declaring::InitMethod);
        };

        let body = match self.parse_block(Some(HashSet::from_iter(params.iter().copied()))) {
            Ok(o) => o,
            Err(e) => {
                if is_init_method {
                    self.declaring.borrow_mut().pop().unwrap();
                }
                return Err(e);
            }
        };
        self.fn_count -= 1;

        self.defined_vars_in_scope.insert(name);

        let params = params.into_iter().collect();

        Ok(FunDecl { name, params, body })
    }

    /// varDecl        → "var" IDENTIFIER ( "=" expression )? ";" ;
    fn parse_var_decl(&mut self) -> Result<'src, VarDecl<'src>> {
        let Some(Token::Identifier(name)) = self.next() else {
            return self.custom_err("variable name");
        };

        self.declaring.borrow_mut().push(Declaring::Var(name));

        let var_decl = match self.next() {
            Some(Token::Equal) => {
                let value = self.parse_expr()?;

                if self.defined_vars_in_scope.contains(name) && !self.is_global_scope {
                    self.prev().unwrap();
                    return self.err(ErrorKind::DuplicateVariable);
                }

                self.expect_after(Token::Semicolon, "variable declaration")?;

                let value = value.into();

                VarDecl { name, value }
            }
            Some(Token::Semicolon) => {
                if self.defined_vars_in_scope.contains(name) {
                    self.prev().unwrap();
                    return self.err(ErrorKind::DuplicateVariable);
                }

                VarDecl { name, value: None }
            }
            _ => {
                self.declaring.borrow_mut().pop().unwrap();

                return self.err(ErrorKind::TokenAfter(
                    Token::Semicolon,
                    "variable declaration",
                ));
            }
        };

        self.defined_vars_in_scope.insert(name);
        self.declaring.borrow_mut().pop().unwrap();

        Ok(var_decl)
    }

    /// expression     → assignment ;

    /// assignment     → ( call "." )? IDENTIFIER "=" assignment
    ///                | logic_or ;
    fn parse_expr(&self) -> Result<'src, Expr<'src>> {
        let or_or_setter = self.parse_logic_or()?;

        if self.accept(Token::Equal).is_some() {
            let val = self.parse_expr()?.into();
            let assignment = match or_or_setter.kind {
                ExprKind::Ident(ident) => ExprKind::Assign {
                    call: None,
                    ident,
                    val,
                },
                ExprKind::Access(call, ident) => ExprKind::Assign {
                    call: Some(call),
                    ident,
                    val,
                },
                _ => return self.err(ErrorKind::InvalidAssignmentTarget),
            };

            Ok(assignment.into_ast(self.line_pos()))
        } else {
            Ok(or_or_setter)
        }
    }

    // logic_or       → logic_and ( "or" logic_and )* ;
    fn parse_logic_or(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_logic_and()?;

        while let Some(Token::Keyword(Keyword::Or)) = self.peek() {
            self.next().unwrap();
            let b = self.parse_logic_and()?;

            a = ExprKind::Or(a.into(), b.into()).into_ast(line_pos);
        }

        Ok(a)
    }

    /// logic_and      → equality ( "and" equality )* ;
    fn parse_logic_and(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_eq()?;

        while let Some(Token::Keyword(Keyword::And)) = self.peek() {
            self.next().unwrap();
            let b = self.parse_eq()?;

            a = ExprKind::And(a.into(), b.into()).into_ast(line_pos);
        }

        Ok(a)
    }

    /// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    fn parse_eq(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_cmp()?;

        while let Some(Token::EqualEqual | Token::BangEqual) = self.peek() {
            let op = match self.next().unwrap() {
                Token::EqualEqual => EqOp::Eq,
                Token::BangEqual => EqOp::Neq,
                other => unreachable!("{other}"),
            };
            let b = self.parse_cmp()?;
            a = ExprKind::Eq(a.into(), op, b.into()).into_ast(line_pos);
        }

        Ok(a)
    }

    /// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn parse_cmp(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_term()?;

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
            a = ExprKind::Cmp(a.into(), op, b.into()).into_ast(line_pos);
        }

        Ok(a)
    }

    /// term           → factor ( ( "-" | "+" ) factor )* ;
    fn parse_term(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_factor()?;

        while let Some(Token::Plus | Token::Minus) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Plus => TermOp::Add,
                Token::Minus => TermOp::Sub,
                other => unreachable!("{other}"),
            };
            let b = self.parse_factor()?;
            a = ExprKind::Term(a.into(), op, b.into()).into_ast(line_pos);
        }

        Ok(a)
    }

    /// factor         → unary ( ( "/" | "*" ) unary )* ;
    fn parse_factor(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut a = self.parse_unary()?;

        while let Some(Token::Slash | Token::Star) = self.peek() {
            let op = match self.next().unwrap() {
                Token::Slash => FactorOp::Div,
                Token::Star => FactorOp::Mul,
                other => unreachable!("{other}"),
            };
            let b = self.parse_unary()?;
            a = ExprKind::Factor(a.into(), op, b.into()).into_ast(line_pos)
        }

        Ok(a)
    }

    /// unary          → ( "!" | "-" ) unary | call ;
    fn parse_unary(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let unary = self
            .accept(Token::Bang)
            .or_else(|| self.accept(Token::Minus));

        if let Some(unary) = unary {
            let op = match unary {
                Token::Bang => UnaryOp::Not,
                Token::Minus => UnaryOp::Neg,
                other => unreachable!("{other}"),
            };

            Ok(ExprKind::Unary(op, self.parse_unary()?.into()).into_ast(line_pos))
        } else {
            self.parse_call()
        }
    }

    /// arguments      → expression ( "," expression )* ;
    fn parse_arguments(&self) -> Result<'src, Vec<Expr<'src>>> {
        let mut args = Vec::new();

        if self.peek() == Some(Token::RightParen) {
            return Ok(args);
        }

        args.push(self.parse_expr()?);

        while let Some(Token::Comma) = self.peek() {
            self.next().unwrap();

            args.push(self.parse_expr()?);
        }

        Ok(args)
    }

    /// call           → primary ( "(" arguments? ")" | "." IDENTIFIER )* ;
    fn parse_call(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let mut call = self.parse_primary()?;

        while let Some(next) = self.accept(Token::LeftParen).or(self.accept(Token::Dot)) {
            let next = match next {
                Token::Dot => {
                    let Some(Token::Identifier(ident)) = self.next() else {
                        return self.custom_err("property name after '.'");
                    };

                    ExprKind::Access(call.into(), ident)
                }
                Token::LeftParen => {
                    let args = self.parse_arguments()?;
                    self.expect_after(Token::RightParen, "arguments")?;

                    ExprKind::Call {
                        callee: call.into(),
                        args,
                    }
                }
                other => unreachable!("{other}"),
            };

            call = next.into_ast(line_pos)
        }

        Ok(call)
    }

    /// accepts this part of primary
    ///     "(" expression ")"
    fn parse_group(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let inner = self.parse_expr()?;

        self.expect_after(Token::RightParen, "expression")?;

        Ok(ExprKind::Group(inner.into()).into_ast(line_pos))
    }

    /// primary        → NUMBER | STRING | "true" | "false" | "nil"
    ///                 | "(" expression ")" | IDENTIFIER "=" expression
    fn parse_primary(&self) -> Result<'src, Expr<'src>> {
        let line_pos = self.line_pos();
        let ast = match self.next() {
            Some(Token::Number(n, _)) => Primary::Number(n),
            Some(Token::String(s)) => Primary::String(Cow::Borrowed(s)),
            Some(Token::Keyword(Keyword::True)) => Primary::Bool(true),
            Some(Token::Keyword(Keyword::False)) => Primary::Bool(false),
            Some(Token::Keyword(Keyword::Nil)) => Primary::Nil,
            Some(Token::Keyword(Keyword::This)) => {
                if self
                    .declaring
                    .borrow()
                    .iter()
                    .find(|d| **d == Declaring::Class)
                    .is_some()
                {
                    return Ok(ExprKind::This.into_ast(line_pos));
                } else {
                    self.prev().unwrap();
                    return self.err(ErrorKind::CannotUseThisOutsideOfClass);
                }
            }
            Some(Token::Identifier(i)) => {
                let curr_defining_this_var = self
                    .declaring
                    .borrow()
                    .iter()
                    .find(|d| matches!(d, Declaring::Var(decl_i) if *decl_i == i))
                    .is_some();

                if !self.defined_vars_in_scope.contains(i) && curr_defining_this_var {
                    self.prev().unwrap();
                    return self.err(ErrorKind::CantReadLocalVarInOwnInit);
                }
                return Ok(ExprKind::Ident(i).into_ast(line_pos));
            }
            Some(Token::LeftParen) => {
                return self.parse_group();
            }
            _ => {
                self.prev().unwrap();
                return self.custom_err("expression");
            }
        };

        Ok(ExprKind::Primary(ast).into_ast(line_pos))
    }
}
