use std::{borrow::Cow, cell::Cell, collections::HashMap, fmt::Display, io::Write};

use crate::parser::{
    AstNode, CmpOp, Decl, DeclKind, EqOp, Expr, ExprKind, FactorOp, ForBegin, FunDecl, Primary,
    Stmt, StmtKind, TermOp, UnaryOp, VarDecl,
};

#[derive(Debug)]
pub enum ErrorKind<'e> {
    MustBeNumber,
    BothMustBeNumbers,
    BothMustBeNumbersOrStrings,
    UndefinedVariable(&'e str),
    StackOverflow,
    NotCallable,
    IncorrectArgCount { got: usize, expected: usize },
    Return(Value<'e>),
    Io(std::io::Error),
}

#[derive(Debug)]
pub struct Error<'e> {
    line: usize,
    kind: ErrorKind<'e>,
}

impl<'e> Error<'e> {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }

    pub fn new(line: usize, kind: ErrorKind<'e>) -> Self {
        Self { line, kind }
    }
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self.kind {
            ErrorKind::MustBeNumber => "Operand must be a number.".into(),
            ErrorKind::BothMustBeNumbers => "Operands must be numbers.".into(),
            ErrorKind::BothMustBeNumbersOrStrings => {
                "Operands must be two numbers or two strings.".into()
            }
            ErrorKind::UndefinedVariable(ident) => {
                format!("Undefined variable '{ident}'.")
            }
            ErrorKind::NotCallable => "Can only call functions and classes".into(),
            ErrorKind::IncorrectArgCount { got, expected } => {
                format!("Expected {expected} arguments but got {got}.")
            }
            ErrorKind::StackOverflow => "Stack overflow.".into(),
            ErrorKind::Io(..) => "IO error".into(),
            ErrorKind::Return(ref r) => format!("Return {r}"),
        };

        writeln!(f, "{msg}")?;
        write!(f, "[line {}]", self.line + 1)
    }
}

pub type Result<'e, T> = std::result::Result<T, Error<'e>>;

const STACK_SIZE: usize = 1 << 12;

#[derive(Debug, Clone)]
pub struct FunDef<'e> {
    pos: usize,
    stack_ptr: usize,
    name: &'e str,
    params: &'e [&'e str],
    body: &'e [Decl<'e>],
}

#[derive(Debug, Clone)]
pub struct Class<'e> {
    name: &'e str,
    parent: Option<&'e str>,
    methods: HashMap<&'e str, FunDef<'e>>,
}

#[derive(Debug, Clone)]
pub enum Value<'e> {
    Primary(Primary<'e>),
    NativeFunction(fn() -> Value<'e>),
    Function(FunDef<'e>),
    Class(Class<'e>),
    ClassInstance(Class<'e>, ()),
}

impl<'e> Value<'e> {
    fn call<'a, T: Write>(
        &'a mut self,
        args: &'e [Expr<'e>],
        executor: &mut Executor<'e, T>,
    ) -> Result<'e, Self> {
        match self {
            Self::NativeFunction(f) => Ok(f()),
            Self::Function(FunDef {
                pos,
                stack_ptr,
                name,
                params,
                body,
            }) => {
                let got = args.len();
                let expected = params.len();
                if got != expected {
                    return executor.err(ErrorKind::IncorrectArgCount { got, expected });
                }

                let mut args = args.iter();

                executor.incr_stack_frame()?;
                for p in &params[..] {
                    eprintln!("EVALING PARAM {name} {p} {}", executor.stack_ptr.get());
                    let arg = args.next().unwrap();
                    eprintln!("ARG ON LINE {} SETTING TO {pos}", arg.line());
                    let val = executor.eval_expr(arg)?;
                    executor.current_stack_frame().insert(p, (*pos, val));
                }

                // Set `effective_stack_ptr` to ensure that functions can only access variables in the scope they are defined in
                // And from outer scopes, but not inner ones
                executor.excluded_stack_range = Some((*stack_ptr, executor.stack_ptr.get()));

                let ret = match executor.eval_block_inner(*body, false) {
                    Ok(..) => {
                        executor.decr_stack_frame();
                        Primary::Nil.into()
                    }
                    Err(Error {
                        kind: ErrorKind::Return(ret),
                        ..
                    }) => match ret {
                        // Don't decrement the stack frame.
                        // This way we 'reserve' it for the closure
                        Value::Function(FunDef { stack_ptr, .. }) => {
                            eprintln!("RETURNING CLOSURE {ret:?}");
                            if stack_ptr != executor.stack_ptr.get() {
                                executor.decr_stack_frame();
                                executor.decr_stack_frame();
                            }
                            ret
                        }
                        _ => {
                            executor.decr_stack_frame();
                            executor.decr_stack_frame();

                            eprintln!("RETURNING VAL {ret}");
                            ret
                        }
                    },
                    Err(e) => return Err(e),
                };

                executor.excluded_stack_range = None;

                Ok(ret)
            }
            Self::Class(class) => Ok(Self::ClassInstance(class.clone(), ())),
            Self::Primary(..) | Self::ClassInstance(..) => executor.err(ErrorKind::NotCallable),
        }
    }

    fn truthiness(&self) -> bool {
        !matches!(self, Self::Primary(Primary::Nil | Primary::Bool(false)))
    }

    fn as_num<T: Write>(&self, executor: &Executor<'e, T>) -> Result<'e, f64> {
        match self {
            Self::Primary(Primary::Number(n)) => Ok(n.into()),
            _ => executor.err(ErrorKind::MustBeNumber),
        }
    }

    fn as_str(&self) -> Option<&std::borrow::Cow<'e, str>> {
        match self {
            Self::Primary(Primary::String(s)) => Some(s),
            _ => None,
        }
    }
}

impl<'e> From<Primary<'e>> for Value<'e> {
    fn from(value: Primary<'e>) -> Self {
        Value::Primary(value)
    }
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primary(p) => p.fmt(f),
            Self::NativeFunction(..) => write!(f, "<native fn>"),
            Self::Function(FunDef { name, .. }) => write!(f, "<fn {name}>"),
            Self::Class(Class { name, .. }) => write!(f, "{name}"),
            Self::ClassInstance(Class { name, .. }, _) => write!(f, "{name} instance"),
        }
    }
}

pub struct Executor<'e, T> {
    program: &'e [Decl<'e>],
    stack: [Option<HashMap<&'e str, (usize, Value<'e>)>>; STACK_SIZE],
    stack_ptr: Cell<usize>,
    line: Cell<usize>,
    pos: Cell<usize>,
    excluded_stack_range: Option<(usize, usize)>,
    stdout: T,
}

impl<'e> Executor<'e, std::io::Stdout> {
    pub fn with_stdout(program: &'e [Decl<'e>]) -> Self {
        Self::new(program, std::io::stdout())
    }
}

macro_rules! make_var_resolver {
    ($s: expr, $getter: tt, $ref: tt, $ident: ident) => {
        if let Some(i) = $s.find_var_frame($ident) {
            let (_, v) = $s.stack[i].$ref().unwrap().$getter($ident).unwrap();
            Ok(v)
        } else {
            $s.err(ErrorKind::UndefinedVariable($ident))
        }
    };
}

impl<'e, T: Write> Executor<'e, T> {
    pub fn new(program: &'e [Decl<'e>], stdout: T) -> Self {
        let mut stack = [const { None }; STACK_SIZE];

        let mut globals = HashMap::new();

        fn clock<'a>() -> Value<'a> {
            Value::Primary(Primary::Number(
                (std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() as f64)
                    .into(),
            ))
        }

        globals.insert("clock", (0, Value::NativeFunction(clock)));

        stack[0] = Some(globals);

        Self {
            program,
            stack,
            stack_ptr: 0.into(),
            line: 0.into(),
            pos: 0.into(),
            excluded_stack_range: None,
            stdout,
        }
    }

    fn err_inner(&self, kind: ErrorKind<'e>) -> Error<'e> {
        Error::new(self.line.get(), kind)
    }
    fn err<E>(&self, kind: ErrorKind<'e>) -> Result<'e, E> {
        Err(self.err_inner(kind))
    }

    /// returns the previous stack frame
    fn decr_stack_frame(&mut self) -> HashMap<&'e str, (usize, Value<'e>)> {
        eprintln!("decring stack frame {}", self.stack_ptr.get());
        let prev = self.current_stack_frame_inner().take().unwrap();
        self.stack_ptr.set(self.stack_ptr.get() - 1);

        prev
    }

    fn incr_stack_frame(&mut self) -> Result<'e, ()> {
        let curr = self.stack_ptr.get();
        if curr < STACK_SIZE - 1 {
            eprintln!("incring stack frame {}", self.stack_ptr.get());
            self.stack_ptr.set(curr + 1);

            *self.current_stack_frame_inner() = Some(HashMap::new());

            Ok(())
        } else {
            self.err(ErrorKind::StackOverflow)
        }
    }

    fn current_stack_frame_inner(&mut self) -> &mut Option<HashMap<&'e str, (usize, Value<'e>)>> {
        let stack_ptr = self.stack_ptr.get();
        &mut self.stack[stack_ptr]
    }

    fn current_stack_frame(&mut self) -> &mut HashMap<&'e str, (usize, Value<'e>)> {
        self.current_stack_frame_inner().as_mut().unwrap()
    }
    fn find_var_frame(&self, ident: &str) -> Option<usize> {
        let curr = self.stack_ptr.get();
        let (a, b) = self.excluded_stack_range.unwrap_or((curr, curr));
        eprintln!("checking frame ranges 0 .. {a} and {b} .. {curr}");
        (0..=a).chain(b..=curr).rev().find(|&i| {
            eprintln!(
                "LOOKING AT FRAME {i} {:?}",
                self.stack[i].as_ref().unwrap().keys().collect::<Vec<_>>()
            );
            self.stack[i]
                .as_ref()
                .and_then(|frame| frame.get(ident))
                .and_then(|(pos, _)| {
                    eprintln!(
                        "TRYING TO GET VAR {ident} at pos {pos}. Curr pos is {} {}",
                        self.pos.get(),
                        self.line.get(),
                    );
                    if *pos <= self.pos.get() {
                        Some(())
                    } else {
                        None
                    }
                })
                .is_some()
        })
    }

    fn resolve_var(&self, ident: &'e str) -> Result<'e, &Value<'e>> {
        make_var_resolver!(self, get, as_ref, ident)
    }

    fn resolve_var_mut(&mut self, ident: &'e str) -> Result<'e, &mut Value<'e>> {
        make_var_resolver!(self, get_mut, as_mut, ident)
    }

    fn print_value(p: Value<'e>) -> String {
        match p {
            Value::Primary(Primary::Number(n)) => format!("{}", Into::<f64>::into(n)),
            p => format!("{p}"),
        }
    }

    pub fn eval(&mut self) -> Result<'e, String> {
        let expr = match self.program.first().unwrap().kind() {
            DeclKind::Expr(expr) => Some(expr),
            DeclKind::Stmt(d) => match d.kind() {
                StmtKind::Expr(e) => Some(e),
                _ => None,
            },
            _ => None,
        };

        let expr = expr.expect("eval only supports programs with one expression");

        Ok(Self::print_value(self.eval_expr(expr)?))
    }

    pub fn run(&mut self) -> Result<'e, ()> {
        for decl in self.program {
            self.eval_decl(decl)?;
        }

        Ok(())
    }

    fn set_line<A>(&self, node: &'e AstNode<A>) {
        eprintln!("SETTING LINE TO {} {}", node.line(), node.pos());
        self.line.set(node.line());
        self.pos.set(node.pos());
    }

    fn eval_var_decl(&mut self, var_decl: &'e VarDecl<'e>) -> Result<'e, ()> {
        let VarDecl { name, value } = var_decl;
        let value_with_pos = match value {
            Some(v) => (v.pos(), self.eval_expr(v)?),
            None => (self.pos.get(), Value::Primary(Primary::Nil)),
        };

        self.current_stack_frame().insert(name, value_with_pos);

        Ok(())
    }

    fn eval_decl(&mut self, decl: &'e Decl<'e>) -> Result<'e, ()> {
        self.set_line(decl);
        match decl.kind() {
            DeclKind::Expr(e) => {
                self.eval_expr(e)?;
            }
            DeclKind::Stmt(s) => {
                self.eval_stmt(s)?;
            }
            DeclKind::Var(v) => self.eval_var_decl(v)?,
            DeclKind::Fun(FunDecl { name, params, body }) => {
                let stack_ptr = self.stack_ptr.get();
                let pos = self.pos.get();
                self.current_stack_frame().insert(
                    name,
                    (
                        pos,
                        Value::Function(FunDef {
                            pos,
                            stack_ptr,
                            name,
                            params,
                            body: body.kind().decls(),
                        }),
                    ),
                );
            }
            DeclKind::Class {
                name,
                parent,
                methods: method_decls,
            } => {
                let stack_ptr = self.stack_ptr.get();
                let pos = self.pos.get();

                let mut methods = HashMap::new();

                for FunDecl { name, params, body } in method_decls {
                    methods.insert(
                        *name,
                        FunDef {
                            pos,
                            stack_ptr,
                            name,
                            params,
                            body: body.kind().decls(),
                        },
                    );
                }

                self.current_stack_frame().insert(
                    name,
                    (
                        pos,
                        Value::Class(Class {
                            name,
                            parent: *parent,
                            methods,
                        }),
                    ),
                );
            }
        };

        Ok(())
    }

    fn eval_block_inner(
        &mut self,
        decls: impl IntoIterator<Item = &'e Decl<'e>>,
        declr_stack_frame_on_ret: bool,
    ) -> Result<'e, ()> {
        let (p_line, p_pos) = (self.line.get(), self.pos.get());
        self.incr_stack_frame()?;
        for decl in decls {
            let res = self.eval_decl(decl);

            if let Err(Error {
                kind: ErrorKind::Return(..),
                ..
            }) = res
            {
                if declr_stack_frame_on_ret {
                    self.decr_stack_frame();
                }

                self.pos.set(p_pos);
                self.line.set(p_line);
            }

            res?;
        }

        self.pos.set(p_pos);
        self.line.set(p_line);
        self.decr_stack_frame();

        Ok(())
    }

    fn eval_block(&mut self, decls: impl IntoIterator<Item = &'e Decl<'e>>) -> Result<'e, ()> {
        self.eval_block_inner(decls, true)
    }

    fn eval_stmt(&mut self, stmt: &'e Stmt<'e>) -> Result<'e, ()> {
        self.set_line(stmt);
        match stmt.kind() {
            StmtKind::Expr(e) => {
                self.eval_expr(e)?;
            }
            StmtKind::For {
                begin,
                condition,
                after_iter,
                body,
            } => {
                self.incr_stack_frame()?;
                if let Some(begin) = begin {
                    match begin {
                        ForBegin::Expr(e) => {
                            self.eval_expr(e)?;
                        }
                        ForBegin::VarDecl(v) => self.eval_var_decl(v)?,
                    }
                }

                while match condition {
                    Some(c) => self.eval_expr(c)?.truthiness(),
                    None => true,
                } {
                    self.eval_stmt(body)?;
                    if let Some(after_iter) = after_iter {
                        self.eval_expr(after_iter)?;
                    }
                }
                self.decr_stack_frame();
            }
            StmtKind::If {
                condition,
                body,
                el,
            } => {
                if self.eval_expr(condition)?.truthiness() {
                    self.eval_stmt(body)?;
                } else if let Some(el) = el {
                    self.eval_stmt(el)?;
                }
            }
            StmtKind::While { condition, body } => {
                while self.eval_expr(condition)?.truthiness() {
                    self.eval_stmt(body)?;
                }
            }
            StmtKind::Print(expr) => {
                let val = self.eval_expr(expr)?;
                let print = Self::print_value(val);
                eprintln!("PRINTING {print}");
                writeln!(self.stdout, "{print}").map_err(|io| self.err_inner(ErrorKind::Io(io)))?;
            }
            StmtKind::Return(ret) => {
                let ret = if let Some(ret) = ret {
                    self.eval_expr(ret)?
                } else {
                    Primary::Nil.into()
                };
                return self.err(ErrorKind::Return(ret));
            }
            StmtKind::Block(b) => {
                eprintln!("evaling normal block");
                self.eval_block(b.kind().decls())?
            }
        };

        Ok(())
    }

    fn eval_expr(&mut self, expr: &'e Expr<'e>) -> Result<'e, Value<'e>> {
        self.set_line(expr);

        let v = match expr.kind() {
            ExprKind::Assign(ident, val) => {
                let val = self.eval_expr(val)?;
                eprintln!("GOT VAL {val}. ASSIGNING TO {ident}");
                *self.resolve_var_mut(ident)? = val.clone();

                val
            }
            ExprKind::Or(a, b) => {
                let a = self.eval_expr(a)?;

                if a.truthiness() {
                    a
                } else {
                    self.eval_expr(b)?
                }
            }
            ExprKind::And(a, b) => {
                let a = self.eval_expr(a)?;

                if a.truthiness() {
                    self.eval_expr(b)?
                } else {
                    Primary::Bool(false).into()
                }
            }
            ExprKind::Eq(a, op, b) => {
                let a = self.eval_expr(a)?;
                let b = self.eval_expr(b)?;
                let res = match (a, b) {
                    (Value::Primary(a), Value::Primary(b)) => match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    },
                    _ => false,
                };

                Primary::Bool(res).into()
            }
            ExprKind::Cmp(a, op, b) => {
                let a = self.eval_expr(a)?.as_num(self)?;
                let b = self.eval_expr(b)?.as_num(self)?;
                let res = match op {
                    CmpOp::Gte => a >= b,
                    CmpOp::Gt => a > b,
                    CmpOp::Lte => a <= b,
                    CmpOp::Lt => a < b,
                };

                Primary::Bool(res).into()
            }
            ExprKind::Term(a, op, b) => {
                let a = self.eval_expr(a)?;
                let b = self.eval_expr(b)?;
                let res = match op {
                    TermOp::Add => {
                        if let (Some(a), Some(b)) = (a.as_str(), b.as_str()) {
                            Primary::String(Cow::Owned(a.clone().into_owned() + b))
                        } else if let (Ok(a), Ok(b)) = (a.as_num(self), b.as_num(self)) {
                            Primary::Number((a + b).into())
                        } else {
                            return self.err(ErrorKind::BothMustBeNumbersOrStrings);
                        }
                    }
                    TermOp::Sub => {
                        if let (Ok(a), Ok(b)) = (a.as_num(self), b.as_num(self)) {
                            Primary::Number((a - b).into())
                        } else {
                            return self.err(ErrorKind::BothMustBeNumbers);
                        }
                    }
                };

                res.into()
            }
            ExprKind::Factor(a, op, b) => {
                let a = self.eval_expr(a)?.as_num(self)?;
                let b = self.eval_expr(b)?.as_num(self)?;
                let res = match op {
                    FactorOp::Div => a / b,
                    FactorOp::Mul => a * b,
                };

                Primary::Number(res.into()).into()
            }
            ExprKind::Unary(op, expr) => match op {
                UnaryOp::Not => Primary::Bool(!self.eval_expr(expr)?.truthiness()).into(),
                UnaryOp::Neg => {
                    Primary::Number((-self.eval_expr(expr)?.as_num(self)?).into()).into()
                }
            },
            ExprKind::Call { callee, args } => self.eval_expr(callee)?.call(args, self)?,
            ExprKind::Ident(ident) => self.resolve_var(ident)?.clone(),
            ExprKind::Group(i) => self.eval_expr(i)?,
            ExprKind::Primary(p) => p.clone().into(),
        };

        Ok(v)
    }
}
