use std::{borrow::Cow, cell::Cell, collections::HashMap, fmt::Display, io::Write};

use crate::parser::{AstKind, AstNode, CmpOp, EqOp, FactorOp, Primary, TermOp, UnaryOp};

#[derive(Debug)]
pub enum ErrorKind<'e> {
    MustBeNumber,
    BothMustBeNumbers,
    BothMustBeNumbersOrStrings,
    UndefinedVariable(&'e str),
    StackOverflow,
    NotCallable,
    NotEnoughParams,
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
            ErrorKind::NotCallable => "Not callable".into(),
            ErrorKind::NotEnoughParams => "Not enough params".into(),
            ErrorKind::StackOverflow => "Stack overflow.".into(),
            ErrorKind::Io(..) => "IO error".into(),
        };

        writeln!(f, "{msg}")?;
        write!(f, "[line {}]", self.line + 1)
    }
}

pub type Result<'e, T> = std::result::Result<T, Error<'e>>;

const STACK_SIZE: usize = 1 << 12;

#[derive(Debug, Clone)]
enum Value<'e> {
    Primary(Primary<'e>),
    NativeFunction(fn() -> Value<'e>),
    Function {
        name: &'e str,
        params: &'e [&'e str],
        body: &'e AstNode<'e>,
    },
}

impl<'e> Value<'e> {
    fn call<T: Write>(
        &self,
        node: &'e AstNode<'e>,
        args: &'e [AstNode<'e>],
        executor: &mut Executor<'e, T>,
    ) -> Result<'e, Self> {
        eprintln!("calling {self}");
        match self {
            Self::NativeFunction(f) => Ok(f()),
            Self::Function { name, params, body } => {
                eprintln!("calling fn {name}");
                executor.incr_stack_frame(node)?;

                let mut args = args.iter();

                for p in &params[..] {
                    let arg = match args.next() {
                        Some(a) => a,
                        None => return Err(executor.err_inner(node, ErrorKind::NotEnoughParams)),
                    };

                    let val = executor.eval_node(arg)?;

                    eprintln!("setting param {p} to {val}");

                    executor.current_stack_frame().insert(p, val);
                }

                let res = executor.eval_node(body)?;

                eprintln!("got res {res}");

                executor.decr_stack_frame();

                Ok(res)
            }
            Self::Primary(..) => executor.err(node, ErrorKind::NotCallable),
        }
    }

    fn truthiness(&self) -> bool {
        !matches!(self, Self::Primary(Primary::Nil | Primary::Bool(false)))
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
            Self::Function { name, .. } => write!(f, "<fn {name}>"),
        }
    }
}

pub struct Executor<'e, T> {
    program: &'e [AstNode<'e>],
    stack: [Option<HashMap<&'e str, Value<'e>>>; STACK_SIZE],
    stack_ptr: Cell<usize>,
    stdout: T,
}

impl<'e> Executor<'e, std::io::Stdout> {
    pub fn with_stdout(program: &'e [AstNode<'e>]) -> Self {
        Self::new(program, std::io::stdout())
    }
}

impl<'e, T: Write> Executor<'e, T> {
    pub fn new(program: &'e [AstNode<'e>], stdout: T) -> Self {
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

        globals.insert("clock", Value::NativeFunction(clock));

        stack[0] = Some(globals);

        Self {
            program,
            stdout,
            stack,
            stack_ptr: 0.into(),
        }
    }

    pub fn eval(&mut self) -> Result<'e, String> {
        let p = self.eval_primary()?;

        if let Some(p) = p {
            Ok(Self::print_value(p))
        } else {
            Ok(String::new())
        }
    }

    pub fn run(&mut self) -> Result<'e, ()> {
        self.eval()?;

        Ok(())
    }

    fn eval_primary(&mut self) -> Result<'e, Option<Value<'e>>> {
        let mut res = None;
        eprintln!("evaling program");
        for declr in self.program {
            eprintln!("evaling declr {declr}");
            res = Some(self.eval_node(declr)?);
        }

        Ok(res)
    }

    fn err_inner(&self, node: &'e AstNode<'e>, kind: ErrorKind<'e>) -> Error<'e> {
        Error::new(node.line(), kind)
    }
    fn err<E>(&self, node: &'e AstNode<'e>, kind: ErrorKind<'e>) -> Result<'e, E> {
        Err(self.err_inner(node, kind))
    }

    fn decr_stack_frame(&mut self) {
        *self.current_stack_frame_inner() = None;
        self.stack_ptr.set(self.stack_ptr.get() - 1);
    }

    fn incr_stack_frame(&mut self, node: &'e AstNode<'e>) -> Result<'e, ()> {
        let curr = self.stack_ptr.get();
        if curr < STACK_SIZE {
            self.stack_ptr.set(curr + 1);
            Ok(())
        } else {
            self.err(node, ErrorKind::StackOverflow)
        }
    }

    fn current_stack_frame_inner(&mut self) -> &mut Option<HashMap<&'e str, Value<'e>>> {
        let stack_ptr = self.stack_ptr.get();
        &mut self.stack[stack_ptr]
    }

    fn current_stack_frame(&mut self) -> &mut HashMap<&'e str, Value<'e>> {
        let stack_frame = self.current_stack_frame_inner();
        if let Some(frame) = stack_frame {
            return frame;
        }

        *stack_frame = Some(HashMap::new());

        let Some(frame) = stack_frame else {
            unreachable!()
        };

        frame
    }
    fn find_var_frame(&self, ident: &str) -> Option<usize> {
        (0..=self.stack_ptr.get()).rev().find(|&i| {
            self.stack[i]
                .as_ref()
                .and_then(|frame| frame.get(ident))
                .is_some()
        })
    }

    fn resolve_var(&self, node: &'e AstNode<'e>, ident: &'e str) -> Result<'e, &Value<'e>> {
        if let Some(i) = self.find_var_frame(ident) {
            let v = self.stack[i].as_ref().unwrap().get(ident).unwrap();
            eprintln!("resolved var {ident} to {v}");
            return Ok(v);
        }
        self.err(node, ErrorKind::UndefinedVariable(ident))
    }

    fn resolve_var_mut(
        &mut self,
        node: &'e AstNode<'e>,
        ident: &'e str,
    ) -> Result<'e, &mut Value<'e>> {
        if let Some(i) = self.find_var_frame(ident) {
            let v = self.stack[i].as_mut().unwrap().get_mut(ident).unwrap();
            eprintln!("resolved var {ident} to {v} (mutably)");
            return Ok(v);
        }
        self.err(node, ErrorKind::UndefinedVariable(ident))
    }

    fn print_value(p: Value<'e>) -> String {
        match p {
            Value::Primary(Primary::Number(n)) => format!("{}", Into::<f64>::into(n)),
            p => format!("{p}"),
        }
    }

    fn eval_node(&mut self, node: &'e AstNode<'e>) -> Result<'e, Value<'e>> {
        eprintln!("eval {node}");
        let value = match node.kind() {
            AstKind::If {
                condition,
                body,
                el,
            } => {
                if self.truthiness(condition)? {
                    self.eval_node(body)?;
                } else if let Some(el) = el {
                    self.eval_node(el)?;
                }

                Primary::Bool(true).into()
            }
            AstKind::For {
                begin,
                condition,
                after_iter,
                body,
            } => {
                if let Some(begin) = begin {
                    self.eval_node(begin)?;
                }

                while match condition {
                    Some(c) => self.truthiness(c)?,
                    None => true,
                } {
                    self.eval_node(body)?;
                    if let Some(after_iter) = after_iter {
                        self.eval_node(after_iter)?;
                    }
                }

                Primary::Bool(true).into()
            }
            AstKind::While { condition, body } => {
                while self.truthiness(condition)? {
                    self.eval_node(body)?;
                }

                Primary::Bool(true).into()
            }
            AstKind::Block(i) => {
                self.incr_stack_frame(node)?;
                for i in i {
                    self.eval_node(i)?;
                }
                self.decr_stack_frame();

                Primary::Bool(true).into()
            }
            AstKind::VarDecl(ident, i) => {
                let val = match i {
                    Some(i) => self.eval_node(i)?,
                    None => Value::Primary(Primary::Nil),
                };

                self.current_stack_frame().insert(ident, val);

                Primary::Bool(true).into()
            }
            AstKind::VarAssign(ident, i) => {
                let new_val = self.eval_node(i)?;
                *self.resolve_var_mut(node, ident)? = new_val.clone();

                new_val
            }
            AstKind::Print(i) => {
                let node_val = self.eval_node(i)?;
                let out = Self::print_value(node_val);

                eprintln!("printing {out}");
                writeln!(self.stdout, "{}", out).map_err(|io| Error {
                    line: i.line(),
                    kind: ErrorKind::Io(io),
                })?;

                Primary::Bool(true).into()
            }
            AstKind::Or(a, b) => {
                if self.truthiness(a)? {
                    self.eval_node(a)?
                } else {
                    self.eval_node(b)?
                }
            }
            AstKind::And(a, b) => {
                if self.truthiness(a)? {
                    self.eval_node(b)?
                } else {
                    self.eval_node(a)?
                }
            }
            AstKind::Equality(..) => Primary::Bool(self.truthiness(node)?).into(),
            AstKind::Cmp(..) => Primary::Bool(self.truthiness(node)?).into(),
            AstKind::Term(..) => self
                .as_num(node)
                .map(|n| Primary::Number(n.into()).into())
                .or_else(|_| {
                    self.as_string(node)
                        .map(Primary::String)
                        .map(Into::into)
                        .ok_or_else(|| self.err_inner(node, ErrorKind::BothMustBeNumbersOrStrings))
                })?,
            AstKind::Factor(..) => Primary::Number(self.as_num(node)?.into()).into(),
            AstKind::Unary(op, i) => match op {
                UnaryOp::Not => Primary::Bool(!self.truthiness(i)?).into(),
                UnaryOp::Neg => Primary::Number((-self.as_num(i)?).into()).into(),
            },
            AstKind::FunDecl { name, params, body } => {
                eprintln!("defining fn");
                self.current_stack_frame()
                    .insert(name, Value::Function { name, params, body });
                eprintln!("defined fn");

                Primary::Bool(true).into()
            }
            AstKind::Call { callee, args } => {
                eprintln!("CALLING HERERE");
                let val = self.eval_node(callee)?;
                eprintln!("calling val {val}");
                val.call(node, args, self)?
            }
            AstKind::Group(i) => self.eval_node(i)?,
            AstKind::VariableAccess(ident) => self.resolve_var(node, ident)?.clone(),
            AstKind::Primary(p) => p.clone().into(),
        };

        eprintln!("returning value {value}");

        Ok(value)
    }

    fn as_num(&mut self, node: &'e AstNode<'e>) -> Result<'e, f64> {
        eprintln!("as num {node}");
        match node.kind() {
            AstKind::Term(a, op, b) => match op {
                TermOp::Add => Ok(self.as_num(a)? + self.as_num(b)?),
                TermOp::Sub => Ok(self.as_num(a)? - self.as_num(b)?),
            },
            AstKind::Factor(a, op, b) => {
                if let (Ok(a), Ok(b)) = (self.as_num(a), self.as_num(b)) {
                    Ok(match op {
                        FactorOp::Mul => a * b,
                        FactorOp::Div => a / b,
                    })
                } else {
                    self.err(node, ErrorKind::BothMustBeNumbers)
                }
            }
            AstKind::Unary(op, i) => match op {
                UnaryOp::Not => self.err(node, ErrorKind::MustBeNumber),
                UnaryOp::Neg => Ok(-self.as_num(i)?),
            },
            AstKind::Group(i) => self.as_num(i),
            AstKind::VariableAccess(ident) => {
                if let Value::Primary(Primary::Number(n)) = self.resolve_var(node, ident)? {
                    Ok((*n).into())
                } else {
                    self.err(node, ErrorKind::MustBeNumber)
                }
            }
            AstKind::Primary(Primary::Number(n)) => Ok(n.into()),
            AstKind::Call { callee, args } => {
                match self.eval_node(callee)?.call(node, args, self)? {
                    Value::Primary(Primary::Number(n)) => Ok(n.into()),
                    _ => self.err(node, ErrorKind::MustBeNumber),
                }
            }
            _ => self.err(node, ErrorKind::MustBeNumber),
        }
    }

    fn as_string(&self, node: &'e AstNode<'e>) -> Option<Cow<'e, str>> {
        eprintln!("as str {node}");
        match node.kind() {
            AstKind::Term(a, op, b) => {
                if let (Some(a), Some(b), TermOp::Add) = (self.as_string(a), self.as_string(b), op)
                {
                    eprintln!("both valid strings");
                    return Some(Cow::Owned(a.into_owned() + &b));
                }
            }
            AstKind::Group(i) => return self.as_string(i),
            AstKind::VariableAccess(ident) => {
                if let Value::Primary(Primary::String(s)) = self.resolve_var(node, ident).ok()? {
                    return Some(s.clone());
                }
            }
            AstKind::Primary(Primary::String(s)) => return Some(Cow::Borrowed(s)),
            _ => {}
        };

        None
    }

    fn truthiness(&mut self, node: &'e AstNode<'e>) -> Result<'e, bool> {
        eprintln!("truthiness {node}");
        let res = match node.kind() {
            AstKind::If { .. } => true,
            AstKind::While { .. } => true,
            AstKind::For { .. } => true,
            AstKind::Block(..) => true,
            AstKind::VarDecl(..) => true,
            AstKind::VarAssign(_, i) => {
                self.eval_node(node)?;
                self.truthiness(i)?
            }
            AstKind::FunDecl { .. } => true,
            AstKind::Call { callee, args } => {
                self.eval_node(callee)?.call(node, args, self)?.truthiness()
            }
            AstKind::Print(..) => true,
            AstKind::Or(a, b) => self.truthiness(a)? || self.truthiness(b)?,
            AstKind::And(a, b) => self.truthiness(a)? && self.truthiness(b)?,
            AstKind::Equality(a, op, b) => {
                if let Ok(a) = self.as_num(a) {
                    let Ok(b) = self.as_num(b) else {
                        return Ok(false);
                    };

                    match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    }
                } else if let Some(a) = self.as_string(a) {
                    let Some(b) = self.as_string(b) else {
                        return Ok(false);
                    };

                    match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    }
                } else {
                    match op {
                        EqOp::Eq => self.truthiness(a)? == self.truthiness(b)?,
                        EqOp::Neq => self.truthiness(a)? != self.truthiness(b)?,
                    }
                }
            }
            AstKind::Cmp(a, op, b) => match op {
                CmpOp::Gt => self.as_num(a)? > self.as_num(b)?,
                CmpOp::Gte => self.as_num(a)? >= self.as_num(b)?,
                CmpOp::Lt => self.as_num(a)? < self.as_num(b)?,
                CmpOp::Lte => self.as_num(a)? <= self.as_num(b)?,
            },
            AstKind::Term(..) => true,
            AstKind::Factor(..) => true,
            AstKind::Unary(op, i) => match op {
                UnaryOp::Not => !self.truthiness(i)?,
                UnaryOp::Neg => self.truthiness(i)?,
            },
            AstKind::VariableAccess(ident) => self.resolve_var(node, ident)?.truthiness(),
            AstKind::Group(i) => self.truthiness(i)?,
            AstKind::Primary(p) => Value::truthiness(&p.clone().into()),
        };

        Ok(res)
    }
}
