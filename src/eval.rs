use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::HashMap,
    fmt::{Debug, Display},
    io::Write,
    rc::Rc,
};

use crate::parser::{
    AstNode, CONSTRUCTOR_FN_NAME, CmpOp, Decl, DeclKind, EqOp, Expr, ExprKind, FactorOp, ForBegin,
    FunDecl, Primary, Stmt, StmtKind, TermOp, UnaryOp, VarDecl,
};

#[derive(Debug)]
pub enum ErrorKind<'src> {
    MustBeNumber,
    BothMustBeNumbers,
    BothMustBeNumbersOrStrings,
    UndefinedVariable(&'src str),
    UndefinedProperty(&'src str),
    OnlyInstancesHave(&'static str),
    NotCallable,
    IncorrectArgCount { got: usize, expected: usize },
    SuperClassMustBeAClass,
    Return(Rc<RefCell<Value<'src>>>),
    Io(std::io::Error),
}

#[derive(Debug)]
pub struct Error<'src> {
    line: usize,
    kind: ErrorKind<'src>,
}

impl<'src> Error<'src> {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn kind(&self) -> &ErrorKind<'src> {
        &self.kind
    }

    pub fn new(line: usize, kind: ErrorKind<'src>) -> Self {
        Self { line, kind }
    }
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self.kind {
            ErrorKind::MustBeNumber => "Operand must be a number".into(),
            ErrorKind::BothMustBeNumbers => "Operands must be numbers".into(),
            ErrorKind::BothMustBeNumbersOrStrings => {
                "Operands must be two numbers or two strings".into()
            }
            ErrorKind::UndefinedVariable(ident) => {
                format!("Undefined variable '{ident}'")
            }
            ErrorKind::UndefinedProperty(p) => {
                format!("Undefined property '{p}'")
            }
            ErrorKind::OnlyInstancesHave(prop_or_field) => {
                format!("Only instances have {prop_or_field}")
            }
            ErrorKind::NotCallable => "Can only call functions and classes".into(),
            ErrorKind::IncorrectArgCount { got, expected } => {
                format!("Expected {expected} arguments but got {got}")
            }
            ErrorKind::SuperClassMustBeAClass => "Superclass must be a class".into(),
            ErrorKind::Io(..) => "IO error".into(),
            ErrorKind::Return(ref r) => format!("Return {}", r.borrow()),
        };

        writeln!(f, "{msg}.")?;
        write!(f, "[line {}]", self.line + 1)
    }
}

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;

#[derive(Debug, Clone, Copy)]
pub struct FunDef<'src> {
    pos: usize,
    name: &'src str,
    params: &'src [&'src str],
    body: &'src [Decl<'src>],
}

#[derive(Debug, Clone)]
pub struct FnVal<'src> {
    def: FunDef<'src>,
    env: Rc<RefCell<Environment<'src>>>,
    is_constructor: bool,
}

type Map<'src> = HashMap<&'src str, (usize, Rc<RefCell<Value<'src>>>)>;

#[derive(Debug, Clone)]
pub struct Class<'src> {
    name: &'src str,
    spr: Option<Rc<Self>>,
    methods: HashMap<&'src str, FnVal<'src>>,
}

#[derive(Debug, Clone)]
pub enum Value<'src> {
    Primary(Primary<'src>),
    NativeFunction(fn() -> Value<'src>),
    Function(FnVal<'src>),
    Class(Rc<Class<'src>>),
    ClassInstance {
        c: Rc<Class<'src>>,
        props: Rc<RefCell<Map<'src>>>,
    },
    Map(Map<'src>),
}

impl<'src> Value<'src> {
    fn call<T: Write>(
        &self,
        mut args: Vec<Rc<RefCell<Value<'src>>>>,
        executor: &Executor<'src, T>,
    ) -> Result<'src, Rc<RefCell<Self>>> {
        match self {
            Self::NativeFunction(f) => Ok(Rc::new(f().into())),
            Self::Function(FnVal {
                def: FunDef {
                    pos, params, body, ..
                },
                env,
                is_constructor,
            }) => {
                let got = args.len();
                let expected = params.len();
                if got != expected {
                    return executor.err(ErrorKind::IncorrectArgCount { got, expected });
                }

                let executor = executor.get_inner_executor(Rc::clone(env));
                let executor = executor.inner();

                executor.pos.set(*pos);

                for p in params.iter().rev() {
                    let arg = args.pop().unwrap();

                    executor
                        .environment
                        .borrow_mut()
                        .definitions
                        .insert(p, (*pos, arg));
                }

                let ret = match executor.eval_decls(body) {
                    Ok(..) => Rc::new(Value::Primary(Primary::Nil).into()),
                    Err(Error {
                        kind: ErrorKind::Return(ret),
                        ..
                    }) => ret,
                    Err(e) => return Err(e),
                };

                if *is_constructor {
                    return Ok(executor.environment.borrow().resolve_this());
                }

                Ok(ret)
            }
            Self::Class(class) => {
                let instance = Rc::new(RefCell::new(Self::ClassInstance {
                    c: Rc::clone(class),
                    props: Rc::new(HashMap::new().into()),
                }));

                let mut constructor = None;

                for (name, m) in class.methods.iter() {
                    // We want our own instance of the methods for each class instance
                    let mut m = m.clone();
                    let is_constructor = *name == CONSTRUCTOR_FN_NAME;
                    m.is_constructor = is_constructor;

                    let mut env = m.env.borrow().clone();
                    env.this = Some(Rc::clone(&instance));
                    m.env = Rc::new(env.into());
                    let method_with_this = Value::Function(m);
                    let method_with_this = Rc::new(method_with_this.into());

                    if is_constructor {
                        constructor = Some(Rc::clone(&method_with_this));
                    }

                    match &*instance.borrow() {
                        Self::ClassInstance { props, .. } => {
                            props.borrow_mut().insert(name, (0, method_with_this))
                        }

                        _ => unreachable!(),
                    };
                }

                if let Some(constructor) = constructor {
                    constructor.borrow().call(args, executor)?;
                } else if !args.is_empty() {
                    return executor.err(ErrorKind::IncorrectArgCount {
                        got: args.len(),
                        expected: 0,
                    });
                }

                Ok(instance)
            }
            Self::Primary(..) | Self::ClassInstance { .. } | Self::Map(..) => {
                executor.err(ErrorKind::NotCallable)
            }
        }
    }

    fn access<T: Write>(
        &self,
        key: &'src str,
        executor: &Executor<'src, T>,
    ) -> Result<'src, Rc<RefCell<Value<'src>>>> {
        match self {
            Self::ClassInstance { props, .. } => {
                let props = props.borrow();
                let val = props
                    .get(key)
                    .map(|(_, val)| val)
                    .ok_or_else(|| executor.err_inner(ErrorKind::UndefinedProperty(key)))?;

                let val = match &*val.borrow() {
                    Value::Function(..) => Rc::new(val.borrow().clone().into()),
                    _ => Rc::clone(val),
                };

                Ok(val)
            }
            _ => executor.err(ErrorKind::OnlyInstancesHave("properties")),
        }
    }

    fn set<T: Write>(
        &self,
        key: &'src str,
        value: Rc<RefCell<Value<'src>>>,
        executor: &Executor<'src, T>,
    ) -> Result<'src, ()> {
        match self {
            Self::ClassInstance { props, .. } => {
                props.borrow_mut().insert(key, (executor.pos.get(), value));

                Ok(())
            }
            _ => executor.err(ErrorKind::OnlyInstancesHave("fields")),
        }
    }

    fn truthiness(&self) -> bool {
        !matches!(self, Self::Primary(Primary::Nil | Primary::Bool(false)))
    }

    fn as_num<T: Write>(&self, executor: &Executor<'src, T>) -> Result<'src, f64> {
        match self {
            Self::Primary(Primary::Number(n)) => Ok(n.into()),
            _ => executor.err(ErrorKind::MustBeNumber),
        }
    }

    fn as_str(&self) -> Option<&std::borrow::Cow<'src, str>> {
        match self {
            Self::Primary(Primary::String(s)) => Some(s),
            _ => None,
        }
    }
}

impl<'src> From<Primary<'src>> for Value<'src> {
    fn from(value: Primary<'src>) -> Self {
        Value::Primary(value)
    }
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primary(p) => write!(f, "{p}"),
            Self::NativeFunction(..) => write!(f, "<native fn>"),
            Self::Function(FnVal {
                def: FunDef { name, .. },
                ..
            }) => {
                write!(f, "<fn {name}>")
            }
            Self::Class(c) => write!(f, "{}", c.name),
            Self::ClassInstance { c, .. } => write!(f, "{} instance", c.name),
            Self::Map(..) => write!(f, "<map>"),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Environment<'src> {
    /// `None` when the environment has no parent. Ie. the global environment
    parent: Option<Rc<RefCell<Self>>>,
    this: Option<Rc<RefCell<Value<'src>>>>,
    spr: Option<Rc<Class<'src>>>,
    definitions: HashMap<&'src str, (usize, Rc<RefCell<Value<'src>>>)>,
}

impl<'src> Environment<'src> {
    fn resolve<T: Write>(
        &self,
        ident: &'src str,
        executor: &Executor<'src, T>,
    ) -> Result<'src, Rc<RefCell<Value<'src>>>> {
        if let Some((pos, var)) = self.definitions.get(ident) {
            if executor.pos.get() >= *pos {
                return Ok(Rc::clone(var));
            }
        }

        if let Some(p) = &self.parent {
            return p.borrow().resolve(ident, executor);
        }

        executor.err(ErrorKind::UndefinedVariable(ident))
    }

    fn resolve_this(&self) -> Rc<RefCell<Value<'src>>> {
        if let Some(this) = &self.this {
            return Rc::clone(this);
        }

        return self.parent
            .as_ref()
            .expect("bug: this wasn't defined in current env, so there must be a parent env where its defined, but the parent wasn't defined")
            .borrow()
            .resolve_this();
    }

    fn resolve_super<T: Write>(
        &self,
        executor: &Executor<'src, T>,
        method: &'src str,
    ) -> Result<'src, Rc<RefCell<Value<'src>>>> {
        if let Some(spr) = &self.spr {
            if let Some(method) = spr.methods.get(method) {
                let method = method.clone();
                method.env.borrow_mut().this = Some(self.resolve_this());
                return Ok(Rc::new(Value::Function(method).into()));
            }

            return executor.err(ErrorKind::UndefinedProperty(method));
        };

        self.parent
            .as_ref()
            .expect("bug: super wasn't defined in current env, so there must be a parent env where its defined, but the parent wasn't defined")
            .borrow()
            .resolve_super(executor, method)
    }
}

pub struct Executor<'src, T> {
    program: &'src [Decl<'src>],
    environment: Rc<RefCell<Environment<'src>>>,
    line: Cell<usize>,
    pos: Cell<usize>,
    stdout: Rc<RefCell<T>>,
}

impl<'src> Executor<'src, std::io::Stdout> {
    pub fn with_stdout(program: &'src [Decl<'src>]) -> Self {
        Self::new(program, std::io::stdout())
    }
}

impl<'src, T: Write> Executor<'src, T> {
    pub fn new(program: &'src [Decl<'src>], stdout: T) -> Self {
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

        globals.insert("clock", (0, Rc::new(Value::NativeFunction(clock).into())));

        let stdout = Rc::new(stdout.into());

        Self {
            program,
            environment: Rc::new(
                Environment {
                    parent: None,
                    this: None,
                    spr: None,
                    definitions: globals,
                }
                .into(),
            ),
            line: 0.into(),
            pos: 0.into(),
            stdout,
        }
    }

    fn err_inner(&self, kind: ErrorKind<'src>) -> Error<'src> {
        Error::new(self.line.get(), kind)
    }

    fn err<E>(&self, kind: ErrorKind<'src>) -> Result<'src, E> {
        Err(self.err_inner(kind))
    }

    fn print_value(p: &Value<'src>) -> String {
        match p {
            Value::Primary(Primary::Number(n)) => format!("{}", Into::<f64>::into(n)),
            p => format!("{p}"),
        }
    }

    pub fn eval(&self) -> Result<'src, String> {
        let expr = match self.program.first().unwrap().kind() {
            DeclKind::Expr(expr) => Some(expr),
            DeclKind::Stmt(d) => match d.kind() {
                StmtKind::Expr(e) => Some(e),
                _ => None,
            },
            _ => None,
        };

        let expr = expr.expect("eval only supports programs with one expression");

        Ok(Self::print_value(&self.eval_expr(expr)?.borrow()))
    }

    pub fn run(&self) -> Result<'src, ()> {
        for decl in self.program {
            self.eval_decl(decl)?;
        }

        Ok(())
    }

    fn set_line<A>(&self, node: &'src AstNode<A>) {
        self.line.set(node.line());
        self.pos.set(node.pos());
    }

    fn get_inner_executor(&self, environment: Rc<RefCell<Environment<'src>>>) -> Self {
        Self {
            program: self.program,
            environment,
            line: self.line.clone(),
            pos: self.pos.clone(),
            stdout: Rc::clone(&self.stdout),
        }
    }

    fn inner(&self) -> Self {
        let parent = Rc::clone(&self.environment);

        let inner = self.get_inner_executor(Rc::new(
            Environment {
                parent: Some(Rc::clone(&parent)),
                this: None,
                spr: None,
                definitions: HashMap::new(),
            }
            .into(),
        ));

        inner
    }

    fn eval_var_decl(&self, var_decl: &'src VarDecl<'src>) -> Result<'src, ()> {
        let VarDecl { name, value } = var_decl;
        let pos_and_value = match value {
            Some(v) => (v.pos(), self.eval_expr(v)?.clone()),
            None => (self.pos.get(), Rc::new(Value::Primary(Primary::Nil).into())),
        };

        self.environment
            .borrow_mut()
            .definitions
            .insert(name, pos_and_value);

        Ok(())
    }

    fn get_fun_value(&self, decl: &'src FunDecl<'src>) -> FnVal<'src> {
        let FunDecl { name, params, body } = decl;
        let parent = Some(Rc::clone(&self.environment));
        FnVal {
            def: FunDef {
                pos: self.pos.get(),
                name,
                params,
                body: body.kind().decls(),
            },
            env: Rc::new(
                Environment {
                    definitions: HashMap::new(),
                    parent,
                    this: None,
                    spr: None,
                }
                .into(),
            ),
            is_constructor: false,
        }
    }

    fn eval_decl(&self, decl: &'src Decl<'src>) -> Result<'src, ()> {
        self.set_line(decl);
        match decl.kind() {
            DeclKind::Expr(e) => {
                self.eval_expr(e)?;
            }
            DeclKind::Stmt(s) => {
                self.eval_stmt(s)?;
            }
            DeclKind::Var(v) => self.eval_var_decl(v)?,
            DeclKind::Fun(decl) => {
                let is_global = self.environment.borrow().parent.is_none();
                self.environment.borrow_mut().definitions.insert(
                    decl.name,
                    (
                        // Allow functions in the global scope to be accessed anywhere, if the fun
                        // has been defined
                        if is_global {
                            0
                        } else {
                            // Otherwise treat function as regular variableOtherwise treat function
                            // as regular variable
                            self.pos.get()
                        },
                        Rc::new(Value::Function(self.get_fun_value(decl)).into()),
                    ),
                );
            }
            DeclKind::Class { name, spr, methods } => {
                let spr = match spr {
                    Some(spr) => {
                        let spr = self.environment.borrow().resolve(spr, self)?;
                        let spr = spr.borrow();

                        match &*spr {
                            Value::Class(c) => Some(Rc::clone(c)),
                            _ => return self.err(ErrorKind::SuperClassMustBeAClass),
                        }
                    }
                    None => None,
                };

                let mut class_hierarchy = Vec::new();

                {
                    let mut spr_helper = &spr;

                    while let Some(c) = spr_helper {
                        class_hierarchy.push(c);
                        spr_helper = &c.spr;
                    }
                }

                let mut methods: HashMap<_, _> = methods
                    .iter()
                    .map(|decl| {
                        let val = self.get_fun_value(decl);

                        val.env.borrow_mut().spr = spr.as_ref().map(Rc::clone);

                        (decl.name, val)
                    })
                    .collect();

                for c in class_hierarchy {
                    for (method_name, val) in &c.methods {
                        // We are looping from child class up the inheritance tree
                        // So we prefer the methods from child classes
                        // To enable method overriding
                        if methods.contains_key(method_name) {
                            continue;
                        }

                        methods.insert(method_name, val.clone());
                    }
                }

                self.environment.borrow_mut().definitions.insert(
                    name,
                    (
                        self.pos.get(),
                        Rc::new(Value::Class(Rc::new(Class { name, spr, methods })).into()),
                    ),
                );
            }
        };

        Ok(())
    }

    fn eval_decls(&self, decls: &'src [Decl<'src>]) -> Result<'src, ()> {
        for d in decls {
            self.eval_decl(d)?;
        }

        Ok(())
    }

    fn eval_block(&self, decls: &'src [Decl<'src>]) -> Result<'src, ()> {
        let inner = self.inner();

        inner.eval_decls(decls)?;

        Ok(())
    }

    fn eval_stmt(&self, stmt: &'src Stmt<'src>) -> Result<'src, ()> {
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
                let inner = self.inner();

                if let Some(begin) = begin {
                    match begin {
                        ForBegin::Expr(e) => {
                            inner.eval_expr(e)?;
                        }
                        ForBegin::VarDecl(v) => inner.eval_var_decl(v)?,
                    }
                }

                while match condition {
                    Some(c) => inner.eval_expr(c)?.borrow().truthiness(),
                    None => true,
                } {
                    inner.eval_stmt(body)?;
                    if let Some(after_iter) = after_iter {
                        inner.eval_expr(after_iter)?;
                    }
                }
            }
            StmtKind::If {
                condition,
                body,
                el,
            } => {
                if self.eval_expr(condition)?.borrow().truthiness() {
                    self.eval_stmt(body)?;
                } else if let Some(el) = el {
                    self.eval_stmt(el)?;
                }
            }
            StmtKind::While { condition, body } => {
                while self.eval_expr(condition)?.borrow().truthiness() {
                    self.eval_stmt(body)?;
                }
            }
            StmtKind::Print(expr) => {
                let val = self.eval_expr(expr)?;
                let print = Self::print_value(&val.borrow());
                writeln!(self.stdout.borrow_mut(), "{print}")
                    .map_err(|io| self.err_inner(ErrorKind::Io(io)))?;
            }
            StmtKind::Return(ret) => {
                let ret = if let Some(ret) = ret {
                    self.eval_expr(ret)?
                } else {
                    Rc::new(RefCell::new(Primary::Nil.into()))
                };
                return self.err(ErrorKind::Return(ret));
            }
            StmtKind::Block(b) => self.eval_block(b.kind().decls())?,
        };

        Ok(())
    }

    fn eval_expr(&self, expr: &'src Expr<'src>) -> Result<'src, Rc<RefCell<Value<'src>>>> {
        self.set_line(expr);

        let v = match expr.kind() {
            ExprKind::Assign { call, ident, val } => match call {
                Some(call) => {
                    let c = self.eval_expr(call)?;
                    let val = self.eval_expr(val)?;

                    c.borrow().set(ident, Rc::clone(&val), self)?;

                    val
                }
                None => {
                    let val = self.eval_expr(val)?;

                    self.environment
                        .borrow()
                        .resolve(ident, self)?
                        .replace(val.borrow().clone());

                    val
                }
            },
            ExprKind::Or(a, b) => {
                let a = self.eval_expr(a)?;
                if a.borrow().truthiness() {
                    a
                } else {
                    self.eval_expr(b)?
                }
            }
            ExprKind::And(a, b) => {
                let a = self.eval_expr(a)?;

                if a.borrow().truthiness() {
                    self.eval_expr(b)?
                } else {
                    a
                }
            }
            ExprKind::Eq(a, op, b) => {
                let a = self.eval_expr(a)?;
                let b = self.eval_expr(b)?;

                let res = {
                    let a = a.borrow();
                    let b = b.borrow();

                    match (&*a, &*b) {
                        (Value::Primary(a), Value::Primary(b)) => match op {
                            EqOp::Eq => a == b,
                            EqOp::Neq => a != b,
                        },
                        _ => false,
                    }
                };

                let res = res || a.as_ptr() == b.as_ptr();

                Rc::new(RefCell::new(Primary::Bool(res).into()))
            }
            ExprKind::Cmp(a, op, b) => {
                let (Ok(a), Ok(b)) = (
                    self.eval_expr(a)?.borrow().as_num(self),
                    self.eval_expr(b)?.borrow().as_num(self),
                ) else {
                    return self.err(ErrorKind::BothMustBeNumbers);
                };

                let res = match op {
                    CmpOp::Gte => a >= b,
                    CmpOp::Gt => a > b,
                    CmpOp::Lte => a <= b,
                    CmpOp::Lt => a < b,
                };

                Rc::new(RefCell::new(Primary::Bool(res).into()))
            }
            ExprKind::Term(a, op, b) => {
                let a = self.eval_expr(a)?;
                let b = self.eval_expr(b)?;
                let res = match op {
                    TermOp::Add => {
                        if let (Some(a), Some(b)) = (a.borrow().as_str(), b.borrow().as_str()) {
                            Primary::String(Cow::Owned(a.clone().into_owned() + b))
                        } else if let (Ok(a), Ok(b)) =
                            (a.borrow().as_num(self), b.borrow().as_num(self))
                        {
                            Primary::Number((a + b).into())
                        } else {
                            return self.err(ErrorKind::BothMustBeNumbersOrStrings);
                        }
                    }
                    TermOp::Sub => {
                        if let (Ok(a), Ok(b)) = (a.borrow().as_num(self), b.borrow().as_num(self)) {
                            Primary::Number((a - b).into())
                        } else {
                            return self.err(ErrorKind::BothMustBeNumbers);
                        }
                    }
                };

                Rc::new(RefCell::new(res.into()))
            }
            ExprKind::Factor(a, op, b) => {
                let (Ok(a), Ok(b)) = (
                    self.eval_expr(a)?.borrow().as_num(self),
                    self.eval_expr(b)?.borrow().as_num(self),
                ) else {
                    return self.err(ErrorKind::BothMustBeNumbers);
                };

                let res = match op {
                    FactorOp::Div => a / b,
                    FactorOp::Mul => a * b,
                };

                Rc::new(RefCell::new(Primary::Number(res.into()).into()))
            }
            ExprKind::Unary(op, expr) => Rc::new(RefCell::new(match op {
                UnaryOp::Not => Primary::Bool(!self.eval_expr(expr)?.borrow().truthiness()).into(),
                UnaryOp::Neg => {
                    Primary::Number((-self.eval_expr(expr)?.borrow().as_num(self)?).into()).into()
                }
            })),
            ExprKind::Call { callee, args } => {
                let mut arg_values = Vec::new();

                for a in args {
                    arg_values.push(self.eval_expr(a)?)
                }

                self.eval_expr(callee)?.borrow().call(arg_values, self)?
            }
            ExprKind::Access(obj, key) => self.eval_expr(obj)?.borrow().access(key, self)?,
            ExprKind::Ident(ident) => {
                let val = self.environment.borrow().resolve(ident, self)?;

                // Pass classes by reference and everything else by value
                let val = match &*val.borrow() {
                    Value::Primary(..) => Rc::new(val.borrow().clone().into()),
                    _ => Rc::clone(&val),
                };

                val
            }
            ExprKind::Group(i) => self.eval_expr(i)?,
            ExprKind::Primary(p) => Rc::new(RefCell::new(p.clone().into())),
            ExprKind::This => self.environment.borrow().resolve_this(),
            ExprKind::Super(method) => self.environment.borrow().resolve_super(self, method)?,
        };

        Ok(v)
    }
}
