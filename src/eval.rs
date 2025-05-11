use std::{cell::RefCell, collections::HashMap, fmt::Display, io::Write};

use crate::parser::{AstKind, AstNode, CmpOp, EqOp, FactorOp, Primary, Program, TermOp, UnaryOp};

#[derive(Debug)]
pub enum ErrorKind<'src> {
    MustBeNumber,
    BothMustBeNumbers,
    BothMustBeNumbersOrStrings,
    UndefinedVariable(&'src str),
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

    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }

    pub fn new(line: usize, kind: ErrorKind<'src>) -> Self {
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
            ErrorKind::Io(..) => "IO error".into(),
        };

        writeln!(f, "{msg}")?;
        write!(f, "[line {}]", self.line + 1)
    }
}

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;

pub struct Executor<'src, 'p, T> {
    program: &'p Program<'src>,
    stdout: RefCell<T>,
    global_vars: RefCell<HashMap<&'src str, &'p AstNode<'src>>>,
}

impl<'src, 'p> Executor<'src, 'p, std::io::Stdout>
where
    'p: 'src,
{
    pub fn with_stdout(program: &'p Program<'src>) -> Self {
        Self::new(program, std::io::stdout())
    }
}

impl<'src, 'p, T: Write> Executor<'src, 'p, T>
where
    'p: 'src,
{
    pub fn new(program: &'p Program<'src>, stdout: T) -> Self {
        Self {
            program,
            stdout: stdout.into(),
            global_vars: HashMap::new().into(),
        }
    }

    pub fn eval(&'src self) -> Result<'src, Option<String>> {
        let mut res = None;
        eprintln!("evaling program");
        for declr in self.program.declarations() {
            eprintln!("evaling declr {declr}");
            res = self.eval_node(declr)?;
        }

        Ok(res)
    }

    pub fn run(&'src self) -> Result<'src, ()> {
        self.eval()?;

        Ok(())
    }

    fn err_inner(&self, node: &'p AstNode<'src>, kind: ErrorKind<'src>) -> Error {
        Error::new(node.line(), kind)
    }
    fn err<E>(&self, node: &'p AstNode<'src>, kind: ErrorKind<'src>) -> Result<E> {
        Err(self.err_inner(node, kind))
    }

    fn resolve_var(
        &'src self,
        node: &'p AstNode<'src>,
        ident: &'src str,
    ) -> Result<'src, &'p AstNode<'src>> {
        let global_vars = self.global_vars.borrow();
        let var = *global_vars
            .get(ident)
            .ok_or_else(|| self.err_inner(node, ErrorKind::UndefinedVariable(ident)))?;

        std::mem::drop(global_vars);

        Ok(var)
    }

    fn eval_node(&'src self, node: &'p AstNode<'src>) -> Result<'src, Option<String>> {
        eprintln!("eval {node}");
        let res = match node.kind() {
            AstKind::VarDecl(ident, i) => {
                let mut global_vars = self.global_vars.borrow_mut();
                global_vars.insert(ident, i);
                return Ok(None);
            }
            AstKind::Print(i) => {
                let mut stdout = self.stdout.borrow_mut();
                writeln!(stdout, "{}", self.eval_node(i)?.unwrap_or_default()).map_err(|io| {
                    Error {
                        line: i.line(),
                        kind: ErrorKind::Io(io),
                    }
                })?;
                return Ok(None);
            }
            AstKind::Equality(..) => self.truthiness(node)?.to_string(),
            AstKind::Cmp(..) => self.truthiness(node)?.to_string(),
            AstKind::Term(..) => self.as_num(node).map(|n| n.to_string()).or_else(|_| {
                self.as_string(node)
                    .ok_or_else(|| self.err_inner(node, ErrorKind::BothMustBeNumbersOrStrings))
            })?,
            AstKind::Factor(..) => self.as_num(node)?.to_string(),
            AstKind::Unary(op, i) => match op {
                UnaryOp::Not => (!self.truthiness(i)?).to_string(),
                UnaryOp::Neg => (-self.as_num(i)?).to_string(),
            },
            AstKind::Primary(p) => match p {
                Primary::Bool(bool) => bool.to_string(),
                Primary::Group(i) => return self.eval_node(i),
                Primary::Nil => String::from("nil"),
                Primary::Number(_) => self.as_num(node)?.to_string(),
                Primary::String(s) => s.to_string(),
                Primary::VariableAccess(ident) => {
                    return self.eval_node(self.resolve_var(node, ident)?)
                }
            },
        };

        Ok(Some(res))
    }

    fn as_num(&'src self, node: &'p AstNode<'src>) -> Result<'src, f64> {
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
            AstKind::Primary(p) => match p {
                Primary::Group(i) => self.as_num(i),
                Primary::Number(n) => Ok(n.into()),
                Primary::VariableAccess(ident) => {
                    return self.as_num(self.resolve_var(node, ident)?)
                }
                _ => self.err(node, ErrorKind::MustBeNumber),
            },
            _ => self.err(node, ErrorKind::MustBeNumber),
        }
    }

    fn as_string(&'src self, node: &'p AstNode<'src>) -> Option<String> {
        eprintln!("as str {node}");
        match node.kind() {
            AstKind::Term(a, op, b) => {
                if let (Some(a), Some(b), TermOp::Add) = (self.as_string(a), self.as_string(b), op)
                {
                    eprintln!("both valid strings");
                    return Some(a + &b);
                }
            }
            AstKind::Primary(p) => match p {
                Primary::String(s) => return Some(s.to_string()),
                Primary::Group(i) => return self.as_string(i),
                Primary::VariableAccess(ident) => {
                    return self.as_string(self.resolve_var(node, ident).ok()?)
                }
                _ => {}
            },
            _ => {}
        };

        None
    }

    fn truthiness(&'src self, node: &'p AstNode<'src>) -> Result<'src, bool> {
        eprintln!("truthiness {node}");
        let res = match node.kind() {
            AstKind::VarDecl(..) => true,
            AstKind::Print(..) => true,
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
            AstKind::Primary(p) => match p {
                Primary::Bool(i) => *i,
                Primary::Group(i) => self.truthiness(i)?,
                Primary::Nil => false,
                Primary::Number(..) => true,
                Primary::String(..) => true,
                Primary::VariableAccess(ident) => {
                    self.truthiness(self.resolve_var(node, ident)?)?
                }
            },
        };

        Ok(res)
    }
}
