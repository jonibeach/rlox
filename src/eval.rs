use std::fmt::Display;

use crate::parser::{CmpOp, EqOp, Expr, ExprKind, FactorOp, Primary, TermOp, UnaryOp};

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    MustBeNumber,
    BothMustBeNumbers,
    BothMustBeNumbersOrStrings,
}

#[derive(Debug, PartialEq)]
pub struct Error {
    line: usize,
    kind: ErrorKind,
}

impl Error {
    pub fn new(line: usize, kind: ErrorKind) -> Self {
        Self { line, kind }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self.kind {
            ErrorKind::MustBeNumber => "Operand must be a number.",
            ErrorKind::BothMustBeNumbers => "Operands must be numbers.",
            ErrorKind::BothMustBeNumbersOrStrings => "Operands must be two numbers or two strings.",
        };

        writeln!(f, "{msg}")?;
        write!(f, "[line {}]", self.line + 1)
    }
}
pub type Result<T> = std::result::Result<T, Error>;

impl<'src> Expr<'src> {
    fn err_inner(&self, kind: ErrorKind) -> Error {
        Error {
            line: self.line(),
            kind,
        }
    }
    fn err<T>(&self, kind: ErrorKind) -> Result<T> {
        Err(self.err_inner(kind))
    }

    pub fn eval(&self) -> Result<String> {
        eprintln!("eval {self}");
        let res = match self.kind() {
            ExprKind::Equality(..) => self.truthiness()?.to_string(),
            ExprKind::Cmp(..) => self.truthiness()?.to_string(),
            ExprKind::Term(..) => self.as_num().map(|n| n.to_string()).or_else(|_| {
                self.as_string()
                    .ok_or_else(|| self.err_inner(ErrorKind::BothMustBeNumbersOrStrings))
            })?,
            ExprKind::Factor(..) => self.as_num()?.to_string(),
            ExprKind::Unary(op, i) => match op {
                UnaryOp::Not => (!i.truthiness()?).to_string(),
                UnaryOp::Neg => (-i.as_num()?).to_string(),
            },
            ExprKind::Primary(p) => match p {
                Primary::Bool(bool) => bool.to_string(),
                Primary::Group(i) => return i.eval(),
                Primary::Nil => String::from("nil"),
                Primary::Number(_) => self.as_num()?.to_string(),
                Primary::String(s) => s.to_string(),
            },
        };

        Ok(res)
    }

    fn as_num(&self) -> Result<f64> {
        eprintln!("as num {self}");
        match self.kind() {
            ExprKind::Equality(..) => self.err(ErrorKind::MustBeNumber),
            ExprKind::Cmp(..) => self.err(ErrorKind::MustBeNumber),
            ExprKind::Term(a, op, b) => match op {
                TermOp::Add => Ok(a.as_num()? + b.as_num()?),
                TermOp::Sub => Ok(a.as_num()? - b.as_num()?),
            },
            ExprKind::Factor(a, op, b) => {
                if let (Ok(a), Ok(b)) = (a.as_num(), b.as_num()) {
                    Ok(match op {
                        FactorOp::Mul => a * b,
                        FactorOp::Div => a / b,
                    })
                } else {
                    self.err(ErrorKind::BothMustBeNumbers)
                }
            }
            ExprKind::Unary(op, i) => match op {
                UnaryOp::Not => self.err(ErrorKind::MustBeNumber),
                UnaryOp::Neg => Ok(-i.as_num()?),
            },
            ExprKind::Primary(p) => match p {
                Primary::Group(i) => i.as_num(),
                Primary::Number(n) => Ok(n.into()),
                _ => self.err(ErrorKind::MustBeNumber),
            },
        }
    }

    fn as_string(&self) -> Option<String> {
        eprintln!("as str {self}");
        match self.kind() {
            ExprKind::Term(a, op, b) => {
                if let (Some(a), Some(b), TermOp::Add) = (a.as_string(), b.as_string(), op) {
                    eprintln!("both valid strings");
                    return Some(a + &b);
                }
            }
            ExprKind::Primary(p) => match p {
                Primary::String(s) => return Some(s.to_string()),
                Primary::Group(i) => return Some(i.as_string()?),
                _ => {}
            },
            _ => {}
        };

        None
    }

    fn truthiness(&self) -> Result<bool> {
        eprintln!("truthiness {self}");
        let res = match self.kind() {
            ExprKind::Equality(a, op, b) => {
                if let Ok(a) = a.as_num() {
                    let Ok(b) = b.as_num() else { return Ok(false) };

                    match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    }
                } else if let Some(a) = a.as_string() {
                    let Some(b) = b.as_string() else {
                        return Ok(false);
                    };

                    match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    }
                } else {
                    match op {
                        EqOp::Eq => a.truthiness()? == b.truthiness()?,
                        EqOp::Neq => a.truthiness()? == b.truthiness()?,
                    }
                }
            }
            ExprKind::Cmp(a, op, b) => match op {
                CmpOp::Gt => a.as_num()? > b.as_num()?,
                CmpOp::Gte => a.as_num()? >= b.as_num()?,
                CmpOp::Lt => a.as_num()? < b.as_num()?,
                CmpOp::Lte => a.as_num()? <= b.as_num()?,
            },
            ExprKind::Term(..) => true,
            ExprKind::Factor(..) => true,
            ExprKind::Unary(op, i) => match op {
                UnaryOp::Not => !i.truthiness()?,
                UnaryOp::Neg => i.truthiness()?,
            },
            ExprKind::Primary(p) => match p {
                Primary::Bool(i) => *i,
                Primary::Group(i) => i.truthiness()?,
                Primary::Nil => false,
                Primary::Number(..) => true,
                Primary::String(..) => true,
            },
        };

        Ok(res)
    }
}
