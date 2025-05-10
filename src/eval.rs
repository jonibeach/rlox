use crate::parser::{CmpOp, EqOp, Expr, FactorOp, Primary, TermOp, UnaryOp};

#[derive(Debug)]
pub enum Error {
    InvalidMathOperand,
    CannotConvertToString,
}

pub type Result<T> = std::result::Result<T, Error>;

impl<'src> Expr<'src> {
    pub fn eval(&self) -> Result<String> {
        eprintln!("eval {self}");
        let res = match self {
            Self::Equality(..) => self.truthiness()?.to_string(),
            Self::Cmp(..) => self.truthiness()?.to_string(),
            Self::Term(..) => self
                .as_str()
                .or_else(|_| self.as_num().map(|n| n.to_string()))?,
            Self::Factor(..) => self.as_num()?.to_string(),
            Self::Unary(op, i) => match op {
                UnaryOp::Not => (!i.truthiness()?).to_string(),
                UnaryOp::Neg => (-i.as_num()?).to_string(),
            },
            Self::Primary(p) => match p {
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
        match self {
            Self::Equality(..) => Err(Error::InvalidMathOperand),
            Self::Cmp(..) => Err(Error::InvalidMathOperand),
            Self::Term(a, op, b) => match op {
                TermOp::Add => Ok(a.as_num()? + b.as_num()?),
                TermOp::Sub => Ok(a.as_num()? - b.as_num()?),
            },
            Self::Factor(a, op, b) => match op {
                FactorOp::Div => Ok(a.as_num()? / b.as_num()?),
                FactorOp::Mul => Ok(a.as_num()? * b.as_num()?),
            },
            Self::Unary(op, i) => match op {
                UnaryOp::Not => Err(Error::InvalidMathOperand),
                UnaryOp::Neg => Ok(-i.as_num()?),
            },
            Self::Primary(p) => match p {
                Primary::Bool(_) => Err(Error::InvalidMathOperand),
                Primary::Group(i) => i.as_num(),
                Primary::Nil => Err(Error::InvalidMathOperand),
                Primary::Number(n) => Ok(n.into()),
                Primary::String(_) => Err(Error::InvalidMathOperand),
            },
        }
    }

    fn as_str(&self) -> Result<String> {
        eprintln!("as str {self}");
        match self {
            Self::Term(a, op, b) => {
                if let (Ok(a), Ok(b), TermOp::Add) = (a.as_str(), b.as_str(), op) {
                    eprintln!("both valid strings");
                    return Ok(a + &b);
                }
            }
            Self::Primary(p) => match p {
                Primary::String(s) => return Ok(s.to_string()),
                Primary::Group(i) => return Ok(i.as_str()?),
                _ => {}
            },
            _ => {}
        };

        Err(Error::CannotConvertToString)
    }

    fn truthiness(&self) -> Result<bool> {
        eprintln!("truthiness {self}");
        let res = match self {
            Self::Equality(a, op, b) => {
                if let Ok(a) = a.as_num() {
                    let Ok(b) = b.as_num() else { return Ok(false) };

                    match op {
                        EqOp::Eq => a == b,
                        EqOp::Neq => a != b,
                    }
                } else if let Ok(a) = a.as_str() {
                    let Ok(b) = b.as_str() else { return Ok(false) };

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
            Self::Cmp(a, op, b) => match op {
                CmpOp::Gt => a.as_num()? > b.as_num()?,
                CmpOp::Gte => a.as_num()? >= b.as_num()?,
                CmpOp::Lt => a.as_num()? < b.as_num()?,
                CmpOp::Lte => a.as_num()? <= b.as_num()?,
            },
            Self::Term(..) => true,
            Self::Factor(..) => true,
            Self::Unary(op, i) => match op {
                UnaryOp::Not => !i.truthiness()?,
                UnaryOp::Neg => i.truthiness()?,
            },
            Self::Primary(p) => match p {
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
