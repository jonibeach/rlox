use crate::parser::{Expr, FactorOp, Primary, TermOp, UnaryOp};

#[derive(Debug)]
pub enum Error {
    InvalidMathOperands,
}

pub type Result<T> = std::result::Result<T, Error>;

impl<'src> Expr<'src> {
    pub fn eval(&self) -> Result<String> {
        let res = match self {
            Self::Equality(..) => unimplemented!(),
            Self::Cmp(..) => unimplemented!(),
            Self::Term(..) => self.as_num()?.to_string(),
            Self::Factor(..) => self.as_num()?.to_string(),
            Self::Unary(op, _) => match op {
                UnaryOp::Not => unimplemented!(),
                UnaryOp::Neg => self.as_num()?.to_string(),
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
        match self {
            Self::Equality(..) => unimplemented!(),
            Self::Cmp(..) => unimplemented!(),
            Self::Term(a, op, b) => match op {
                TermOp::Add => Ok(a.as_num()? + b.as_num()?),
                TermOp::Sub => Ok(a.as_num()? - b.as_num()?),
            },
            Self::Factor(a, op, b) => match op {
                FactorOp::Div => Ok(a.as_num()? / b.as_num()?),
                FactorOp::Mul => Ok(a.as_num()? * b.as_num()?),
            },
            Self::Unary(op, i) => match op {
                UnaryOp::Not => unimplemented!(),
                UnaryOp::Neg => Ok(-i.as_num()?),
            },
            Self::Primary(p) => match p {
                Primary::Bool(_) => Err(Error::InvalidMathOperands),
                Primary::Group(i) => i.as_num(),
                Primary::Nil => Err(Error::InvalidMathOperands),
                Primary::Number(n) => Ok(n.into()),
                Primary::String(_) => Err(Error::InvalidMathOperands),
            },
        }
    }
}
