use std::fmt;
use std::path::PathBuf;

use crate::compiler::Type;
use crate::tokenizer::Token;
use crate::vm::{Op, Value};

#[derive(Debug, Clone)]
pub enum ErrorKind {
    TypeError(Op, Vec<Type>),
    RuntimeTypeError(Op, Vec<Value>),
    Assert,
    InvalidProgram,
    Unreachable,

    SyntaxError(usize, Token),
}

#[derive(Debug, Clone)]
pub struct Error {
    pub kind: ErrorKind,
    pub file: PathBuf,
    pub line: usize,
    pub message: Option<String>,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::TypeError(op, types) => {
                let types = types
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}, {:?}", a, v) });
                write!(f, "Cannot apply {:?} to types {}", op, types)
            }
            ErrorKind::RuntimeTypeError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}, {:?}", a, v) });
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            ErrorKind::Assert => {
                write!(f, "Assertion failed.")
            }
            ErrorKind::SyntaxError(line, token) => {
                write!(f, "Syntax error on line {} at token {:?}", line, token)
            }
            ErrorKind::Unreachable => {
                write!(f, "Reached unreachable code.")
            }
            ErrorKind::InvalidProgram => {
                write!(f, "[!!!] Invalid program")
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match &self.message {
            Some(s) => format!("\n{}", s),
            None => String::from(""),
        };
        write!(f, "{:?}:{} {}{}", self.file, self.line, self.kind, message)
    }
}

