use std::fmt;
use std::path::PathBuf;
use crate::vm::{Op, Value};

#[derive(Debug)]
pub enum ErrorKind {
    TypeError(Op, Vec<Value>),
    AssertFailed(Value, Value),
    SyntaxError(usize),
}

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub file: PathBuf,
    pub line: usize,
    pub message: Option<String>,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::TypeError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}, {:?}", a, v) });
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            ErrorKind::AssertFailed(a, b) => {
                write!(f, "Assertion failed, {:?} != {:?}.", a, b)
            }
            ErrorKind::SyntaxError(line) => {
                write!(f, "Syntax error on line {}", line)
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
        write!(f, "{:?}:{} [Runtime Error] {}{}", self.file, self.line, self.kind, message)
    }
}

