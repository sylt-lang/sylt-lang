use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::PathBuf;
use owo_colors::OwoColorize;

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
                write!(f, "{} Cannot apply {:?} to types {}", "Type Error".bold(), op, types)
            }
            ErrorKind::RuntimeTypeError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}, {:?}", a, v) });
                write!(f, "{} Cannot apply {:?} to values {}", "Runtime Type Error".bold(), op, values)
            }
            ErrorKind::Assert => {
                write!(f, "{}", "Assertion failed".bold())
            }
            ErrorKind::SyntaxError(line, token) => {
                write!(f, "{} on line {} at token {:?}", "Syntax Error".bold(), line, token)
            }
            ErrorKind::Unreachable => {
                write!(f, "{}", "Unreachable".bold())
            }
            ErrorKind::InvalidProgram => {
                write!(f, "{}", "[!!] Invalid program [!!]".bold())
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match &self.message {
            Some(s) => format!("\n{} {}", ">>>".red(), s),
            None => String::from(""),
        };

        let line = if let Ok(file) = File::open(&self.file) {
            io::BufReader::new(file).lines().enumerate()
                    .filter(|(n, _)| self.line-2 <= *n + 1 && *n + 1 <= self.line)
                    .fold(String::from("\n"), |a, (n, l)| format!("{} {:3} | {}\n", a, (n + 1).blue(), l.unwrap()))
        } else {
            String::new()
        };

        write!(f, "\n<{}> {}:{} {}{}{}\n", "ERR".red(), self.file.display().blue(), self.line.blue(), self.kind, message, line)
    }
}

