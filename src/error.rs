use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::PathBuf;

use owo_colors::OwoColorize;

use crate::{Op, Value};
use crate::Type;
use crate::tokenizer::Token;

#[derive(Debug, Clone)]
pub enum ErrorKind {
    TypeError(Op, Vec<Type>),
    TypeMismatch(Type, Type),
    CannotInfer(Type, Type),
    ArgumentType(Vec<Type>, Vec<Type>),
    IndexError(Value, Type),

    /// (External function, parameters)
    ExternTypeMismatch(String, Vec<Type>),
    ValueError(Op, Vec<Value>),
    UnknownField(Value, String),
    ArgumentCount(usize, usize),

    /// (Indexed value, length, index)
    IndexOutOfBounds(Value, usize, usize),

    AssertFailed,
    InvalidProgram,
    Unreachable,

    /// (line, token)
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
                    .fold(String::new(), |a, v| { format!("{}{:?}, ", a, v) });
                write!(f, "Cannot apply {:?} to types {}", op, types)
            }
            ErrorKind::TypeMismatch(a, b) => {
                write!(f, "Expected '{:?}' and got '{:?}'.", a, b)
            }
            ErrorKind::CannotInfer(a, b) => {
                write!(f, "Failed to infer type '{:?}' from '{:?}'.", a, b)
            }
            ErrorKind::ArgumentType(a, b) => {
                let expected = a
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}{:?}, ", a, v) });
                let given = b
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}{:?}, ", a, v) });
                write!(f, "Argument types do not match, expected [{:?}] but got [{:?}]",
                       expected, given)
            }
            ErrorKind::IndexOutOfBounds(value, len, slot) => {
                write!(f, "Failed to index for {:?} - length is {} but index is {}",
                       value, len, slot)
            }
            ErrorKind::ExternTypeMismatch(name, types) => {
                write!(f, "Extern function '{}' doesn't accept argument(s) with type(s) {:?}",
                       name, types)
            }
            ErrorKind::ValueError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| { format!("{}{:?}, ", a, v) });
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            ErrorKind::AssertFailed => {
                write!(f, "Assertion failed")
            }
            ErrorKind::SyntaxError(line, token) => {
                write!(f, "Syntax Error on line {} at token {:?}", line, token)
            }
            ErrorKind::Unreachable => {
                write!(f, "Reached unreachable code.")
            }
            ErrorKind::InvalidProgram => {
                write!(f, "{}", "[!!] Invalid program [!!]".bold())
            }
            ErrorKind::IndexError(value, slot) => {
                write!(f, "Cannot index value '{:?}' with type '{:?}'.", value, slot)
            }
            ErrorKind::UnknownField(obj, field) => {
                write!(f, "Cannot find field '{}' on {:?}", field, obj)
            }
            ErrorKind::ArgumentCount(expected, given) => {
                write!(f, "Incorrect argument count, expected {} but got {}.",
                       expected, given)
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prompt = "     ";
        let message = match &self.message {
            Some(s) => format!("\n{} {}", prompt, s),
            None => String::from(""),
        };

        let line = if let Ok(file) = File::open(&self.file) {
            io::BufReader::new(file).lines().enumerate()
                    .filter(|(n, _)| self.line <= *n + 3 && *n + 3 <= self.line + 2)
                    .fold(String::from("\n"), |a, (n, l)| format!("{} {:3} | {}\n", a, (n + 1).blue(), l.unwrap()))
        } else {
            String::new()
        };

        write!(f, "{} {}:{}\n{} {}{}{}", "ERROR".red(),
               self.file.display().blue(), self.line.blue(), prompt, self.kind, message, line)
    }
}

