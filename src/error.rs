use owo_colors::OwoColorize;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

use crate::{tokenizer::Token, Op, Type, Value};

/// Returns the line in the source code and some context before it.
/// Fails if the line can't be found for some reason.
///
/// This logic is shared between most (but not all) errors. It handles
/// the [Option]s as well since that logic is also shared.
fn source_line_at(file: &Option<PathBuf>, line: Option<usize>) -> Option<String> {
    match (file, line) {
        (Some(file), Some(line)) => {
            if let Ok(file) = File::open(file) {
                Some(io::BufReader::new(file)
                   .lines()
                   .enumerate()
                   .filter(|(n, _)| line <= *n + 3 && *n + 3 <= line + 2)
                   .fold(String::from("\n"), |a, (n, l)| {
                       format!("{} {:3} | {}\n", a, (n + 1).blue(), l.unwrap())
                   }))
            } else {
                None
            }
        }
        // This doesn't need to be an error if you want to report an error on a line
        // number without specifying a file.
        (None, Some(_)) => unimplemented!("Line number without corresponding file"),

        // Either only a file or no info at all
        _ => None,
    }
}

fn file_line_display(file: &Option<PathBuf>, line: Option<usize>) -> Option<String> {
    match (file, line) {
        (Some(file), Some(line)) => Some(format!("{}:{}", file.display().blue(), line.blue())),
        // As with source_line_at, might not be an error.
        (None, Some(_)) => unimplemented!("Line number without corresponding file"),
        _ => None,
    }
}

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
    UnknownField(String, String),
    ArgumentCount(usize, usize),

    /// (Indexed value, length, index)
    IndexOutOfBounds(Value, usize, usize),

    AssertFailed,
    InvalidProgram,
    Unreachable,

    /// (line, token)
    SyntaxError(usize, Token),
    /// (start, end)
    GitConflictError(usize, usize),

    FileNotFound(PathBuf),
    NoFileGiven,
}

#[derive(Clone)]
pub enum Error {
    CompileError {
        kind: ErrorKind,
        file: Option<PathBuf>,
        line: Option<usize>,
        message: Option<String>,
    },
    TypecheckError {
        kind: ErrorKind,
        file: PathBuf,
        line: usize,
        message: Option<String>,
    },
    RuntimeError {
        kind: ErrorKind,
        file: PathBuf,
        line: usize,
        message: Option<String>,
    },
    BincodeError,
}

impl Error {
    fn kind(&self) -> ErrorKind {
        match self {
            Error::CompileError     { kind, .. }
            | Error::TypecheckError { kind, .. }
            | Error::RuntimeError   { kind, .. }
            => kind.clone(),
            _ => unimplemented!(),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            //TODO debug_non_exhaustive
            Error::CompileError { kind, .. }
                => write!(f, "CompileError {{ kind: {:?}, .. }}", kind),
            Error::TypecheckError { kind, .. }
                => write!(f, "TypecheckError {{ kind: {:?}, .. }}", kind),
            Error::RuntimeError { kind, .. }
                => write!(f, "RuntimeError {{ kind: {:?}, .. }}", kind),
            Error::BincodeError
                => write!(f, "BincodeError"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prompt = "      ";

        match self {
            Error::CompileError { kind, file, line, message } => {
                let message = match message {
                    Some(s) => format!("{}{}\n", prompt, s),
                    None => String::new(),
                };

                write!(
                    f,
                    "{} {}\n{}\n{}{}",
                    "Compilation error".red(),
                    file_line_display(file, *line).unwrap_or_else(String::new),
                    kind,
                    message,
                    source_line_at(file, *line).unwrap_or_else(String::new),
                )
            }
            _ => todo!(),
        }
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::TypeError(op, types) => {
                let types = types
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(f, "Cannot apply {:?} to types {}", op, types)
            }
            ErrorKind::TypeMismatch(a, b) => {
                write!(f, "Expected '{:?}' and got '{:?}'", a, b)
            }
            ErrorKind::CannotInfer(a, b) => {
                write!(f, "Failed to infer type '{:?}' from '{:?}'", a, b)
            }
            ErrorKind::ArgumentType(a, b) => {
                let expected = a
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                let given = b
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(
                    f,
                    "Argument types do not match, expected [{:?}] but got [{:?}]",
                    expected, given
                )
            }
            ErrorKind::IndexError(value, slot) => {
                write!(f, "Cannot index value '{:?}' with type '{:?}'", value, slot)
            }
            ErrorKind::ExternTypeMismatch(name, types) => {
                write!(
                    f,
                    "Extern function '{}' doesn't accept argument(s) with type(s) {:?}",
                    name, types
                )
            }
            ErrorKind::ValueError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            ErrorKind::UnknownField(obj, field) => {
                write!(f, "Cannot find field '{}' on blob {:?}", field, obj)
            }
            ErrorKind::ArgumentCount(expected, given) => {
                write!(
                    f,
                    "Incorrect argument count, expected {} but got {}",
                    expected, given
                )
            }
            ErrorKind::IndexOutOfBounds(value, len, slot) => {
                write!(
                    f,
                    "Failed to index for {:?} - length is {} but index is {}",
                    value, len, slot
                )
            }
            ErrorKind::AssertFailed => {
                write!(f, "Assertion failed")
            }
            ErrorKind::InvalidProgram => {
                write!(f, "{}", "[!!] Invalid program [!!]".bold())
            }
            ErrorKind::Unreachable => {
                write!(f, "Reached unreachable code")
            }
            ErrorKind::SyntaxError(line, token) => {
                write!(f, "Syntax Error on line {} at token {:?}", line, token)
            }
            ErrorKind::GitConflictError(start_line, end_line) => {
                write!(
                    f,
                    "Git conflict markers found between lines {} and {}",
                    start_line, end_line
                )
            }
            ErrorKind::FileNotFound(path) => {
                write!(f, "File '{}' not found", path.display())
            }
            ErrorKind::NoFileGiven => {
                write!(f, "No file to run")
            }
        }
    }
}

