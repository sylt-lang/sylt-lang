use owo_colors::OwoColorize;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

use crate::{tokenizer::Token, Op, Type, Value};

fn source_line_at(file: &Path, line: Option<usize>) -> Option<String> {
    match (File::open(file), line) {
        (Ok(file), Some(line)) => {
            Some(io::BufReader::new(file)
                .lines()
                .enumerate()
                .filter(|(n, _)| line <= *n + 3 && *n + 3 <= line + 2)
                .fold(String::from("\n"), |a, (n, l)| {
                    format!("{} {:3} | {}\n", a, (n + 1).blue(), l.unwrap())
                })
            )
        }
        _ => None,
    }
}

fn file_line_display(file: &Path, line: Option<usize>) -> String {
    format!("{}:{}",
        file.display().blue(),
        if let Some(line) = line {
            line.blue().to_string()
        } else {
            "??".blue().to_string()
        }
    )
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
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
}

#[derive(Clone, Copy, Debug)]
pub enum RuntimePhase {
    Runtime,
    Typecheck,
}

impl fmt::Display for RuntimePhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimePhase::Runtime => write!(f, "runtime"),
            RuntimePhase::Typecheck => write!(f, "typecheck"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Error {
    RuntimeError {
        kind: RuntimeError,
        phase: RuntimePhase,
        file: PathBuf,
        line: usize,
        message: Option<String>,
    },

    SyntaxError {
        file: PathBuf,
        line: usize,
        token: Token,
        message: Option<String>,
    },

    GitConflictError {
        file: PathBuf,
        start: usize,
        end: usize,
    },

    FileNotFound(PathBuf),
    NoFileGiven,

    BincodeError,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let indent = "      ";

        match self {
            Error::RuntimeError { kind, phase, file, line, message } => {
                write!(f, "{}: {}", phase.red(), "error".red())?;
                write!(f, "{}\n", file_line_display(file, Some(*line)))?;
                write!(f, "{}{}\n", indent, kind)?;

                if let Some(message) = message {
                    write!(f, "{}{}\n", indent, message)?;
                }
                write!(f, "{}\n",
                    source_line_at(file, Some(*line)).unwrap_or_else(String::new)
                )
            }
            Error::SyntaxError {
                file,
                line,
                token,
                message,
            } => {
                write!(f, "{}: ", "Syntax error".red())?;
                write!(f, "{}\n", file_line_display(file, Some(*line)))?;
                write!(f, "{}Syntax Error on line {} at token {:?}", indent, line, token)?;

                if let Some(message) = message {
                    write!(f, "{}{}\n", indent, message)?;
                }
                write!(f, "{}\n",
                    source_line_at(file, Some(*line)).unwrap_or_else(String::new)
                )
            }
            _ => todo!(),
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::TypeError(op, types) => {
                let types = types
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(f, "Cannot apply {:?} to types {}", op, types)
            }
            RuntimeError::TypeMismatch(a, b) => {
                write!(f, "Expected '{:?}' and got '{:?}'", a, b)
            }
            RuntimeError::CannotInfer(a, b) => {
                write!(f, "Failed to infer type '{:?}' from '{:?}'", a, b)
            }
            RuntimeError::ArgumentType(a, b) => {
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
            RuntimeError::IndexError(value, slot) => {
                write!(f, "Cannot index value '{:?}' with type '{:?}'", value, slot)
            }
            RuntimeError::ExternTypeMismatch(name, types) => {
                write!(
                    f,
                    "Extern function '{}' doesn't accept argument(s) with type(s) {:?}",
                    name, types
                )
            }
            RuntimeError::ValueError(op, values) => {
                let values = values
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(f, "Cannot apply {:?} to values {}", op, values)
            }
            RuntimeError::UnknownField(obj, field) => {
                write!(f, "Cannot find field '{}' on blob {:?}", field, obj)
            }
            RuntimeError::ArgumentCount(expected, given) => {
                write!(
                    f,
                    "Incorrect argument count, expected {} but got {}",
                    expected, given
                )
            }
            RuntimeError::IndexOutOfBounds(value, len, slot) => {
                write!(
                    f,
                    "Failed to index for {:?} - length is {} but index is {}",
                    value, len, slot
                )
            }
            RuntimeError::AssertFailed => {
                write!(f, "Assertion failed")
            }
            RuntimeError::InvalidProgram => {
                write!(f, "{}", "[!!] Invalid program [!!]".bold())
            }
            RuntimeError::Unreachable => {
                write!(f, "Reached unreachable code")
            }
            /*
            RuntimeError::GitConflictError(start_line, end_line) => {
                write!(
                    f,
                    "Git conflict markers found between lines {} and {}",
                    start_line, end_line
                )
            }
            RuntimeError::FileNotFound(path) => {
                write!(f, "File '{}' not found", path.display())
            }
            RuntimeError::NoFileGiven => {
                write!(f, "No file to run")
            }
            */
        }
    }
}

