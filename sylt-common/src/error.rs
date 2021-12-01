use crate::{Op, Type, Value, FileOrLib, library_source};

use colored::Colorize;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_tokenizer::Span;

static INDENT: &'static str = "      ";

fn write_source_line_from_file_at(f: &mut fmt::Formatter<'_>, file: &Path, line: usize) -> fmt::Result {
    let file = if let Ok(file) = File::open(file) {
        file
    } else {
        return write!(f, "Unable to open file {}", file.display());
    };

    let start_line = (line.saturating_sub(2)).max(1);
    let lines = line + 1 - start_line;

    for (line_num, line) in io::BufReader::new(file)
        .lines()
        .enumerate()
        .skip(start_line - 1)
        .take(lines)
    {
        writeln!(
            f,
            " {:>3} | {}",
            (line_num + 1).to_string().blue(),
            line.unwrap()
        )?;
    }
    Ok(())
}

fn write_source_line_from_stdlib(f: &mut fmt::Formatter<'_>, lib: &str, line: usize) -> fmt::Result {
    let content = if let Some(content) = library_source(lib) {
        content
    } else {
        writeln!( f, " failed to read library file: {:?}", lib)?;
        return Ok(());
    };

    let start_line = (line.saturating_sub(2)).max(1);
    let lines = line + 1 - start_line;

    for (line_num, line) in content
        .lines()
        .enumerate()
        .skip(start_line - 1)
        .take(lines)
    {
        writeln!(
            f,
            " {:>3} | {}",
            (line_num + 1).to_string().blue(),
            line
        )?;
    }
    Ok(())
}

fn underline(f: &mut fmt::Formatter<'_>, col_start: usize, len: usize) -> fmt::Result {
    write!(f, "{: <1$}", "", col_start)?;
    writeln!(f, "{:^<1$}", "", len,)
}

fn write_source_span_at(f: &mut fmt::Formatter<'_>, file: &FileOrLib, span: Span) -> fmt::Result {

    match file {
        FileOrLib::File(file) => write_source_line_from_file_at(f, file, span.line_start)?,
        FileOrLib::Lib(lib) => write_source_line_from_stdlib(f, lib, span.line_start)?,
    }
    write!(f, "{}", INDENT)?;
    underline(f, span.col_start, span.col_end - span.col_start)
}

fn file_line_display(file: &FileOrLib, line: usize) -> String {
    match file {
        FileOrLib::File(file) =>
            format!(
                "{}:{}",
                file.display().to_string().blue(),
                line.to_string().blue(),
            ),
        FileOrLib::Lib(lib) =>
            format!(
                "sylt standard library {}:{}",
                lib,
                line.to_string().blue(),
            ),
    }
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
    IndexError(Value, Value),

    /// (External function, parameters)
    ExternArgsMismatch(String, Vec<Value>),
    ExternError(String, String),
    ValueError(Op, Vec<Value>),
    UnknownField(String, String),
    ImmutableField(String),
    ArgumentCount(usize, usize),

    /// (Indexed value, length, index)
    IndexOutOfBounds(Value, usize, usize),

    AssertFailed,
    InvalidProgram,
    Unreachable,
}

#[derive(Debug, Clone)]
pub struct Helper {
    pub at: Option<(FileOrLib, Span)>,
    pub message: String,
}

#[derive(Debug, Clone)]
pub enum TypeError {
    // The message should be given afterwards,
    // since some errors are quite exotic.
    Exotic,

    // This error should be implemented at a later time.
    ToDo {
        line: u32,
        file: String,
    },

    Violating(Type),

    BinOp {
        lhs: Type,
        rhs: Type,
        op: String,
    },

    UniOp {
        val: Type,
        op: String,
    },

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    Mismatch {
        got: Type,
        expected: Type,
    },

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    MismatchAssign {
        got: Type,
        expected: Type,
    },

    Assignability,

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    ExcessiveForce {
        got: Type,
        expected: Type,
    },

    NamespaceNotExpression,

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    WrongArity {
        got: usize,
        expected: usize,
    },

    UnknownField {
        blob: String,
        field: String,
    },

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    MissingField {
        blob: String,
        field: String,
    },

    // TODO(ed): got and expected doesn't make sense - we don't know what we expect!
    TupleIndexOutOfRange {
        got: i64,
        length: usize,
    },

    TupleLengthMismatch {
        lhs: usize,
        rhs: usize,
    },

    UnresolvedName(String),

    WrongConstraintArity {
        name: String,
        got: usize,
        expected: usize,
    },

    UnknownConstraint(String),
    UnknownConstraintArgument(String),

    UnknownVariant(String, String),
    MissingVariants(String, Vec<String>),
    ExtraVariants(String, Vec<String>),
}

// TODO(ed): Switch to spans for the whole compiler?
#[derive(Clone, Debug)]
pub enum Error {
    NoFileGiven,
    FileNotFound(PathBuf),
    IOError(Rc<std::io::Error>),
    GitConflictError {
        file: FileOrLib,
        span: Span,
    },

    SyntaxError {
        file: FileOrLib,
        span: Span,
        message: String,
    },

    TypeError {
        kind: TypeError,
        file: FileOrLib,
        span: Span,
        message: Option<String>,
        helpers: Vec<Helper>,
    },

    // TODO(ed): Remove this! They should be panics, and be caught in the type-checker.
    CompileError {
        file: FileOrLib,
        span: Span,
        message: Option<String>,
    },

    RuntimeError {
        kind: RuntimeError,
        file: PathBuf,
        line: usize,
        message: Option<String>,
    },

    LuaError(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NoFileGiven => {
                write!(f, "No file to run")
            }
            Error::LuaError(stderr) => {
                write!(f, "Lua failed to run, \n:stderr:\n{}", stderr)
            }
            Error::FileNotFound(path) => {
                write!(f, "File '{}' not found", path.display())
            }
            Error::IOError(e) => {
                write!(f, "Unknown IO error: {}", e)
            }
            Error::GitConflictError { file, span } => {
                write!(f, "{}: ", "git conflict error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line_start))?;
                write!(
                    f,
                    "{}Git conflict marker found at line {}\n",
                    INDENT, span.line_start,
                )?;

                write_source_span_at(f, file, *span)
            }
            Error::RuntimeError { kind, message, .. } => {
                write!(f, "{}:\n", "Runtime error".red())?;
                write!(f, "{}{}\n", INDENT, kind)?;
                if let Some(message) = message {
                    for line in message.split('\n') {
                        write!(f, "{}{}\n", INDENT, line)?;
                    }
                }
                Ok(())
            }
            Error::SyntaxError { file, span, message } => {
                write!(f, "{}: ", "syntax error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line_start))?;
                write!(f, "{}Syntax Error on line {}\n", INDENT, span.line_start)?;

                for line in message.split('\n') {
                    write!(f, "{}{}\n", INDENT, line)?;
                }

                write_source_span_at(f, file, *span)
            }
            Error::TypeError { kind, file, span, message, helpers } => {
                write!(
                    f,
                    "{}: {}\n",
                    "typecheck error".red(),
                    file_line_display(file, span.line_start)
                )?;
                if !matches!(kind, TypeError::Exotic) {
                    write!(f, "{}{}\n", INDENT, kind)?;
                }

                if let Some(message) = message {
                    for line in message.split('\n') {
                        write!(f, "{}{}\n", INDENT, line)?;
                    }
                }
                write_source_span_at(f, file, *span)?;

                if !helpers.is_empty() {
                    // TODO(ed): Might be helpfull to not write all the errors?
                    write!(f, "{}\n", "help:".yellow())?;
                    for Helper { message, at } in helpers.iter() {
                        write!(f, "{}{}\n", INDENT, message)?;
                        match at {
                            Some((file, span)) => write_source_span_at(f, file, *span)?,
                            None => {}
                        }
                    }
                }
                Ok(())
            }
            Error::CompileError { file, span, message } => {
                write!(f, "{}: ", "compile error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line_start))?;
                write!(f, "{}Failed to compile line {}\n", INDENT, span.line_start)?;

                if let Some(message) = message {
                    for line in message.split('\n') {
                        write!(f, "{}{}\n", INDENT, line)?;
                    }
                }
                write_source_span_at(f, file, *span)
            }
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::IndexError(value, slot) => {
                write!(f, "Cannot index value '{:?}' with type '{:?}'", value, slot)
            }
            RuntimeError::ExternArgsMismatch(name, values) => {
                write!(
                    f,
                    "Extern function '{}' doesn't accept argument(s) {:?}",
                    name, values
                )
            }
            RuntimeError::ExternError(fun, msg) => {
                write!(f, "Extern function '{}': {:?}", fun, msg)
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
            RuntimeError::ImmutableField(field) => {
                write!(f, "Cannot mutate field '{}' since it is immutable", field)
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
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Exotic => Ok(()),

            TypeError::ToDo { line, file } => {
                write!(
                    f,
                    "Todo: implement this error on line {} in file {}",
                    line, file
                )
            }

            TypeError::Mismatch { got, expected } => {
                write!(f, "A '{:?}' cannot be a '{:?}'", got, expected)
            }

            TypeError::MismatchAssign { got, expected } => {
                write!(f, "Cannot assign a '{:?}' to a '{:?}'", got, expected)
            }

            TypeError::Assignability => {
                write!(f, "Could not assign")
            }

            TypeError::BinOp { op, lhs, rhs } => {
                write!(f, "{} is not defined for '{:?}' and '{:?}'", op, lhs, rhs)
            }

            TypeError::UniOp { op, val } => {
                write!(f, "{} is not defined for '{:?}'", op, val)
            }

            TypeError::Violating(ty) => {
                write!(f, "Got '{:?}', which it cannot be", ty)
            }

            TypeError::ExcessiveForce { got, expected } => {
                write!(
                    f,
                    "This type force is unnessecary, '{:?}' is a '{:?}'",
                    got, expected
                )
            }

            TypeError::NamespaceNotExpression => {
                write!(f, "This resolves to a namespace, not a value")
            }

            TypeError::WrongArity { got, expected } => {
                write!(f, "Expected {} arguments but got {}", expected, got)
            }

            TypeError::UnknownField { blob, field } => {
                write!(f, "Cannot find field '{}.{}'", blob, field)
            }

            TypeError::MissingField { blob, field } => {
                write!(f, "Blob instance lacks field '{}.{}'", blob, field)
            }

            TypeError::TupleIndexOutOfRange { length, got } => {
                write!(f, "A tuple of length {} has no element {}", length, got)
            }

            TypeError::TupleLengthMismatch { lhs, rhs } => {
                write!(f, "Tuple lengths don't match '{}'!='{}'", lhs, rhs)
            }

            TypeError::UnresolvedName(name) => {
                write!(f, "Cannot resolve name '{}'", name)
            }

            TypeError::WrongConstraintArity { name, got, expected } => {
                write!(
                    f,
                    "Constraint '{}' take {} arguments, got {}",
                    name, got, expected
                )
            }

            TypeError::UnknownConstraint(constraint) => {
                write!(f, "Unknown constraint '{}'", constraint)
            }

            TypeError::UnknownConstraintArgument(argument) => {
                write!(f, "Cannot resolve this constraint argument '{}'", argument)
            }

            TypeError::UnknownVariant(enum_name, var_name) => {
                write!(
                    f,
                    "Enum '{}' doesn't have variant '{}'",
                    enum_name, var_name
                )
            }

            TypeError::MissingVariants(enum_name, vars) => {
                write!(f, "Enum '{}' lacks these variants:\n", enum_name)?;
                for var in vars.iter() {
                    write!(f, "{} - {}\n", INDENT, var)?;
                }
                Ok(())
            }

            TypeError::ExtraVariants(enum_name, vars) => {
                write!(f, "Enum '{}' has these extra variants:\n", enum_name)?;
                for var in vars.iter() {
                    write!(f, "{} + {}\n", INDENT, var)?;
                }
                Ok(())
            }
        }
    }
}
