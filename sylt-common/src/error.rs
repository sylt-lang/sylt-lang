use crate::{Op, Type, Value};

use owo_colors::OwoColorize;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_tokenizer::Span;

static INDENT: &'static str = "      ";

fn write_source_line_at(f: &mut fmt::Formatter<'_>, file: &Path, line: usize) -> fmt::Result {
    let file = if let Ok(file) = File::open(file) {
        file
    } else {
        return write!(f, "Unable to open file {}", file.display());
    };

    let start_line = (line.saturating_sub(2)).max(1);
    let lines = line - start_line + 1;

    for (line_num, line) in io::BufReader::new(file)
        .lines()
        .enumerate()
        .skip(start_line - 1)
        .take(lines)
    {
        writeln!(f, " {:3} | {}", (line_num + 1).blue(), line.unwrap())?;
    }
    Ok(())
}

fn underline(f: &mut fmt::Formatter<'_>, col_start: usize, len: usize) -> fmt::Result {
    write!(f, "{: <1$}", "", col_start)?;
    writeln!(f, "{:^<1$}", "", len,)
}

fn write_source_span_at(f: &mut fmt::Formatter<'_>, file: &Path, span: Span) -> fmt::Result {
    write_source_line_at(f, file, span.line)?;
    write!(f, "{}", INDENT)?;
    underline(f, span.col_start, span.col_end - span.col_start)
}

fn file_line_display(file: &Path, line: usize) -> String {
    format!(
        "{}:{}",
        file.display().blue(),
        line.blue().to_string(),
    )
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
    FieldTypeMismatch(String, String, Type, Type, String),
    TypeError(Op, Vec<Type>),
    TypeCompare(String),
    TypeMismatch(Type, Type),
    CannotInfer(Type, Type),
    ArgumentType(Vec<Type>, Vec<Type>, String),
    IndexError(Value, Type),

    /// (External function, parameters)
    ExternTypeMismatch(String, Vec<Type>),
    ExternError(String, String),
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

// TODO(ed): Switch to spans for the whole compiler?
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
        span: Span,
        message: Option<String>,
    },

    CompileError {
        file: PathBuf,
        span: Span,
        message: Option<String>,
    },

    GitConflictError {
        file: PathBuf,
        span: Span,
    },

    FileNotFound(PathBuf),
    NoFileGiven,
    IOError(Rc<std::io::Error>),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[rustfmt::skip]
            Error::RuntimeError { kind, phase, file, line, message } => {
                write!(f, "{} {}: ", phase.red(), "error".red())?;
                write!(f, "{}\n", file_line_display(file, *line))?;
                write!(f, "{}{}\n", INDENT, kind)?;

                if let Some(message) = message {
                    write!(f, "{}\n", message)?;
                }

                write_source_line_at(f, file, *line)
            }
            Error::CompileError {
                file,
                span,
                message,
            } => {
                write!(f, "{}: ", "compile error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line))?;
                write!(f, "{}Failed to compile line {}\n", INDENT, span.line)?;

                if let Some(message) = message {
                    write!(f, "{}{}\n", INDENT, message)?;
                }

                write_source_span_at(f, file, *span)
            }
            Error::SyntaxError {
                file,
                span,
                message,
            } => {
                write!(f, "{}: ", "syntax error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line))?;
                write!(f, "{}Syntax Error on line {}\n", INDENT, span.line)?;

                if let Some(message) = message {
                    write!(f, "{}{}\n", INDENT, message)?;
                }

                write_source_span_at(f, file, *span)
            }
            Error::GitConflictError { file, span } => {
                write!(f, "{}: ", "git conflict error".red())?;
                write!(f, "{}\n", file_line_display(file, span.line))?;

                write!(
                    f,
                    "{}Git conflict marker found at line {}\n",
                    INDENT, span.line,
                )?;

                write_source_span_at(f, file, *span)
            }
            Error::FileNotFound(path) => {
                write!(f, "File '{}' not found", path.display())
            }
            Error::NoFileGiven => {
                write!(f, "No file to run")
            }
            Error::IOError(e) => {
                write!(f, "Unknown IO error: {}", e)
            }
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::FieldTypeMismatch(obj, field, a, b, msg) => {
                write!(
                    f,
                    "Field {}.{} expected {:?} but got {:?}. {}",
                    obj, field, a, b, msg
                )
            }
            RuntimeError::TypeError(op, types) => {
                let types = types
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(f, "Cannot apply {:?} to types {}", op, types)
            }
            RuntimeError::TypeCompare(msg) => {
                write!(f, "{}", msg)
            }
            RuntimeError::TypeMismatch(a, b) => {
                write!(f, "Expected '{:?}' and got '{:?}'", a, b)
            }
            RuntimeError::CannotInfer(a, b) => {
                write!(f, "Failed to infer type '{:?}' from '{:?}'", a, b)
            }
            RuntimeError::ArgumentType(a, b, msg) => {
                let expected = a
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                let given = b
                    .iter()
                    .fold(String::new(), |a, v| format!("{}{:?}, ", a, v));
                write!(
                    f,
                    "Argument types do not match, expected [{:?}] but got [{:?}]. {}",
                    expected, given, msg
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

#[cfg(test)]
mod test {
    // A small hack is required to test the functions working on Formatters
    // since we can't construct new Formatters.
    //
    // The formatted span output is very weird to test. Feel free to move the
    // string around and check that the ^^^ lines up correctly. Spaces matter!
    //
    // For some tests, color is disabled by setting the env variable NO_COLOR=1.

    struct UnderlineTester(usize, usize);
    impl std::fmt::Display for UnderlineTester {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            super::underline(f, self.0, self.1)
        }
    }

    struct SourceSpanTester<'p>(&'p std::path::Path, super::Span);
    impl<'p> std::fmt::Display for SourceSpanTester<'p> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            super::write_source_span_at(f, self.0, self.1)
        }
    }

    #[test]
    fn underline() {
        assert_eq!(&format!("{}", UnderlineTester(1, 2)), " ^^\n");
        assert_eq!(&format!("{}", UnderlineTester(2, 1)), "  ^\n");
        assert_eq!(&format!("{}", UnderlineTester(0, 0)), "\n");
        assert_eq!(&format!("{}", UnderlineTester(0, 2)), "^^\n");
    }

    fn get_tmp() -> std::path::PathBuf {
        let mut tmp = std::env::temp_dir();
        tmp.push(format!("test-{}.sy", sungod::Ra::default().sample::<u32>()));
        tmp
    }

    fn write_str_to_tmp(s: &str) -> std::path::PathBuf {
        let tmp = get_tmp();
        std::fs::write(&tmp, s).expect(&format!(
            "Unable to write test string to tmp file at {}",
            tmp.display(),
        ));
        tmp.clone()
    }

    macro_rules! test_source_span {
        ($fn:ident, $src:expr, (line: $line:expr, col_start: $col_start:expr, col_end: $col_end:expr), $result:expr $(,)?) => {
            #[test]
            fn $fn() {
                std::env::set_var("NO_COLOR", "1");
                let path = write_str_to_tmp($src);
                assert_eq!(
                    &format!(
                        "{}",
                        SourceSpanTester(
                            &path,
                            super::Span {
                                line: $line,
                                col_start: $col_start,
                                col_end: $col_end,
                            }
                        ),
                    ),
                    $result,
                );
            }
        };
    }

    test_source_span!(
        write_source_span_display_simple,
        "hello\nstart :: fn {\n",
        (line: 2, col_start: 1, col_end: 6),
        "   1 | hello
   2 | start :: fn {
       ^^^^^\n",
    );

    test_source_span!(
        write_source_span_display_many_lines,
        "hello\nhello\nhello\nstart :: fn {\n  abc := 123\n  def := ghi\n}\n",
        (line: 4, col_start: 1, col_end: 6),
        "   2 | hello
   3 | hello
   4 | start :: fn {
       ^^^^^\n",
    );
}
