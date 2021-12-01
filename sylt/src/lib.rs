/// Re-export of derived functions for [Args].
pub use gumdrop::Options;

use std::fmt::Debug;
use std::io::Write;
use std::path::{Path, PathBuf};
use sylt_common::error::Error;
use sylt_common::prog::Prog;
use sylt_common::RustFunction;

pub mod formatter;

type ExternFunctionList = Vec<(String, RustFunction, String)>;

/// Generates the linking for the standard library, and lingon if it's active.
pub fn lib_bindings() -> ExternFunctionList {
    let mut lib = Vec::new();

    lib.append(&mut sylt_std::sylt::_sylt_link());

    lib
}

pub fn read_file(path: &Path) -> Result<String, Error> {
    std::fs::read_to_string(path).map_err(|_| Error::FileNotFound(path.to_path_buf()))
}

pub fn compile_with_reader_to_writer<R>(
    args: &Args,
    functions: ExternFunctionList,
    reader: R,
    write_file: Option<Box<dyn Write>>,
) -> Result<Prog, Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    let file = PathBuf::from(args.args.first().expect("No file to run"));
    let tree = sylt_parser::tree(&file, reader)?;
    if args.dump_tree {
        println!("{}", tree);
    }
    sylt_compiler::compile(!args.skip_typecheck, write_file, tree, &functions)
}

// TODO(ed): This name isn't true anymore - since it can compile
pub fn run_file_with_reader<R>(
    args: &Args,
    functions: ExternFunctionList,
    reader: R,
) -> Result<(), Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    match &args.compile {
        None => {
            use std::process::{Command, Stdio};
            let mut child = Command::new("lua")
                .stdin(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("Failed to start lua - make sure it's installed correctly");
            let stdin = child.stdin.take().unwrap();
            match compile_with_reader_to_writer(args, functions, reader, Some(Box::new(stdin)))? {
                Prog::Lua => {
                    let output = child.wait_with_output().unwrap();
                    // NOTE(ed): Status is always 0 when piping to STDIN, atleast on my version of lua,
                    // so we check stderr - which is a bad idea.
                    if !output.stderr.is_empty() {
                        return Err(vec![Error::LuaError(
                            String::from_utf8(output.stderr).unwrap(),
                        )]);
                    }
                }
                Prog::Bytecode(_) => unreachable!(),
            };
        }

        Some(s) if s == "-" => {
            use std::io;
            // NOTE(ed): Lack of running
            compile_with_reader_to_writer(args, functions, reader, Some(Box::new(io::stdout())))?;
        }

        Some(s) => {
            use std::fs::File;
            let file =
                File::create(PathBuf::from(s)).expect(&format!("Failed to create file: {}", s));
            let writer: Option<Box<dyn Write>> = Some(Box::new(file));
            // NOTE(ed): Lack of running
            compile_with_reader_to_writer(args, functions, reader, writer)?;
        }
    };
    Ok(())
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: ExternFunctionList) -> Result<(), Vec<Error>> {
    run_file_with_reader(args, functions, read_file)
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(
        long = "skip-typecheck",
        no_short,
        help = "Does no type checking what so ever"
    )]
    pub skip_typecheck: bool,

    #[options(long = "dump-tree", no_short, help = "Writes the tree to stdout")]
    pub dump_tree: bool,

    #[options(
        short = "c",
        long = "compile",
        help = "Compile to a lua file - for stdout"
    )]
    pub compile: Option<String>,

    #[options(short = "v", no_long, count, help = "Increase verbosity, up to max 2")]
    pub verbosity: u32,

    #[options(
        long = "format",
        help = "Run an auto formatter on the supplied file and print the result to stdout."
    )]
    pub format: bool,

    #[options(help = "Print this help")]
    pub help: bool,

    #[options(free)]
    pub args: Vec<String>,
}

impl Args {
    /// Wraps the function with the same name from [gumdrop] for convenience.
    pub fn parse_args_default_or_exit() -> Args {
        <Args as Options>::parse_args_default_or_exit()
    }
}

pub fn path_to_module(current_file: &Path, module: &str) -> PathBuf {
    let mut res = PathBuf::from(current_file);
    res.pop();
    res.push(format!("{}.sy", module));
    res
}

#[macro_export]
macro_rules! assert_errs {
    ($result:expr, $expect:pat) => {
        let errs = $result.err().unwrap_or(Vec::new());

        #[allow(unused_imports)]
        use sylt_common::error::Error;
        #[allow(unused_imports)]
        use sylt_tokenizer::Span;
        if !matches!(errs.as_slice(), $expect) {
            eprintln!("===== Got =====");
            for err in errs {
                eprint!("{}", err);
            }
            eprintln!("===== Expect =====");
            eprint!("{}\n\n", stringify!($expect));
            assert!(false);
        }
    };
}

#[cfg(test)]
mod bytecode {
    #[macro_export]
    macro_rules! test_file_run {
        ($fn:ident, $path:literal, $print:expr, $errs:pat, $_:expr) => {
            #[test]
            fn $fn() {
                #[allow(unused_imports)]
                use sylt_common::error::RuntimeError;
                #[allow(unused_imports)]
                use sylt_common::error::TypeError;
                #[allow(unused_imports)]
                use sylt_common::Type;

                let mut args = $crate::Args::default();
                args.args = vec![format!("../{}", $path)];
                args.verbosity = if $print { 1 } else { 0 };
                let res = $crate::run_file(&args, ::sylt_std::sylt::_sylt_link());
                $crate::assert_errs!(res, $errs);
            }
        };
    }

    sylt_macro::find_tests!(test_file_run);
}

#[cfg(test)]
mod lua {
    #[macro_export]
    macro_rules! test_file_lua {
        ($fn:ident, $path:literal, $print:expr, $errs:pat, $any_runtime_errors:expr) => {
            #[test]
            fn $fn() {
                use std::io::Write;
                use std::process::{Command, Stdio};
                #[allow(unused_imports)]
                use sylt_common::error::RuntimeError;
                #[allow(unused_imports)]
                use sylt_common::error::TypeError;
                #[allow(unused_imports)]
                use sylt_common::Type;

                let file = format!("../{}", $path);
                let mut args = $crate::Args::default();
                args.args = vec![file.clone()];
                args.verbosity = if $print { 1 } else { 0 };

                let mut child = Command::new("lua")
                    .stdin(Stdio::piped())
                    .stderr(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()
                    .expect(concat!("Failed to start lua, testing:", $path));

                let stdin = child.stdin.take().unwrap();
                let writer: Option<Box<dyn Write>> = Some(Box::new(stdin));
                let res = $crate::compile_with_reader_to_writer(
                    &args,
                    ::sylt_std::sylt::_sylt_link(),
                    $crate::read_file,
                    writer,
                );

                println!("Expect error: {}", $any_runtime_errors);
                println!("Got error: {:?}", res.is_err());
                if $any_runtime_errors {
                    assert_errs!(res, []);
                } else {
                    assert_errs!(res, $errs);
                }

                let output = child.wait_with_output().unwrap();
                // HACK(ed): Status is always 0 when piping to STDIN, atleast on my version of lua,
                // so we check stderr - which is a bad idea.
                let stderr = String::from_utf8_lossy(&output.stderr);
                let stdout = String::from_utf8_lossy(&output.stdout);
                let success = output.status.success() && stderr.is_empty();
                println!("Success: {}", success);
                if $any_runtime_errors {
                    assert!(
                        !success,
                        "Program ran to completion when it should crash\n:STDOUT:\n{}\n\n:STDERR:\n{}\n",
                        stdout,
                        stderr
                    );
                } else {
                    assert!(
                        success,
                        "Failed when it should succeed\n:STDOUT:\n{}\n\n:STDERR:\n{}\n",
                        stdout,
                        stderr
                    );
                }
            }
        };
    }

    sylt_macro::find_tests!(test_file_lua);
}
