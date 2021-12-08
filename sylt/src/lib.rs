/// Re-export of derived functions for [Args].
pub use gumdrop::Options;

use std::fmt::Debug;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_common::error::Error;

pub mod formatter;

pub fn read_file(path: &Path) -> Result<String, Error> {
    std::fs::read_to_string(path).map_err(|_| Error::FileNotFound(path.to_path_buf()))
}

pub fn compile_with_reader_to_writer<R>(
    args: &Args,
    reader: R,
    write_file: &mut dyn Write,
) -> Result<(), Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    let file = PathBuf::from(args.args.first().expect("No file to run"));
    let tree = sylt_parser::tree(&file, reader)?;
    if args.dump_tree {
        println!("{}", tree);
    }
    sylt_compiler::compile(!args.skip_typecheck, write_file, tree)
}

// TODO(ed): This name isn't true anymore - since it can compile
pub fn run_file_with_reader<R>(args: &Args, reader: R) -> Result<(), Vec<Error>>
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
            let mut stdin = child.stdin.take().unwrap();
            compile_with_reader_to_writer(args, reader, &mut stdin)?;

            drop(stdin); // Close stdin so the child can do its thing.

            let output = child.wait_with_output().unwrap();
            // NOTE(ed): Status is always 0 when piping to STDIN, atleast on my version of lua,
            // so we check stderr - which is a bad idea.
            if !output.stderr.is_empty() {
                return Err(vec![Error::LuaError(
                    String::from_utf8(output.stderr).unwrap(),
                )]);
            }
        }

        Some(s) if s == "-" => {
            use std::io;
            // NOTE(ed): Lack of running
            compile_with_reader_to_writer(args, reader, io::stdout().by_ref())?;
        }

        Some(s) => {
            use std::fs::File;
            let mut buf = Vec::new();
            // NOTE(ed): Lack of running
            compile_with_reader_to_writer(args, reader, buf.by_ref())?;

            File::create(PathBuf::from(s))
                .expect(&format!("Failed to create file: {}", s))
                .write(&buf)
                .map_err(|e| vec![Error::IOError(Rc::new(e))])?;
        }
    };
    Ok(())
}

/// Compiles, and runs the given file.
pub fn run_file(args: &Args) -> Result<(), Vec<Error>> {
    run_file_with_reader(args, read_file)
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(
        long = "skip-typecheck",
        no_short,
        help = "Does no type checking what so ever"
    )]
    pub skip_typecheck: bool,

    #[options(long = "dump-tree", no_short, help = "Write the syntax tree to stdout")]
    pub dump_tree: bool,

    #[options(long = "output", help = "Output a compiled lua file, '-' for stdout")]
    pub compile: Option<String>,

    #[options(short = "v", no_long, count, help = "Increase verbosity (max 2)")]
    pub verbosity: u32,

    #[options(
        long = "format",
        help = "Format the file and write the result to stdout"
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
mod lua {
    #[macro_export]
    macro_rules! test_file_lua {
        ($fn:ident, $path:literal, $print:expr, $errs:pat, $any_runtime_errors:expr) => {
            #[test]
            fn $fn() {
                use std::process::{Command, Stdio};
                #[allow(unused_imports)]
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

                let mut stdin = child.stdin.take().unwrap();
                let res = $crate::compile_with_reader_to_writer(
                    &args,
                    $crate::read_file,
                    &mut stdin,
                );

                drop(stdin); // Close stdin so the child can do its thing.

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
