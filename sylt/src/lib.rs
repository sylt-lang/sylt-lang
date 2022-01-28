/// Re-export of derived functions for [Args].
pub use gumdrop::Options;

use std::fmt::Debug;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_common::error::Error;

pub mod formatter;

#[cfg(test)]
pub mod test;

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
    let tree = sylt_parser::tree(&file, reader, true)?;
    if args.dump_tree {
        println!("{}", tree);
    }
    sylt_compiler::compile(write_file, tree)
}

// TODO(ed): This name isn't true anymore - since it can compile
pub fn run_file_with_reader<R>(args: &Args, reader: R) -> Result<(), Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    match &args.output {
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
    #[options(long = "dump-tree", help = "Write the syntax tree to stdout")]
    pub dump_tree: bool,

    #[options(
        long = "output",
        short = "o",
        meta = "FILE",
        help = "Output a compiled lua file, '-' for stdout"
    )]
    pub output: Option<String>,

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
