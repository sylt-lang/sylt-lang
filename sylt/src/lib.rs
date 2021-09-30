/// Re-export of derived functions for [Args].
pub use gumdrop::Options;

use std::fmt::Debug;
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

    #[cfg(feature = "lingon")]
    lib.append(&mut sylt_std::lingon::_sylt_link());

    #[cfg(feature = "network")]
    lib.append(&mut sylt_std::network::_sylt_link());

    lib
}

pub fn read_file(path: &Path) -> Result<String, Error> {
    std::fs::read_to_string(path).map_err(|_| Error::FileNotFound(path.to_path_buf()))
}

pub fn compile_with_reader<R>(
    args: &Args,
    functions: ExternFunctionList,
    reader: R,
) -> Result<Prog, Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    let mut file = PathBuf::from(args.args.first().expect("No file to run"));
    let tree = sylt_parser::tree(&file, reader)?;
    if args.dump_tree {
        println!("{}", tree);
    }
    assert!(file.set_extension("lua"));
    let lua_file = if args.lua { Some(file) } else { None };
    let prog = sylt_compiler::compile(!args.skip_typecheck, lua_file, tree, &functions)?;
    Ok(prog)
}

pub fn run_file_with_reader<R>(
    args: &Args,
    functions: ExternFunctionList,
    reader: R,
) -> Result<(), Vec<Error>>
where
    R: Fn(&Path) -> Result<String, Error>,
{
    let prog = compile_with_reader(args, functions, reader)?;
    if args.lua {
        Ok(())
    } else {
        run(&prog, &args)
    }
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: ExternFunctionList) -> Result<(), Vec<Error>> {
    run_file_with_reader(args, functions, read_file)
}

pub fn run(prog: &Prog, args: &Args) -> Result<(), Vec<Error>> {
    let mut vm = sylt_machine::VM::new();
    vm.print_bytecode = args.verbosity >= 1;
    vm.print_exec = args.verbosity >= 2;
    vm.init(&prog, &args.args);
    if let Err(e) = vm.run() {
        Err(vec![e])
    } else {
        Ok(())
    }
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(short = "r", long = "run", help = "Runs a precompiled sylt binary")]
    pub is_binary: bool,

    #[options(
        long = "skip-typecheck",
        no_short,
        help = "Does no type checking what so ever"
    )]
    pub skip_typecheck: bool,

    #[options(long = "dump-tree", no_short, help = "Writes the tree to stdout")]
    pub dump_tree: bool,

    #[options(short = "l", long = "lua", help = "Compile to lua")]
    pub lua: bool,

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

#[cfg(test)]
mod running {
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

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal, $print:expr, $errs:pat) => {
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

    sylt_macro::find_tests!(test_file);
}
