
/// Re-export of derived functions for [Args].
pub use gumdrop::Options;

use owo_colors::OwoColorize;
use sylt_common::error::{Error, RuntimeError};
use sylt_common::rc::Rc;
use sylt_common::{Op, RustFunction, Type, Value};
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::path::{Path, PathBuf};

pub mod compiler;
pub mod parser;
pub mod typechecker;
pub mod vm;

// Lingon linking layer
#[cfg(feature = "lingon")]
pub mod lingon_sylt;
pub mod lib_sylt;

/// Generates the linking for the standard library, and lingon if it's active.
pub fn lib_bindings() -> Vec<(String, RustFunction)> {
    let mut lib = Vec::new();

    lib.append(&mut lib_sylt::_sylt_link());

    #[cfg(feature = "lingon")]
    lib.append(&mut lingon_sylt::_sylt_link());

    lib
}

pub trait Next {
    fn next(&self) -> Self;
}

pub fn compile(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<Prog, Vec<Error>> {
    let path = match &args.file {
        Some(file) => file,
        None => {
            return Err(vec![Error::NoFileGiven]);
        }
    };
    let tree = parser::tree(&path)?;
    let prog = compiler::compile(tree, &functions)?;
    Ok(prog)
}

/// Compiles, links and runs the given file. The supplied functions are callable
/// external functions.
pub fn run_file(args: &Args, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    let prog = compile(args, functions)?;
    typechecker::typecheck(&prog, &args)?;
    run(&prog, &args)
}

pub fn run(prog: &Prog, args: &Args) -> Result<(), Vec<Error>> {
    let mut vm = vm::VM::new();
    vm.print_bytecode = args.verbosity >= 1;
    vm.print_exec = args.verbosity >= 2;
    vm.init(&prog);
    if let Err(e) = vm.run() {
        Err(vec![e])
    } else {
        Ok(())
    }
}

#[derive(Default, Debug, Options)]
pub struct Args {
    #[options(free)]
    pub file: Option<PathBuf>,

    #[options(short = "r", long = "run", help = "Runs a precompiled sylt binary")]
    pub is_binary: bool,

    #[options(short = "c", long = "compile", help = "Compile a sylt binary")]
    pub compile_target: Option<PathBuf>,

    #[options(short = "v", no_long, count, help = "Increase verbosity, up to max 2")]
    pub verbosity: u32,

    #[options(help = "Print this help")]
    pub help: bool,
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

// TODO(ed): We need to rewrite this with indexes to this struct instead
// of an RC - otherwise we cannot support all recursive types.
#[derive(Debug, Clone)]
pub struct Blob {
    pub id: usize,
    pub namespace: usize,
    pub name: String,
    /// Maps field names to their type
    pub fields: HashMap<String, Type>,
}

impl PartialEq for Blob {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Blob {
    fn new(id: usize, namespace: usize, name: &str) -> Self {
        Self {
            id,
            namespace,
            name: String::from(name),
            fields: HashMap::new(),
        }
    }
}

#[derive(Debug)]
enum BlockLinkState {
    Linked,
    Nothing,
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    upvalues: Vec<(usize, bool, Type)>,
    linking: BlockLinkState,

    namespace: usize,

    pub name: String,
    pub file: PathBuf,
    ops: Vec<Op>,
    last_line_offset: usize,
    line_offsets: HashMap<usize, usize>,
}

impl Block {
    fn new(name: &str, namespace: usize, file: &Path) -> Self {
        Self {
            ty: Type::Void,
            upvalues: Vec::new(),
            linking: BlockLinkState::Nothing,

            namespace,

            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
        }
    }

    pub fn args(&self) -> &Vec<Type> {
        if let Type::Function(ref args, _) = self.ty {
            args
        } else {
            unreachable!();
        }
    }

    pub fn ret(&self) -> &Type {
        if let Type::Function(_, ref ret) = self.ty {
            ret
        } else {
            unreachable!()
        }
    }

    fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        0
    }

    pub fn debug_print(&self, constants: Option<&[Value]>) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            println!(
                "{}{:05} {:?}{}",
                if self.line_offsets.contains_key(&i) {
                    format!("{:5} ", self.line_offsets[&i].blue())
                } else {
                    format!("    {} ", "|".blue())
                },
                i.red(),
                s,
                match (s, constants) {
                    (Op::Constant(c), Some(constants))
                    | (Op::Link(c), Some(constants))
                      => format!("    => {:?}", &constants[*c]),
                    _ => "".to_string()
                }
            );
        }
        println!();
    }

    fn add(&mut self, op: Op, token_position: usize) -> usize {
        let mut len = self.curr();
        if matches!(op, Op::Pop) && len > 1 {
            len -= 1;
            match self.ops.last().unwrap() {
                Op::Copy(n) => {
                    if *n == 1 {
                        self.ops.pop();
                        return len - 1;
                    } else {
                        self.ops[len] = Op::Copy(*n - 1);
                        return len;
                    }
                }
                Op::Constant(_) | Op::ReadLocal(_) | Op::ReadUpvalue(_) => {
                    self.ops.pop();
                    return len - 1;
                }
                _ => {}
            }
        }
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    fn curr(&self) -> usize {
        self.ops.len()
    }
}

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub blobs: Vec<Blob>,
    pub functions: Vec<RustFunction>,
    pub constants: Vec<Value>,
    pub strings: Vec<String>,
}

#[cfg(test)]
mod tests {
    #[macro_export]
    macro_rules! assert_errs {
        ($result:expr, $expect:pat) => {
            let errs = $result.err().unwrap_or(Vec::new());

            #[allow(unused_imports)]
            use ::sylt_common::error::Error;
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
                use ::sylt_common::error::RuntimeError;
                #[allow(unused_imports)]
                use $crate::Type;

                let mut args = $crate::Args::default();
                args.file = Some(std::path::PathBuf::from(format!("../{}", $path)));
                args.verbosity = if $print { 1 } else { 0 };
                let res = $crate::run_file(
                    &args,
                    $crate::lib_sylt::_sylt_link(),
                );
                $crate::assert_errs!(res, $errs);
            }
        };
    }

    sylt_macro::find_tests!();
}
