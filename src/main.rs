#![feature(box_patterns)]

use gumdrop::Options;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;
use std::process::{exit, Command, Stdio};

mod ast;
mod codegen;
mod error;
mod lexer;
mod name_resolution;
mod parser;
mod type_checker;

#[derive(Options)]
struct Args {
  #[options(help = "print help message")]
  help: bool,

  #[options(required, free, help = "the singular source file to compile")]
  source: String,

  #[options(
    short = 'a',
    long = "dump-ast",
    help = "output the parsed AST to a file or '-' for stdout"
  )]
  dump_ast: Option<String>,

  #[options(
    short = 't',
    long = "dump-types",
    help = "output the types of the program to a file or '-' for stdout"
  )]
  dump_types: Option<String>,

  #[options(
    short = 'l',
    long = "dump-lua",
    help = "output the generated lua code to a file or '-' for stdout"
  )]
  dump_lua: Option<String>,

  #[options(
    short = 'o',
    long = "only-compile",
    help = "don't automaticallt run the program - parse and typecheck and codegen only if codegen is writen to file"
  )]
  only_compile: bool,

  #[options(
    no_short,
    long = "love",
    help = "codegen a love module instead of just running main"
  )]
  love: bool,
}

fn main() {
  let args = Args::parse_args_default_or_exit();
  let src = match std::fs::read_to_string(&args.source) {
    Ok(src) => src,
    Err(e) => {
      eprintln!("Failed to open source file {:?}: {}", &args.source, e);
      exit(1);
    }
  };

  let ast = match parser::parse(&src) {
    Err(errs) => {
      for e in errs.iter() {
        eprintln!("{}", e.render(Some(&src)));
      }
      exit(5);
    }
    Ok(a) => a,
  };

  match args.dump_ast {
    Some(s) if s == "-" => println!("{:#?}", ast),
    Some(s) => std::fs::write(s, format!("{:#?}", ast)).expect("Failed to write AST to file"),
    None => {}
  }

  // TODO[et]: How slow is this clone?
  let (names, fields, named_ast) = match name_resolution::resolve(ast) {
    Err(errs) => {
      for e in errs.iter() {
        eprintln!("{}", e.render(Some(&src)));
      }
      exit(6);
    }
    Ok(a) => a,
  };

  let types = match type_checker::check(&names, &named_ast, &fields) {
    Err(e) => {
      // TODO: Can this be run per def?
      eprintln!("{}", e.render(Some(&src)));
      exit(7);
    }
    Ok(a) => a,
  };

  match args.dump_types {
    Some(s) => {
      let mut out = BufWriter::new(match s {
        s if s == "-" => Box::new(std::io::stdout()) as Box<dyn Write>,
        p => {
          let path = Path::new(&p);
          Box::new(File::create(&path).expect("Failed to write types to file")) as Box<dyn Write>
        }
      });

      for (i, t) in types.iter().enumerate() {
        let rendered_type = match t {
          type_checker::Node::Child(id) => format!("#{}", id.0),
          type_checker::Node::Ty(ty) => ty.render_to_string(types.clone(), &names, &fields),
        };
        match &names.get(i) {
          Some(name) => writeln!(
            out,
            "{:03} V {:?} @ {}\n  used at: {:?}\n  type: {}\n  raw: {:?}",
            i, name.name, name.def_at, name.usages, rendered_type, t
          ),
          None => writeln!(out, "{:03} N {}", i, rendered_type),
        }
        .expect("Failed to write to type file");
      }
    }
    None => {}
  }

  if args.only_compile {
    match args.dump_lua {
      None => {}
      Some(s) => {
        let mut code = BufWriter::new(match s {
          s if s == "-" => Box::new(std::io::stdout()) as Box<dyn Write>,
          p => {
            let path = Path::new(&p);
            Box::new(File::create(&path).expect("Failed to write lua to file")) as Box<dyn Write>
          }
        });
        match codegen::gen(&mut code, &types, &names, &fields, &named_ast, args.love) {
          Err(err) => {
            eprintln!("file error: {:?}", err);
            exit(4);
          }
          Ok(_) => {}
        };
      }
    }
  } else {
    let mut lua = Command::new("lua")
      .stdin(Stdio::piped())
      .spawn()
      .expect("Didn't find a `lua` executable");
    let mut out = lua.stdin.as_mut().unwrap();
    let mut code = BufWriter::new(&mut out);
    match codegen::gen(&mut code, &types, &names, &fields, &named_ast, args.love) {
      Err(err) => {
        eprintln!("file error: {:?}", err);
        exit(4);
      }
      Ok(_) => {}
    };
    match args.dump_lua {
      Some(s) if s == "-" => println!("{}", std::str::from_utf8(code.buffer()).unwrap()),
      Some(s) => std::fs::write(
        s,
        format!("{}", std::str::from_utf8(code.buffer()).unwrap()),
      )
      .expect("Failed to write generated code to file"),
      None => {}
    }
    drop(code);
    drop(out);

    if let Some(ref mut stdout) = lua.stdout {
      for line in BufReader::new(stdout).lines() {
        match line {
          Ok(l) => println!("{}", l),
          Err(err) => eprintln!("{}", err),
        }
      }
    }

    if let Some(ref mut stderr) = lua.stderr {
      for line in BufReader::new(stderr).lines() {
        match line {
          Ok(l) => eprintln!("{}", l),
          Err(err) => eprintln!("{}", err),
        }
      }
    }
    lua.wait().expect("Lua crashed");
  }
}

#[test]
fn run_golden_tests() -> goldentests::TestResult<()> {
  let config = goldentests::TestConfig::new("target/debug/sylt", "tests", "--+ ")?;
  config.run_tests()
}
