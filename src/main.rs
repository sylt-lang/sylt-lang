#![feature(box_patterns)]

use gumdrop::Options;
use std::collections::BinaryHeap;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;
use std::process::{exit, Command, Stdio};

pub mod ast;
pub mod codegen;
pub mod error;
pub mod hexer;
pub mod lexer;
pub mod name_resolution;
pub mod parser;
pub mod type_checker;

#[derive(Options)]
struct Args {
  #[options(help = "print help message")]
  help: bool,

  #[options(required, free, help = "the source files to compile")]
  source: Vec<String>,

  #[options(
    short = 'o',
    long = "operators",
    help = "a source file defining operators and their precedence"
  )]
  operators: Option<String>,

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
    short = 'c',
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

  #[options(
    short = 'x',
    long = "no-preamble",
    help = "Don't include the preamble automatically"
  )]
  no_preamble: bool,
}

pub const PREAMBLE: &'static str = include_str!("preamble.sy");
pub const OPERATORS: &'static str = include_str!("operators.syop");

fn main() {
  let args = Args::parse_args_default_or_exit();

  let operator_source = args
    .operators
    .as_ref()
    .map(|f| std::fs::read_to_string(f))
    .unwrap_or_else(|| Ok(OPERATORS.to_string()));
  let ops = match operator_source.as_ref() {
    Ok(src) => hexer::parse(&src),
    Err(e) => Err(error::Error::Special(format!(
      "Failed to open operator source file {:?}: {}",
      args.operators, e
    ))),
  }
  .map_err(|e| e.render(&[]));

  let ops = match ops {
    Ok(ops) => ops,
    Err(e) => {
      eprintln!("{}", e);
      exit(1);
    }
  };

  let preamble = "PREAMBLE";
  let files_in_order = args
    .source
    .clone()
    .into_iter()
    .chain([preamble.to_string()].into_iter())
    .collect::<BinaryHeap<_>>();
  let mut errors = Vec::new();
  let mut srcs: Vec<Option<(String, String)>> = Vec::new();
  let mut asts = Vec::new();
  for filename in files_in_order.iter() {
    if *filename == preamble {
      if !args.no_preamble {
        srcs.push(Some((filename.to_string(), PREAMBLE.to_string())));
      }
    } else {
      match std::fs::read_to_string(&filename) {
        Ok(src) => {
          srcs.push(Some((filename.to_string(), src)));
        }
        Err(e) => {
          srcs.push(None);
          errors.push(
            error::Error::Special(format!("Failed to open source file {:?}: {}", &filename, e))
              .render(&[]),
          );
          continue;
        }
      };
    }
  }

  for (file_id, filename) in files_in_order.iter().enumerate() {
    let src = match srcs.get(file_id) {
      Some(Some((_, src))) => src,
      _ => continue,
    };
    match parser::parse(&src, file_id, ops.clone()) {
      Ok(ast) => {
        match args.dump_ast.as_ref() {
          _ if filename == preamble => {}
          Some(s) if s == "-" => println!("{}\n{:#?}", filename, ast),
          Some(s) => std::fs::write(format!("{}_{}.ast", s, filename), format!("{:#?}", ast))
            .expect("Failed to write AST to file"),
          None => {}
        }
        asts.push(Some(ast));
      }
      Err(errs) => {
        asts.push(None);
        for e in errs.iter() {
          errors.push(e.render(srcs.as_slice()));
        }
        continue;
      }
    };
  }

  if !errors.is_empty() {
    for e in errors.iter() {
      eprintln!("{}", e);
    }
    exit(1);
  }

  let combined_ast: Vec<(ast::ProperName<'_>, ast::Def<'_>)> = asts
    .into_iter()
    .filter_map(|x| x)
    .map(|(m, xs)| xs.into_iter().map(|x| (m, x)).collect::<Vec<_>>())
    .flatten()
    .collect::<Vec<_>>();
  let (names, fields, named_ast) = match name_resolution::resolve(combined_ast) {
    Err(errs) => {
      for e in errs.iter() {
        eprintln!("{}", e.render(srcs.as_slice()));
      }
      exit(6);
    }
    Ok(a) => a,
  };

  // TODO[et]: Can I remove this clone somehow?
  let (types, errors) = type_checker::check(&names, &named_ast, &fields);
  if !errors.is_empty() {
    for e in errors.iter() {
      eprintln!("{}", e.render(srcs.as_slice()));
    }
    exit(1);
  }
  let named_ast = name_resolution::sort_and_trim(&names, named_ast.clone());
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
  let mut config = goldentests::TestConfig::new("target/debug/sylt", "tests", "--+ ")?;
  config.overwrite_tests = std::env::var("OVERWRITE").is_ok();
  config.run_tests()
}
