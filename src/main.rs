use std::io::{BufRead, BufReader, BufWriter};
use std::process::{Command, Stdio};

mod ast;
mod codegen;
mod error;
mod lexer;
mod name_resolution;
mod parser;
mod type_checker;

fn main() {
  let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

  // println!("=src=\n{}", src);

  let ast = match parser::parse(&src) {
    Err(err) => {
      eprintln!("parse err: {:?}", err);
      std::process::exit(1);
    }
    Ok(a) => a,
  };
  
  // println!("=ast=\n{:#?}", ast);

  let (names, named_ast) = match name_resolution::resolve(ast) {
    Err(err) => {
      eprintln!("name err: {:?}", err);
      std::process::exit(2);
    }
    Ok(a) => a,
  };

  let types = match type_checker::check(&names, &named_ast) {
    Err(err) => {
      eprintln!("check err: {:?}", err);
      std::process::exit(3);
    }
    Ok(a) => a,
  };

  let mut lua = Command::new("lua")
    .stdin(Stdio::piped())
    .spawn()
    .expect("Didn't find a `lua` executable");
  let mut out = lua.stdin.as_mut().unwrap();
  let mut code = BufWriter::new(&mut out);
  match codegen::gen(&mut code, &types, &names, &named_ast) {
    Err(err) => {
      eprintln!("file error: {:?}", err);
      std::process::exit(4);
    }
    Ok(a) => a,
  };
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

#[test]
fn run_golden_tests() -> goldentests::TestResult<()> {
  let config = goldentests::TestConfig::new("target/debug/sylt", "tests", "--+ ")?;
  config.run_tests()
}
