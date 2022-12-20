use std::fs::File;

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
    Err(err) => return eprintln!("parse err: {:?}", err),
    Ok(a) => a,
  };

  let (names, named_ast) = match name_resolution::resolve(ast) {
    Err(err) => return eprintln!("name err: {:?}", err),
    Ok(a) => a,
  };

  let types = match type_checker::check(&names, &named_ast) {
    Err(err) => return eprintln!("check err: {:?}", err),
    Ok(a) => a,
  };

  let mut file = File::create("out.lua").unwrap();
  let code = match codegen::gen(&mut file, &types, &names, &named_ast) {
    Err(err) => return eprintln!("file error: {:?}", err),
    Ok(a) => a,
  };
  // println!("OUT: {:?}", types);
}
