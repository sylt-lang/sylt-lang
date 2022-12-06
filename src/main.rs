mod ast;
mod error;
mod lexer;
mod name_resolution;
mod parser;

fn main() {
  let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

  println!("src: {}", src);

  let ast = match parser::parse(&src) {
    Err(err) => return println!("err: {:?}", err),
    Ok(a) => a,
  };

  let resolved = match name_resolution::resolve(ast) {
    Err(err) => return println!("err: {:?}", err),
    Ok(a) => a,
  };
  println!("OUT: {:?}", resolved);
}
