mod ast;
mod lexer;
mod parser;

fn main() {
  let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

  println!("src: {}", src);

  println!("src: {:?}", parser::parse(&src));
}
