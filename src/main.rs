use chumsky::Parser;
mod lexer;
mod parser;
mod parser_new;
mod ast;


fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    println!("src: {}", src);

    println!("src: {:?}", parser::parser().parse(src));
}
