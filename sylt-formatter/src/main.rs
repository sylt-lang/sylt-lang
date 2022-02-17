use std::fs;

use sylt_formatter::Args;

mod lib;
mod parse;

fn main() {
    let args = Args::parse_args_default_or_exit();

    let file = &args.args[0];

    let content = fs::read_to_string(file).unwrap();

    let tokens: Vec<_> = sylt_tokenizer::spanned_lexer(&content).collect();

    let module = parse::parse_module(&tokens).unwrap();

    dbg!(module);
}

// a :: 1
