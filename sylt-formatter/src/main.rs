use std::fs;

use parser::module::Module;
use sylt_formatter::Args;

mod lib;
mod parser;

fn main() {
    let args = Args::parse_args_default_or_exit();

    let file = &args.args[0];

    let content = fs::read_to_string(file).unwrap();

    let tokens: Vec<_> = sylt_tokenizer::spanned_lexer(&content).collect();

    let res = Module::parse(&tokens);

    match res {
        Ok((_ctx, module)) => {
            dbg!(module);
        }

        Err((_ctx, parse_err)) => {
            println!("{}", parse_err.message());
        }
    }
}

// a :: 1
