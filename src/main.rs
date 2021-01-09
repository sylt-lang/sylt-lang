mod tokenizer;
mod vm;
mod compiler;

fn main() {
    let file = "tests/simple.tdy";
    let tokens = tokenizer::file_to_tokens(file);

    for token in tokens.iter() {
        println!("{:?}", token);
    }

    let block = compiler::compile("main", file, tokens);

    vm::run_block(block);
}
