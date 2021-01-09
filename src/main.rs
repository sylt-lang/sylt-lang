mod tokenizer;
mod vm;
mod compiler;

fn main() {
    let tokens = tokenizer::file_to_tokens("tests/simple.tdy");

    let block = compiler::compile("main", tokens);

    vm::run_block(block);
}
