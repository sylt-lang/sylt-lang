mod tokenizer;

fn main() {
    println!("Hello, world!");

    let tokens = tokenizer::file_to_tokens("tests/simple.tdy");

    for token in tokens.iter() {
        println!("| {:?}", token);
    }
}
