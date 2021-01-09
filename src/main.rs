mod tokenizer;
mod vm;

fn main() {
    /*
    let tokens = tokenizer::file_to_tokens("tests/simple.tdy");

    for token in tokens.iter() {
        println!("| {:?}", token);
    }
    */

    let mut blocks = vm::Block::new("main");
    blocks.add(vm::Op::Constant(vm::Value::Bool(true)));
    blocks.add(vm::Op::Print);
    blocks.add(vm::Op::Constant(vm::Value::Int(123)));
    blocks.add(vm::Op::Constant(vm::Value::Int(123)));
    blocks.add(vm::Op::Add);
    blocks.add(vm::Op::Print);
    blocks.add(vm::Op::Return);

    vm::run_block(blocks);
}
