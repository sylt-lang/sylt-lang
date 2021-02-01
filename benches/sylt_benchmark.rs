use criterion::{criterion_group, criterion_main, Criterion};
use std::path::Path;

pub fn fib_50(c: &mut Criterion) {
    let prog =
"
j := 0
for , j < 1000, j = j + 1 {
    a := 0
    b := 1

    for i := 0, i < 50, i = i + 1 {
        c := a
        a = b
        b = c + b
    }
    a <=> 12586269025
}
";
    let compiled = sylt::compiler::compile("main", Path::new("prog"), sylt::tokenizer::string_to_tokens(prog)).unwrap();
    c.bench_function("fib 50", |b| b.iter(|| sylt::vm::run_block(&compiled).unwrap()));
}

pub fn fib_90(c: &mut Criterion) {
    let prog =
"
a := 0
b := 1

for i := 0, i < 90, i = i + 1 {
    c := a
    a = b
    b = c + b
}
a <=> 2880067194370816120
";
    let compiled = sylt::compiler::compile("main", Path::new("prog"), sylt::tokenizer::string_to_tokens(prog)).unwrap();
    c.bench_function("fib 90", |b| b.iter(|| sylt::vm::run_block(&compiled).unwrap()));
}

criterion_group!(benches, fib_50, fib_90);
criterion_main!(benches);
