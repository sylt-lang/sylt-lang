use criterion::{criterion_group, criterion_main, Criterion};
use std::fs;
use std::path::Path;

macro_rules! bench_file {
    ( $name:ident ) => {
        pub fn $name(c: &mut Criterion) {
            let prog =
                fs::read_to_string(Path::new(&format!("progs/bench/{}.sy", stringify!($name))))
                    .unwrap();
            c.bench_function(stringify!($name), |b| {
                b.iter(|| {
                    sylt::run_string(&prog, false, Vec::new()).unwrap();
                })
            });
        }
    };
}

macro_rules! bench {
    ( [ $( $name:ident ),* ] ) => {
        $(bench_file!($name);)*

        criterion_group!(benches, $( $name ),* );
        criterion_main!(benches);
    }
}

// List of all benchmarks to run
bench!([fib, fib_iter, sum]);
