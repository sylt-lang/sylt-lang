use std::path::Path;
use std::rc::Rc;

pub mod compiler;
pub mod tokenizer;
pub mod vm;

mod error;

use error::Error;
use tokenizer::TokenStream;

pub fn run_file(path: &Path, print: bool) -> Result<(), Vec<Error>> {
    run(tokenizer::file_to_tokens(path), path, print)
}

pub fn run_string(s: &str, print: bool) -> Result<(), Vec<Error>> {
    run(tokenizer::string_to_tokens(s), Path::new("builtin"), print)
}

pub fn run(tokens: TokenStream, path: &Path, print: bool) -> Result<(), Vec<Error>> {
    match compiler::compile("main", path, tokens) {
        Ok(blocks) => {
            let mut vm = vm::VM::new().print_blocks(print).print_ops(print);
            vm.typecheck(&blocks)?;
            if let Err(e) = vm.run(Rc::clone(&blocks[0])) {
                Err(vec![e])
            } else {
                Ok(())
            }
        }
        Err(errors) => Err(errors),
    }
}

#[cfg(test)]
mod tests {
    use super::{run_file, run_string};
    use std::path::Path;

    #[macro_export]
    macro_rules! assert_errs {
        ($result:expr, [ $( $kind:pat ),* ]) => {
            eprintln!("{} => {:?}", stringify!($result), $result);
            assert!(matches!(
                $result.unwrap_err().as_slice(),
                &[$($crate::error::Error {
                    kind: $kind,
                    file: _,
                    line: _,
                    message: _,
                },
                )*]
            ))
        };
    }

    #[macro_export]
    macro_rules! test_string {
        ($fn:ident, $prog:literal) => {
            #[test]
            fn $fn() {
                $crate::run_string($prog, true).unwrap();
            }
        };
        ($fn:ident, $prog:literal, $errs:tt) => {
            #[test]
            fn $fn() {
                $crate::assert_errs!($crate::run_string($prog, true), $errs);
            }
        }
    }

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal) => {
            #[test]
            fn $fn() {
                let file = Path::new($path);
                run_file(&file, true).unwrap();
            }
        };
    }

    use crate::error::ErrorKind;

    #[test]
    fn unreachable_token() {
        assert_errs!(run_string("<!>\n", true), [ErrorKind::Unreachable]);
    }

    macro_rules! test_multiple {
        ($mod:ident, $( $fn:ident : $prog:literal ),+ $( , )? ) => {
            mod $mod {
                $( test_string!($fn, $prog); )+
            }
        }
    }

    test_multiple!(
        order_of_operations,
        terms_and_factors: "1 + 1 * 2 <=> 3
                            1 * 2 + 3 <=> 5",
        in_rhs: "5 <=> 1 * 2 + 3",
        parenthesis: "(1 + 2) * 3 <=> 9",
        negation: "-1 <=> 0 - 1
                   -1 + 2 <=> 1
                   -(1 + 2) <=> -3
                   1 + -1 <=> 0
                   2 * -1 <=> -2",
    );

    test_multiple!(
        variables,
        single_variable: "a := 1
                          a <=> 1",
        two_variables: "a := 1
                        b := 2
                        a <=> 1
                        b <=> 2",
        stack_ordering: "a := 1
                         b := 2
                         b <=> 2
                         a <=> 1",
        assignment: "a := 1
                     b := 2
                     a = b
                     a <=> 2
                     b <=> 2",
    );

    test_multiple!(
        if_,
        compare_constants_equality: "if 1 == 2 {
                                       <!>
                                     }",
        compare_constants_unequality: "if 1 != 1 {
                                         <!>
                                       }",
        compare_variable: "a := 1
                           if a == 0 {
                             <!>
                           }
                           if a != 1 {
                             <!>
                           }",
        else_: "a := 1
                res := 0
                if a == 0 {
                  <!>
                } else {
                  res = 1
                }
                res <=> 1",
        else_if: "a := 1
                  res := 0
                  if a == 0 {
                    <!>
                  } else if a == 1 {
                    res = 1
                  } else {
                    <!>
                  }
                  res <=> 1",
    );

    test_file!(scoping, "tests/scoping.tdy");
    test_file!(for_, "tests/for.tdy");
    test_file!(fun, "tests/fun.tdy");
}
