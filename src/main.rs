use std::path::{Path, PathBuf};

use sylt::{run_file, Value, Type, error::ErrorKind};
use std::borrow::Borrow;
use std::cell::RefCell;

struct Args {
    file: Option<PathBuf>,
    print: bool,
}

fn main() {
    let args = parse_args();
    let file = args.file.unwrap_or_else(|| Path::new("progs/tests/simple.sy").to_owned());
    let errs = match run_file(&file, args.print, sylt_macro::link!(
        extern_test as test,
        dbg,
        push,
        len,
    )) {
        Err(it) => it,
        _ => return,
    };
    for err in errs.iter() {
        println!("{}", err);
    }
    println!(" {} errors occured.", errs.len());
}

fn parse_args() -> Args {
    let mut args = Args {
        file: None,
        print: false,
    };

    for s in std::env::args().skip(1) {
        let path = Path::new(&s).to_owned();
        if path.is_file() {
            args.file = Some(path);
        } else if "-p" == s {
            args.print = true;
        } else {
            eprintln!("Invalid argument {}.", s);
        }
    };
    args
}

sylt_macro::extern_function!(
    extern_test
    [sylt::Value::Float(x), sylt::Value::Float(y)] -> sylt::Type::Float => {
        Ok(sylt::Value::Float(x + y))
    },
    [sylt::Value::Float(x)] -> sylt::Type::Float => {
        Ok(sylt::Value::Float(*x))
    },
);

sylt_macro::extern_function!(
    dbg
    [x] -> sylt::Type::Void => {
        println!("DBG: {:?}, {:?}", x, Type::from(x));
        Ok(sylt::Value::Nil)
    },
);

pub fn push(values: &[Value], typecheck: bool) -> Result<Value, ErrorKind> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls: &RefCell<Vec<Value>> = ls.borrow();
            let ls = ls.borrow();
            assert!(ls.len() == 1);
            let ls = Type::from(&ls[0]);
            let v = Type::from(&*v);
            if ls == v {
                Ok(Value::Nil)
            } else {
                Err(ErrorKind::TypeMismatch(ls, v))
            }
        }
        ([Value::List(ls), v], false) => {
            // NOTE(ed): Deliberattly no type checking.
            let ls: &RefCell<Vec<Value>> = ls.borrow();
            ls.borrow_mut().push(v.clone());
            Ok(Value::Nil)
        }
        (values, _) => {
            Err(ErrorKind::ExternTypeMismatch(
                "push".to_string(),
                values.iter().map(|x| Type::from(x)).collect()
            ))
        }
    }
}

sylt_macro::extern_function!(
    len
    [Value::List(ls)] -> Type::Int => {
        let ls: &RefCell<Vec<Value>> = ls.borrow();
        let ls = ls.borrow();
        Ok(Value::Int(ls.len() as i64))
    },
    [Value::Tuple(ls)] -> Type::Int => {
        Ok(Value::Int(ls.len() as i64))
    },
);
