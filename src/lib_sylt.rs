use crate::*;
use crate as sylt;

#[sylt_macro::sylt_link(push, "sylt::lib_sylt")]
pub fn dbg(values: &[Value], _typecheck: bool) -> Result<Value, RuntimeError> {
    println!(
        "{}: {:?}, {:?}",
        "DBG".purple(),
        values.iter().map(Type::from).collect::<Vec<_>>(),
        values
    );
    Ok(Value::Nil)
}

#[sylt_macro::sylt_link(push, "sylt::lib_sylt")]
pub fn push(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::List(ls), v], true) => {
            let ls: &RefCell<_> = ls.borrow();
            let ls = &ls.borrow();
            assert!(ls.len() == 1);
            let ls = Type::from(&ls[0]);
            let v: Type = Type::from(&*v);
            if ls == v {
                Ok(Value::Nil)
            } else {
                Err(RuntimeError::TypeMismatch(ls, v))
            }
        }
        ([Value::List(ls), v], false) => {
            // NOTE(ed): Deliberately no type checking.
            let ls: &RefCell<_> = ls.borrow();
            ls.borrow_mut().push(v.clone());
            Ok(Value::Nil)
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "push".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::extern_function!(
    "sylt::lib_sylt"
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

#[sylt_macro::sylt_link(inf, "sylt::lib_sylt")]
pub fn inf(values: &[Value], _typecheck: bool) -> Result<Value, RuntimeError> {
    match values {
        [x] => {
            let t: Type = Type::from(&*x);
            let x = x.clone();
            Ok(Value::Iter(t, Rc::new(RefCell::new(move || Some(x.clone())))))
        }
        values => Err(RuntimeError::ExternTypeMismatch(
            "push".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}


sylt_macro::sylt_link_gen!("sylt::lib_sylt");
