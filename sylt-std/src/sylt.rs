#![allow(unused)]
use crate as sylt_std;

use colored::Colorize;
use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;
use sungod::Ra;
use sylt_common::error::RuntimeError;
use sylt_common::{Blob, RuntimeContext, Type, Value};

sylt_macro::extern_function!(
    "sylt_std::sylt",
    atan2,
    ? "Returns the angle of a direction relative to +x, where the first argument is x",
    -> "fn float, float -> float",
    [Float(x), Float(y)] => {
        Ok(Float(y.atan2(*x)))
    },
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    dbg,
    ? "Prints values to stdout",
    -> "fn #X -> #X",
    [value] => {
        println!(
            "DBG: {:?}, {:?}",
            Type::from(value),
            value
        );
        Ok(value.clone())
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    random_choice,
    ? "Selects an element randomly from a list",
    -> "fn [#ITEM] -> #ITEM",
    [Value::List(list)] => {
        Ok(list.borrow()[Ra::ggen::<usize>() % list.borrow().len()].clone())
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    for_each,
    ? "Does something for each element in a list",
    -> "fn [#ITEM], fn #ITEM -> void -> void",
    [List(list), callable] => {
        let list = Rc::clone(list);
        let callable = callable.clone();
        for element in list.borrow().iter() {
            ctx.machine.eval_call(callable.clone(), &[element]).unwrap();
        }
        Ok(Nil)
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    map,
    ? "Applies a function to all elements in a list",
    -> "fn [#ITEM], fn #ITEM -> #OUT -> [#OUT]",
    [List(list), callable] => {
        let list = Rc::clone(list);
        let callable = callable.clone();
        let mapped = list
            .borrow()
            .iter()
            .map(|element| ctx.machine.eval_call(callable.clone(), &[element]).unwrap())
            .collect();
        Ok(List(Rc::new(RefCell::new(mapped))))
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    reduce,
    ? "Reduce the list to a single element, returns 'nil' if the input list is empty",
    -> "fn [#ITEM], fn #ITEM, #ITEM -> #OUT -> #OUT",
    [List(list), callable] => {
        let list = Rc::clone(list);
        let callable = callable.clone();
        let reduced = list
            .borrow()
            .iter()
            .cloned()
            .reduce(|a, b| ctx.machine.eval_call(callable.clone(), &[&a, &b]).unwrap());
        Ok(reduced.unwrap_or(Value::Nil))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    fold,
    ? "Applies a function to all elements pairwise in order, starts with the accumulator",
    -> "fn #ITEM, [#ITEM], fn #ITEM, #ITEM -> #OUT -> #OUT",
    [start, List(list), callable] => {
        let list = Rc::clone(list);
        let callable = callable.clone();
        let folded = list
            .borrow()
            .iter()
            .fold(start.clone(), |a, b| ctx.machine.eval_call(callable.clone(), &[&a, &b]).unwrap());
        Ok(folded)
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    filter,
    ? "Creates a new list with the elements that pass the test function",
    -> "fn [#ITEM], fn #ITEM -> bool -> [#ITEM]",
    [List(list), callable] => {
        let list = Rc::clone(list);
        let callable = callable.clone();
        let filtered = list
            .borrow()
            .iter()
            .filter(|element| ctx.machine.eval_call(callable.clone(), &[element]).unwrap() == Bool(true))
            .cloned()
            .collect();
        Ok(List(Rc::new(RefCell::new(filtered))))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    args,
    ? "Returns the args parsed into a dict, split on =",
    -> "fn -> {str:str}",
    values => {
        let mut args = HashMap::new();
        args.insert(Value::from("prog"), Value::from(ctx.machine.args()[0].as_str()));

        for arg in ctx.machine.args().iter().skip(1) {
            let (pre, suf) = arg.split_once("=").unwrap_or((arg.as_str(), ""));
            args.insert(Value::from(pre), Value::from(suf));
        }
        Ok(Dict(Rc::new(RefCell::new(args))))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    push,
    ? "Appends an element to the end of a list",
    -> "fn [#ITEM], #ITEM -> void",
    [List(ls), v] => {
        ls.borrow_mut().push(v.clone());
        Ok(Nil)
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    add,
    ? "Inserts a value into a set",
    -> "fn {#ITEM}, #ITEM -> void",
    [Set(ls), v] => {
        // NOTE(ed): Deliberately no type checking.
        ls.borrow_mut().insert(v.clone());
        Ok(Nil)
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    clear,
    ? "Removes all elements from the list",
    -> "fn [#ITEM] -> void",
    [List(ls)] => {
        // NOTE(ed): Deliberately no type checking.
        ls.borrow_mut().clear();
        Ok(Nil)
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    prepend,
    ? "Adds an element to the start of a list",
    -> "fn [#ITEM] -> void",
    [List(ls), v] => {
        // NOTE(ed): Deliberately no type checking.
        ls.borrow_mut().insert(0, v.clone());
        Ok(Value::Nil)
    }
);


// TODO(er): Add length of string, set and tuple(?)
sylt_macro::extern_function!(
    "sylt_std::sylt",
    len,
    ? "Gives the length of list",
    -> "fn [#ITEM] | {#KEY: #VALUE} -> int",
    [List(ls)] => {
        Ok(Int(ls.borrow().len() as i64))
    },
    [Dict(ls)] => {
        Ok(Int(ls.borrow().len() as i64))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    sin,
    ? "The sine function you know and love from trigonometry class",
    -> "fn float -> float",
    [Float(t)] => {
        Ok(Float(t.sin()))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    cos,
    ? "The cosine function you know and love from trigonometry class",
    -> "fn float -> float",
    [Float(t)] => {
        Ok(Float(t.cos()))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    as_float,
    ? "Converts an int to a float",
    -> "fn int -> float",
    [Int(t)] => {
        Ok(Float(*t as f64))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    as_int,
    ? "Converts something to an int",
    -> "fn float -> int",
    [Float(t)] => {
        Ok(Int(*t as i64))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    as_char,
    ? "Converts a string containing a single char to an int",
    -> "fn str -> int",
    [Value::String(s)] => {
        let mut chars = s.chars();
        let c = match chars.next() {
            Some(c) => c,
            //TODO(gu): Actually what went wrong
            None => return Err(RuntimeError::ExternTypeMismatch("as_char".to_string(), vec![Type::String])),
        };
        if chars.next().is_none() {
            Ok(Int(c as i64))
        } else {
            //TODO(gu): Actually what went wrong
            Err(RuntimeError::ExternTypeMismatch("as_char".to_string(), vec![Type::String]))
        }
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    floor,
    ? "Rounds a float down (towards -inf)",
    -> "fn float -> int",
    [Float(t)] => { Ok(Int(t.floor() as i64)) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    as_chars,
    ? "Converts an ASCII string into a list of chars. Non-ASCII is converted to '?'.",
    -> "str -> [int]",
    [Value::String(s)] => {
        let chars = s
            .chars()
            .map(|c|
                if c.is_ascii()
                    || c == 'å'
                    || c == 'ä'
                    || c == 'ö'
                {
                    c
                } else {
                    '?'
                } as i64
            )
            .map(Int)
            .collect();

        Ok(List(Rc::new(RefCell::new(chars))))
    },
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    sqrt,
    ? "Returns the square root",
    -> "fn float -> float",
    [Float(x)] => { Ok(Float(x.sqrt())) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    abs,
    ? "Returns the absolute value",
    -> "fn float -> float",
    [Float(x)] => { Ok(Float(x.abs())) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    sign,
    ? "Returns the sign of the value",
    -> "fn #X -> #X", // TODO(ed): Figure out how we can limit x...
    [Float(x)] => { Ok(Float(x.signum())) },
    [Int(x)] => { Ok(Int(x.signum())) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    clamp,
    ? "Clamps the value 'a' between 'lo' and 'hi'",
    -> "fn #X, #X, #X -> #X", // TODO(ed): Figure out how we can limit x...
    [Float(a), Float(lo), Float(hi)] => { Ok(Float(a.min(*hi).max(*lo))) },
    [Int(a), Int(lo), Int(hi)] => { Ok(Int(*a.min(hi).max(lo))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    min,
    ? "Returns the smallest",
    -> "fn float, float -> float",
    [Float(a), Float(b)] => { Ok(Float(a.min(*b))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    max,
    ? "Returns the largest",
    -> "fn float, float -> float",
    [Float(a), Float(b)] => { Ok(Float(a.max(*b))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    rem,
    ? "Returns the value x modulo y",
    -> "fn #X, #X -> #X",
    [Float(x), Float(y)] => { Ok(Float(x.rem_euclid(*y))) },
    [Int(x), Int(y)] => { Ok(Int(x.rem_euclid(*y))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    pow,
    ? "Raises the first argument to the power of the second argument",
    -> "fn float, float -> float",
    [Float(x), Float(y)] => { Ok(Float(x.powf(*y))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    angle,
    ? "Calculates the angle of a 2d vector",
    -> "fn (float, float) -> float",
    [Tuple(v)] => {
        let (x, y) = break_up_vec(v);
        Ok(Float(y.atan2(x)))
    },
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    magnitude_squared,
    ? "Calculates the squared magnitude of the tuple as a vector",
    -> "fn (float, float) -> float",
    [Tuple(ls)] => {
        let mut sum = 0.0;
        for value in ls.iter() {
            if let Float(value) = value {
                sum += value * value;
            }
        }
        Ok(Float(sum))
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    magnitude,
    ? "Calculates the squared magnitude of the tuple as a vector",
    -> "fn (float, float) -> float",
    _ => {
        if let Value::Float(mag) = magnitude_squared(ctx)? {
            Ok(Value::Float(mag.abs().sqrt()))
        } else {
            unreachable!();
        }
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    normalize,
    ? "Returns a unit length vector pointing in the same direction.",
    -> "fn (float, float) -> (float, float)",
    [Tuple(v)] => {
        let (x, y) = break_up_vec(v);
        let length = (x * x + y * y).sqrt();
        let (x, y) = if length != 0.0 {
            (x / length, y / length)
        } else {
            (x, y)
        };
        Ok(Tuple(Rc::new(vec![Float(x), Float(y)])))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    reflect,
    ? "Flips the component of 'v' that points towards 'n'",
    -> "fn (float, float), (float, float) -> (float, float)",
    [Tuple(v), Tuple(n)] => {
        let (vx, vy) = break_up_vec(v);
        let (nx, ny) = break_up_vec(n);
        let s = 2.0 * (vx * nx + vy * ny);
        Ok(Tuple(Rc::new(vec![Float(vx - s * nx), Float(vy - s * ny)])))
    },
);

fn break_up_vec(vec: &[Value]) -> (f64, f64) {
    use Value::Float;
    match vec {
        [Float(x), Float(y)] => (*x, *y),
        _ => panic!("Only suport 2d vectors!"),
    }
}

sylt_macro::extern_function!(
    "sylt_std::sylt",
    dot,
    ? "Computes the scalar product",
    -> "fn (float, float) -> float",
    [Tuple(a), Tuple(b)] => {
        let (ax, ay) = break_up_vec(a);
        let (bx, by) = break_up_vec(b);
        Ok(Float(ax * bx + ay * by))
    }
);
sylt_macro::extern_function!(
    "sylt_std::sylt",
    debug_assertions,
    ? "Whether the sylt runtime was compiled with debug assertions or not.",
    -> "fn -> bool",
    [] => { Ok(Bool(cfg!(debug_assertions))) }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    pop,
    ? "Removes the last element in the list, and returns it",
    -> "fn [#ITEM] -> #ITEM?",
    [List(ls)] => {
        Ok(ls.borrow_mut().pop().unwrap_or(Nil))
    }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    last,
    ? "Returns the last element in a list",
    -> "fn [#ITEM] -> #ITEM?",
    [List(ls)] => {
        Ok(ls.borrow().last().cloned().unwrap_or(Nil))
    }
);


sylt_macro::extern_function!(
    "sylt_std::sylt",
    thread_sleep,
    ? "Sleep (blocking) for some time.",
    -> "fn float -> void",
    [Float(secs)] => {
        std::thread::sleep(std::time::Duration::from_secs_f64(*secs));
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    as_str,
    ? "Converts to a string representation",
    -> "fn #X -> str",
    [v] => { Ok(Value::String(Rc::new(v.to_string()))) }
);

sylt_macro::extern_function!(
    "sylt_std::sylt",
    print,
    ? "Prints values to stdout",
    -> "fn #X -> void",
    _ => {
        println!("{}", ctx.machine
            .stack_from_base(ctx.stack_base)
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(" "));
        Ok(Nil)
    }
);

sylt_macro::sylt_link_gen!("sylt_std::sylt");
