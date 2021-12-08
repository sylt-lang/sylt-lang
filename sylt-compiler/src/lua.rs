use crate::intermediate::{Var, IR};
use std::io::Write;

macro_rules! write {
    ($out:expr, $msg:expr ) => {
        // :3
        let _ = $out.write($msg.as_ref());
    };
    ($out:expr, $( $msg:expr ),+ ) => {
        let _ = $out.write(format!($( $msg ),*).as_ref());
    };
}

fn var(Var(v): &Var, out: &mut dyn Write) {
    write!(out, "V{}", v);
}

pub fn generate(ir: &Vec<IR>, out: &mut dyn Write) {
    let mut depth = 0;
    for instruction in ir.iter() {
        // TODO indent
        write!(out, "local ");
        match instruction {
            IR::Nil(t) => {
                var(t, out);
                write!(out, " = __NIL");
            }
            IR::Int(t, i) => {
                var(t, out);
                write!(out, " = {}", i);
            }
            IR::Bool(t, b) => {
                var(t, out);
                write!(out, " = {}", b);
            }
            IR::Add(t, a, b) => {
                var(t, out);
                write!(out, " = ");
                write!(out, "__ADD(");
                var(a, out);
                write!(out, ", ");
                var(b, out);
                write!(out, ")");
            }
            IR::Sub(t, a, b) => {
                var(t, out);
                write!(out, " = ");
                var(a, out);
                write!(out, " - ");
                var(b, out);
            }
            IR::FunctionBegin(a, params) => {
                write!(out, "function ");
                var(a, out);
                write!(out, "(");
                for (i, param) in params.iter().enumerate() {
                    if i != 0 {
                        write!(out, ", ");
                    }
                    var(param, out);
                }
                write!(out, ")");
            }
            IR::FunctionEnd => {
                write!(out, "end");
            }
        }
        write!(out, "\n");
    }
}
