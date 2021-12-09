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
    write!(out, include_str!("preamble.lua"));

    let mut depth = 0;
    for instruction in ir.iter() {
        for _ in 0..depth {
            write!(out, "  ");
        }
        match instruction {
            IR::Nil(t) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = __NIL");
            }
            IR::Int(t, i) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = {}", i);
            }
            IR::Bool(t, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = {}", b);
            }
            IR::Add(t, a, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, "__ADD(");
                var(a, out);
                write!(out, ", ");
                var(b, out);
                write!(out, ")");
            }
            IR::Sub(t, a, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                var(a, out);
                write!(out, " - ");
                var(b, out);
            }
            IR::FunctionBegin(a, params) => {
                write!(out, "local ");
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
                depth += 1;
            }
            IR::FunctionEnd => {
                write!(out, "end");
                depth -= 1;
            }
            IR::Mul(t, a, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                var(a, out);
                write!(out, " * ");
                var(b, out);
            }
            IR::Div(t, a, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                var(a, out);
                write!(out, " / ");
                var(b, out);
            }
            IR::Copy(d, s) => {
                write!(out, "local ");
                var(d, out);
                write!(out, " = ");
                var(s, out);
            }
        }
        write!(out, "\n");
    }
}
