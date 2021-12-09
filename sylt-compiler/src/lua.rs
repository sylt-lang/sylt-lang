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

pub fn bin_op(out: &mut dyn Write, t: &Var, a: &Var, b: &Var, op: &str) {
    write!(out, "local ");
    var(t, out);
    write!(out, " = ");
    var(a, out);
    write!(out, " {} ", op);
    var(b, out);
}

pub fn comma_sep(out: &mut dyn Write, vars: &[Var]) {
    for (i, v) in vars.iter().enumerate() {
        if i != 0 {
            write!(out, ", ");
        }
        var(v, out);
    }
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
            IR::Sub(t, a, b) => bin_op(out, t, a, b, "-"),
            IR::Mul(t, a, b) => bin_op(out, t, a, b, "*"),
            IR::Div(t, a, b) => bin_op(out, t, a, b, "/"),

            IR::FunctionBegin(a, params) => {
                write!(out, "local ");
                write!(out, "function ");
                var(a, out);
                write!(out, "(");
                comma_sep(out, params);
                write!(out, ")");
                depth += 1;
            }
            IR::FunctionEnd => {
                write!(out, "end");
                depth -= 1;
            }
            IR::Neg(t, a) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, "-");
                var(a, out);
            }
            IR::Copy(d, s) => {
                write!(out, "local ");
                var(d, out);
                write!(out, " = ");
                var(s, out);
            }
            IR::External(t, e) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, e);
            }
            IR::Call(t, f, args) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                var(f, out);
                write!(out, "(");
                comma_sep(out, args);
                write!(out, ")");
            }
            IR::Assert(v) => {
                write!(out, "assert(");
                var(v, out);
                write!(out, ", \":(\")");
            }
            IR::Str(t, s) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = \"{}\"", s);
            }
            IR::Float(t, f) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = \"{}\"", f);
            }
            IR::Equals(t, a, b) => bin_op(out, t, a, b, "=="),
            IR::NotEquals(t, a, b) => bin_op(out, t, a, b, "~="),
            IR::Greater(t, a, b) => bin_op(out, t, a, b, ">"),
            IR::GreaterEqual(t, a, b) => bin_op(out, t, a, b, ">="),
            IR::Less(t, a, b) => bin_op(out, t, a, b, "<"),
            IR::LessEqual(t, a, b) => bin_op(out, t, a, b, "<="),
            IR::In(t, a, b) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, "__CONTAINS(");
                var(a, out);
                write!(out, ", ");
                var(b, out);
                write!(out, ")");
            }

            IR::List(t, exprs) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, "__LIST{");
                comma_sep(out, exprs);
                write!(out, "}");
            }
            IR::Tuple(t, exprs) => {
                write!(out, "local ");
                var(t, out);
                write!(out, " = ");
                write!(out, "__TUPLE{");
                comma_sep(out, exprs);
                write!(out, "}");
            }
        }
        write!(out, "\n");
    }
}
