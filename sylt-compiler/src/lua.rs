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

pub fn bin_op(out: &mut dyn Write, t: &Var, a: &Var, b: &Var, op: &str) {
    write!(out, "local ");
    write!(out, "{}", t);
    write!(out, " = ");
    write!(out, "{}", a);
    write!(out, " {} ", op);
    write!(out, "{}", b);
}

pub fn comma_sep(out: &mut dyn Write, vars: &[Var]) {
    for (i, v) in vars.iter().enumerate() {
        if i != 0 {
            write!(out, ", ");
        }
        write!(out, "{}", v);
    }
}

pub fn generate(ir: &Vec<IR>, out: &mut dyn Write) {
    write!(out, include_str!("preamble.lua"));

    let mut depth = 0;
    for instruction in ir.iter() {
        depth += match instruction {
            IR::Else | IR::End => -1,
            _ => 0,
        };

        for _ in 0..depth {
            write!(out, "  ");
        }
        match instruction {
            IR::Nil(t) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = __NIL");
            }
            IR::Int(t, i) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = {}", i);
            }
            IR::Bool(t, b) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = {}", b);
            }
            IR::Add(t, a, b) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__ADD(");
                write!(out, "{}", a);
                write!(out, ", ");
                write!(out, "{}", b);
                write!(out, ")");
            }
            IR::Sub(t, a, b) => bin_op(out, t, a, b, "-"),
            IR::Mul(t, a, b) => bin_op(out, t, a, b, "*"),
            IR::Div(t, a, b) => bin_op(out, t, a, b, "/"),

            IR::Function(f, params) => {
                write!(out, "local ");
                write!(out, "function ");
                write!(out, "{}", f);
                write!(out, "(");
                comma_sep(out, params);
                write!(out, ")");
                depth += 1;
            }
            IR::Neg(t, a) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "-");
                write!(out, "{}", a);
            }
            IR::Copy(d, s) => {
                write!(out, "local ");
                write!(out, "{}", d);
                write!(out, " = ");
                write!(out, "{}", s);
            }
            IR::External(t, e) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, e);
            }
            IR::Call(t, f, args) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "{}", f);
                write!(out, "(");
                comma_sep(out, args);
                write!(out, ")");
            }
            IR::Assert(v) => {
                write!(out, "assert(");
                write!(out, "{}", v);
                write!(out, ", \":(\")");
            }
            IR::Str(t, s) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = \"{}\"", s);
            }
            IR::Float(t, f) => {
                write!(out, "local ");
                write!(out, "{}", t);
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
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__CONTAINS(");
                write!(out, "{}", a);
                write!(out, ", ");
                write!(out, "{}", b);
                write!(out, ")");
            }

            IR::And(t, a, b) => bin_op(out, t, a, b, "and"),
            IR::Or(t, a, b) => bin_op(out, t, a, b, "or"),
            IR::Not(t, a) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "not ");
                write!(out, "{}", a);
            }

            IR::List(t, exprs) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__LIST{");
                comma_sep(out, exprs);
                write!(out, "}");
            }

            IR::Set(t, exprs) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__SET{");
                write!(
                    out,
                    "{}",
                    exprs
                        .iter()
                        .map(|v| format!("[{}] = true", v))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                write!(out, "}");
            }

            IR::Dict(t, exprs) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__DICT{");
                write!(
                    out,
                    "{}",
                    exprs
                        .windows(2)
                        .step_by(2)
                        .map(|v| match v {
                            [k, v] => {
                                format!("[{}] = {}", k, v)
                            }
                            _ => unreachable!(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                write!(out, "}");
            }

            IR::Blob(t, fields) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__BLOB{");
                write!(
                    out,
                    "{}",
                    fields
                        .iter()
                        .map(|(f, v)| format!("{} = {}", f, v))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                write!(out, "}");
            }

            IR::Tuple(t, exprs) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__TUPLE{");
                comma_sep(out, exprs);
                write!(out, "}");
            }

            IR::Define(t) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "nil");
            }
            IR::Assign(t, a) => {
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "{}", a);
            }
            IR::If(a) => {
                write!(out, "if ");
                write!(out, "{}", a);
                write!(out, " then");
                depth += 1;
            }
            IR::Else => {
                write!(out, "else");
                depth += 1;
            }
            IR::End => {
                write!(out, "end");
            }
            IR::Loop => {
                write!(out, "while true do");
                depth += 1;
            }
            IR::Break => {
                write!(out, "break");
            }
            IR::Continue => {
                write!(out, "continue");
            }
            IR::Return(t) => {
                write!(out, "return ");
                write!(out, "{}", t);
            }
            IR::HaltAndCatchFire(msg) => {
                write!(out, "__CRASH(\"{}\")()", msg);
            }
            IR::Variant(t, v, a) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__VARIANT{");
                write!(out, "\"{}\", {}", v, a);
                write!(out, "}");
            }
            IR::Index(t, a, i) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "__INDEX(");
                write!(out, "{}, {}", a, i);
                write!(out, ")");
            }
            IR::AssignIndex(t, i, a) => {
                write!(out, "__ASSIGN_INDEX(");
                write!(out, "{}, {}, {}", t, i, a);
                write!(out, ")");
            }
            IR::Access(t, a, f) => {
                write!(out, "local ");
                write!(out, "{}", t);
                write!(out, " = ");
                write!(out, "{}.{}", a, f);
            }
            IR::AssignAccess(t, f, c) => {
                write!(out, "{}.{}", t, f);
                write!(out, " = ");
                write!(out, "{}", c);
            }
        }
        write!(out, "\n");
    }
}
