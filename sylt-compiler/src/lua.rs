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
            IR::Int(t, i) => {
                var(t, out);
                write!(out, " = {}", i);
            }
            IR::AddInt(t, a, b) => {
                var(t, out);
                write!(out, " = ");
                var(a, out);
                write!(out, " + ");
                var(b, out);
            }
        }
        out.write_all(b"\n");
    }
}
