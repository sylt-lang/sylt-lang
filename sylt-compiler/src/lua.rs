use crate::intermediate::{Var, IR};
use std::{collections::HashMap, io::Write};

macro_rules! write {
    ($out:expr, $msg:expr ) => {
        // :3
        let _ = $out.write($msg.as_ref());
    };
    ($out:expr, $( $msg:expr ),+ ) => {
        let _ = $out.write(format!($( $msg ),*).as_ref());
    };
}

macro_rules! ii {
    ( $self:expr, $var:expr, $fmt:literal, $a:expr ) => {
        iis!($self, $var, $fmt, $self.expand($a))
    };

    ( $self:expr, $var:expr, $fmt:literal, $a:expr, $b:expr ) => {{
        let a = $self.expand($a).to_string();
        let b = $self.expand($b);
        iis!($self, $var, $fmt, a, b)
    }};
}

macro_rules! iis {
    ( $self:expr, $var:expr, $fmt:literal, $( $dep:expr ),* ) => {
        Some(($var, format!($fmt, $( $dep ),*)))
    };
    ( $self:expr, $var:expr, $fmt:literal) => {
        Some(($var, $fmt.into()))
    };
}

struct Generator<'a, 'b> {
    usage_count: &'a HashMap<Var, usize>,
    out: &'b mut dyn Write,
    lut: HashMap<Var, String>,
}

impl<'a, 'b> Generator<'a, 'b> {
    pub fn new(usage_count: &'a HashMap<Var, usize>, out: &'b mut dyn Write) -> Self {
        Self { usage_count, out, lut: HashMap::new() }
    }

    fn comma_sep(&mut self, vars: &[Var]) -> String {
        vars.iter()
            .map(|v| format!("{}", self.expand(v)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn expand(&mut self, var: &Var) -> String {
        match self.lut.get(var) {
            Some(var) => var.into(),
            None => var.to_string(),
        }
    }

    fn define(&mut self, var: Var, value: String) {
        self.lut.insert(var, value);
    }

    pub fn generate(&mut self, ir: &Vec<IR>) {
        write!(self.out, include_str!("preamble.lua"));

        let mut depth = 0;
        for instruction in ir.iter() {
            depth += match instruction {
                IR::Else | IR::End => -1,
                _ => 0,
            };

            for _ in 0..depth {
                write!(self.out, "  ");
            }
            let expr = match instruction {
                IR::Nil(t) => iis!(self, t, "__NIL"),
                IR::Int(t, i) => iis!(self, t, "{}", i),
                IR::Bool(t, b) => iis!(self, t, "{}", b),
                IR::Add(t, a, b) => ii!(self, t, "__ADD({}, {})", a, b),
                IR::Sub(t, a, b) => ii!(self, t, "({} - {})", a, b),
                IR::Mul(t, a, b) => ii!(self, t, "({} * {})", a, b),
                IR::Div(t, a, b) => ii!(self, t, "({} / {})", a, b),

                IR::Neg(t, a) => ii!(self, t, "(-{})", a),

                IR::Str(t, s) => iis!(self, t, "\"{}\"", s),
                IR::Float(t, f) => iis!(self, t, "{:?}", f),

                IR::Equals(t, a, b) => ii!(self, t, "({} == {})", a, b),
                IR::LessEqual(t, a, b) => ii!(self, t, "({} <= {})", a, b),
                IR::Less(t, a, b) => ii!(self, t, "({} < {})", a, b),
                IR::GreaterEqual(t, a, b) => ii!(self, t, "({} >= {})", a, b),
                IR::Greater(t, a, b) => ii!(self, t, "({} > {})", a, b),
                IR::NotEquals(t, a, b) => ii!(self, t, "({} ~= {})", a, b),

                IR::In(t, a, b) => ii!(self, t, "__CONTAINS({}, {})", a, b),

                IR::Not(t, a) => ii!(self, t, "(not {})", a),

                IR::List(t, exprs) => iis!(self, t, "__LIST{{ {} }}", self.comma_sep(exprs)),

                IR::Set(t, exprs) => iis!(
                    self,
                    t,
                    "__SET{{ {} }}",
                    exprs
                        .iter()
                        .map(|v| format!("[{}] = true", v))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),

                IR::Dict(t, exprs) => iis!(
                    self,
                    t,
                    "__DICT{{ {} }}",
                    exprs
                        .windows(2)
                        .step_by(2)
                        .map(|v| match v {
                            [k, v] => {
                                let k = self.expand(k).to_string();
                                let v = self.expand(v);
                                format!("[{}] = {}", k, v)
                            }
                            _ => unreachable!(),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                ),

                IR::Blob(t, fields) => iis!(
                    self,
                    t,
                    "__BLOB{{ {} }}",
                    fields
                        .iter()
                        .map(|(f, v)| format!("{} = {}", f, self.expand(v)))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),

                IR::Tuple(t, exprs) => iis!(self, t, "__TUPLE{{ {} }}", self.comma_sep(exprs)),

                IR::Assign(t, a) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let a = self.expand(a);
                        write!(self.out, "local {} = {}", t, a);
                    }
                    None
                }

                IR::Variant(t, v, a) => {
                    iis!(self, t, "__VARIANT{{ \"{}\", {} }}", v, self.expand(a))
                }

                IR::Index(t, a, i) => ii!(self, t, "__INDEX({}, {})", a, i),

                IR::Function(f, params) => {
                    write!(self.out, "local ");
                    write!(self.out, "function ");
                    write!(self.out, "{}", f);
                    write!(self.out, "(");
                    write!(
                        self.out,
                        "{}",
                        params
                            .iter()
                            .map(|v| format!("{}", v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    write!(self.out, ")");
                    None
                }

                IR::External(t, e) => {
                    write!(self.out, "{}", t);
                    write!(self.out, " = ");
                    write!(self.out, e);
                    None
                }

                IR::Call(t, f, args) => {
                    write!(self.out, "local ");
                    write!(self.out, "{}", t);
                    write!(self.out, " = ");
                    write!(self.out, "{}", f);
                    let args = self.comma_sep(args).to_string();
                    write!(self.out, "({})", args);
                    None
                }

                IR::Assert(v) => {
                    write!(self.out, "assert({}, \"Assert failed!\")", v);
                    None
                }

                IR::Define(t) => {
                    write!(self.out, "local ");
                    write!(self.out, "{}", t);
                    write!(self.out, " = ");
                    write!(self.out, "nil");
                    None
                }

                IR::If(a) => {
                    write!(self.out, "if ");
                    write!(self.out, "{}", a);
                    write!(self.out, " then");
                    depth += 1;
                    None
                }
                IR::Else => {
                    write!(self.out, "else");
                    depth += 1;
                    None
                }
                IR::End => {
                    write!(self.out, "end");
                    None
                }
                IR::Loop => {
                    write!(self.out, "while true do");
                    depth += 1;
                    None
                }
                IR::Break => {
                    write!(self.out, "break");
                    None
                }
                IR::Return(t) => {
                    write!(self.out, "return ");
                    write!(self.out, "{}", t);
                    None
                }
                IR::HaltAndCatchFire(msg) => {
                    write!(self.out, "__CRASH(\"{}\")()", msg);
                    None
                }
                IR::AssignIndex(t, i, a) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        write!(self.out, "__ASSIGN_INDEX({}, {}, {})", t, i, a);
                    }
                    None
                }
                IR::Access(t, a, f) => iis!(self, t, "{}.{}", self.expand(a), f),
                IR::AssignAccess(t, f, c) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let t = self.expand(t).to_string();
                        write!(self.out, "{}.{}", t, f);
                        write!(self.out, " = ");
                        write!(self.out, "{}", c);
                    }
                    None
                }
                IR::Label(l) => {
                    write!(self.out, "::{}::", l);
                    None
                }
                IR::Goto(l) => {
                    write!(self.out, "goto {}", l);
                    None
                }
            };
            match expr {
                Some((var, value)) => {
                    match self.usage_count.get(var).unwrap_or(&0) {
                        0 => {},
                        1 => self.define(*var, value),
                        _ => {
                            write!(self.out, "local {} = {}", var, value);
                        }
                    }
                }
                None => {}
            }
            write!(self.out, "\n");
        }
    }
}

pub fn generate(ir: &Vec<IR>, usage_count: &HashMap<Var, usize>, out: &mut dyn Write) {
    Generator::new(usage_count, out).generate(ir);
}
