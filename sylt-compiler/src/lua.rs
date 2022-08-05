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
        {
            let var = $var;
            let value = format!($fmt, $( $dep ),*);
            match $self.usage_count.get(var).unwrap_or(&0) {
                0 => {},
                1 => $self.define(*var, value),
                _ => {
                    write!($self.out, "local {} = {}", var.format($self.var_to_name), value);
                }
            }
        }
    };
    ( $self:expr, $var:expr, $fmt:literal) => {
        {
            let var = $var;
            let value = $fmt.to_string();
            match $self.usage_count.get(var).unwrap_or(&0) {
                0 => {},
                1 => $self.define(*var, value),
                _ => {
                    write!($self.out, "local {} = {}", var.format($self.var_to_name), value);
                }
            }
        }
    };
}

struct Generator<'a, 'b, 'c> {
    usage_count: &'a HashMap<Var, usize>,
    lut: HashMap<Var, String>,
    out: &'b mut dyn Write,
    //
    var_to_name: &'c HashMap<Var, String>,
}

impl<'a, 'b, 'c> Generator<'a, 'b, 'c> {
    pub fn new(usage_count: &'a HashMap<Var, usize>, var_to_name: &'c HashMap<Var, String>, out: &'b mut dyn Write) -> Self {
        Self { usage_count, out, lut: HashMap::new(), var_to_name }
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
            None => var.format(self.var_to_name),
        }
    }

    fn define(&mut self, var: Var, value: String) {
        self.lut.insert(var, value);
    }

    #[sylt_macro::timed("lua::generate")]
    pub fn generate(&mut self, ir: &Vec<IR>, require: Option<&String>) {
        write!(self.out, include_str!("preamble.lua"));
        if let Some(file) = require {
            write!(
                self.out,
                "require \"{}\"",
                file.strip_suffix(".lua").unwrap_or(file)
            );
        }

        let mut depth = 0;
        for instruction in ir.iter() {
            //TODO(gu): which instruction?
            let _handle = sylt_macro::timed_handle!("lua::generate instruction");
            depth += match instruction {
                IR::Else | IR::End => -1,
                _ => 0,
            };

            for _ in 0..depth {
                write!(self.out, "  ");
            }
            match instruction {
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

                IR::Not(t, a) => ii!(self, t, "(not {})", a),

                IR::List(t, exprs) => iis!(self, t, "__LIST{{ {} }}", self.comma_sep(exprs)),

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

                IR::Variant(t, v, a) => {
                    iis!(self, t, "__VARIANT{{ \"{}\", {} }}", v, self.expand(a))
                }

                IR::Index(t, a, i) => ii!(self, t, "__INDEX({}, {})", a, i),

                IR::Function(f, params) => {
                    write!(self.out, "local ");
                    write!(self.out, "function ");
                    let f = self.expand(f);
                    write!(self.out, "{}", f);
                    write!(self.out, "(");
                    write!(
                        self.out,
                        "{}",
                        params
                            .iter()
                            .map(|v| v.format(self.var_to_name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    write!(self.out, ")");
                    depth += 1;
                }

                IR::External(t, e) => {
                    let t = self.expand(t);
                    write!(self.out, "{}", t);
                    write!(self.out, " = ");
                    write!(self.out, e);
                }

                IR::Call(t, f, args) => {
                    write!(self.out, "local ");
                    let t = self.expand(t);
                    write!(self.out, "{}", t);
                    write!(self.out, " = ");
                    let f = self.expand(f);
                    write!(self.out, "{}", f);
                    let args = self.comma_sep(args).to_string();
                    write!(self.out, "({})", args);
                }

                IR::Assert(v) => {
                    let v = self.expand(v).to_string();
                    write!(self.out, "assert({}, \"Assert failed!\")", v);
                }

                IR::Define(t) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        write!(self.out, "local ");
                        let t = self.expand(t);
                        write!(self.out, "{}", t);
                        write!(self.out, " = ");
                        write!(self.out, "nil");
                    }
                }

                IR::If(a) => {
                    write!(self.out, "if ");
                    let a = self.expand(a).to_string();
                    write!(self.out, "{}", a);
                    write!(self.out, " then");
                    depth += 1;
                }
                IR::Else => {
                    write!(self.out, "else");
                    depth += 1;
                }
                IR::End => {
                    write!(self.out, "end");
                }
                IR::Loop => {
                    write!(self.out, "while true do");
                    depth += 1;
                }
                IR::Break => {
                    write!(self.out, "break");
                }
                IR::Return(t) => {
                    write!(self.out, "return ");
                    let t = self.expand(t).to_string();
                    write!(self.out, "{}", t);
                }
                IR::HaltAndCatchFire(msg) => {
                    write!(self.out, "__CRASH(\"{}\")()", msg);
                }

                IR::Access(t, a, f) => iis!(self, t, "{}.{}", self.expand(a), f),

                IR::Copy(t, a) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let t = self.expand(t);
                        let a = self.expand(a);
                        write!(self.out, "local {} = {}", t, a);
                    }
                }

                // These cannot be optimized
                IR::Assign(t, a) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let a = self.expand(a);
                        let t = self.expand(t);
                        write!(self.out, "{} = {}", t, a);
                    }
                }
                IR::AssignIndex(t, i, a) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let a = self.expand(a);
                        let i = self.expand(i);
                        let t = self.expand(t);
                        write!(self.out, "__ASSIGN_INDEX({}, {}, {})", t, i, a);
                    }
                }
                IR::AssignAccess(t, f, c) => {
                    if self.usage_count.get(t).unwrap_or(&0) > &0 {
                        let t = self.expand(t);
                        let c = self.expand(c);
                        write!(self.out, "{}.{} = {}", t, f, c);
                    }
                }

                IR::Label(l) => {
                    write!(self.out, "::{}::", l);
                }
                IR::Goto(l) => {
                    write!(self.out, "goto {}", l);
                }
            }
            write!(self.out, "\n");
        }
    }
}

#[sylt_macro::timed("lua::generate")]
pub fn generate(
    ir: &Vec<IR>,
    var_to_name: &HashMap<Var, String>,
    usage_count: &HashMap<Var, usize>,
    out: &mut dyn Write,
    require: Option<&String>,
) {
    Generator::new(usage_count, var_to_name, out).generate(ir, require);
}
