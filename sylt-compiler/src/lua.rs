use sylt_parser::expression::ComparisonKind;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind,
    Span, Statement, StatementKind, Op,
};

use crate::*;

macro_rules! write {
    ($compiler:expr, $msg:expr ) => {
        $compiler.write(String::from($msg))
    };
    ($compiler:expr, $( $msg:expr ),+ ) => {
        $compiler.write(format!($( $msg ),*))
    };
}

pub struct LuaCompiler<'t> {
    compiler: &'t mut Compiler,
    pub blocks: String,
}

impl<'t> LuaCompiler<'t> {
    pub(crate) fn new(compiler: &'t mut Compiler) -> Self {
        Self {
            compiler,
            blocks: String::new(),
        }
    }

    fn write(&mut self, msg: String) {
        self.blocks = format!("{} {}", self.blocks, msg);
    }

    fn write_global(&mut self, slot: usize) {
        write!(self, "global_var_{}", slot);
    }

    fn write_slot(&mut self, slot: VarSlot) {
        write!(self, "local_var_{}", slot);
    }

    fn assignable(&mut self, ass: &Assignable, ctx: Context) -> Option<usize> {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                self.read_identifier(&ident.name, ass.span, ctx, ctx.namespace);
            },
            Call(f, expr) => {
                self.assignable(f, ctx);
                write!(self, "(");
                for (i, e) in expr.iter().enumerate() {
                    if i == 0 {
                        write!(self, ",");
                    }
                    self.expression(e, ctx);
                }
                write!(self, ")");
            }
            ArrowCall(pre, f, expr) => {
                self.assignable(f, ctx);
                write!(self, "(");
                self.expression(pre, ctx);
                for e in expr.iter() {
                    write!(self, ",");
                    self.expression(e, ctx);
                }
                write!(self, ")");
            }
            Access(a, field) => {
                self.assignable(a, ctx);
                write!(self, ". {}", field.name);
            }
            Index(a, b) => {
                self.assignable(a, ctx);
                write!(self, "[");
                self.expression(b, ctx);
                write!(self, "]");
            }
            Expression(expr) => {
                self.expression(expr, ctx);
            }
        }
        None
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, op: &str, ctx: Context) {
        self.expression(&a, ctx);
        write!(self, op);
        self.expression(&b, ctx);
    }

    fn expression(&mut self, expression: &Expression, ctx: Context) {
        use ComparisonKind::*;
        use ExpressionKind::*;

        match &expression.kind {
            // Get(a) => {
            // }

            // TypeConstant(ty) => {
            // }

            Add(a, b) => self.bin_op(a, b, "+", ctx),
            Sub(a, b) => self.bin_op(a, b, "-", ctx),
            Mul(a, b) => self.bin_op(a, b, "*", ctx),
            Div(a, b) => self.bin_op(a, b, "/", ctx),

            Comparison(a, cmp, b) => match cmp {
                Equals => self.bin_op(a, b, "==", ctx),
                NotEquals => self.bin_op(a, b, "~=", ctx),
                Greater => self.bin_op(a, b, "<", ctx),
                GreaterEqual => self.bin_op(a, b, "<=", ctx),
                Less => self.bin_op(a, b, ">", ctx),
                LessEqual => self.bin_op(a, b, ">=", ctx),
                _ => todo!(),
                // Is => self.bin_op(a, b, &[Op::Is], expression.span, ctx),
                // In => self.bin_op(a, b, &[Op::Contains], expression.span, ctx),
            }

            AssertEq(a, b) => {
                write!(self, "assert(");
                self.expression(a, ctx);
                write!(self, "==");
                self.expression(b, ctx);
                write!(self, ", \"Assert failed\")");
            }

            Neg(a) => {
                write!(self, "-");
                self.expression(a, ctx);
            }

            And(a, b) => self.bin_op(a, b, "and", ctx),
            Or(a, b) => self.bin_op(a, b, "or", ctx),
            Not(a) => {
                write!(self, "not");
                self.expression(a, ctx);
            }

            Duplicate(expr)
            | Parenthesis(expr) => {
                write!(self, "(");
                self.expression(expr, ctx);
                write!(self, ")");
            }

            // IfExpression {
            //     condition,
            //     pass,
            //     fail,
            // } => {
            // }

            // IfShort {
            //     condition,
            //     fail,
            //     ..
            // } => {
            // }

            Function {
                name,
                params,
                ret,
                body,
            } => {
                self.statement(body, ctx);
            }

            // Blob { blob, fields } => {
            // }

            Tuple(xs) => {
                write!(self, "setmetatable( { ");
                for x in xs {
                    self.expression(x, ctx);
                    write!(self, " , ");
                }
                write!(self, "} , __TUPLE_TABLE or {})");
            }

            List(xs) => {
                write!(self, "setmetatable( { ");
                for x in xs {
                    self.expression(x, ctx);
                    write!(self, " , ");
                }
                write!(self, "} , __LIST_TABLE or {})");
            }

            Set(xs) => {
                write!(self, "setmetatable( { ");
                for x in xs {
                    self.expression(x, ctx);
                    write!(self, " , ");
                }
                write!(self, "} , __SET_TABLE or {})");
            }

            Dict(xs) => {
                write!(self, "setmetatable( { ");
                for (k, v) in xs.iter().zip(xs.iter().skip(1)) {
                    self.expression(k, ctx);
                    write!(self, "=");
                    self.expression(v, ctx);
                }
                write!(self, "} , __SET_TABLE or {})");
            }

            Float(a) => write!(self, "{}", a),
            Bool(a) => {
                if *a {
                    write!(self, "true")
                } else {
                    write!(self, "false")
                }
            }
            Int(a) => write!(self, "{}", a),
            Str(a) => write!(self, "{}", a),
            Nil => write!(self, "nil"),

            _ => todo!(),
        }
    }

    fn read_identifier(
        &mut self,
        name: &str,
        span: Span,
        ctx: Context,
        namespace: usize,
    ) -> Option<usize> {
        match self.compiler.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                self.write_slot(up.slot);
            }

            Ok(Lookup::Variable(var)) => {
                self.write_slot(var.slot);
            }

            Err(()) => match self.compiler.namespaces[namespace].get(name).cloned() {
                Some(Name::Global(slot)) => {
                    self.write_global(slot);
                }
                Some(Name::Blob(blob)) => {
                    self.write_global(blob);
                }
                Some(Name::Namespace(new_namespace)) => {
                    return Some(new_namespace)
                }
                None => {
                    // SAD!
                }
            },
        }
        None
    }

    fn set_identifier(&mut self, name: &str, span: Span, ctx: Context, namespace: usize) {
        match self.compiler.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                self.write_slot(up.slot);
            }

            Ok(Lookup::Variable(var)) => {
                self.write_slot(var.slot);
            }

            Err(()) => match self.compiler.namespaces[namespace].get(name).cloned() {
                Some(Name::Global(slot)) => {
                    let var = &self.compiler.frames[0].variables[slot];
                    if var.kind.immutable() && ctx.frame != 0 {
                        error!(self.compiler, ctx, span, "Cannot mutate constant '{}'", name);
                    } else {
                        self.write_global(slot);
                    }
                }
                _ => {
                    // SAD!
                    error!(
                        self.compiler,
                        ctx,
                        span,
                        "Cannot assign '{}' in '{}'",
                        name,
                        self.compiler.file_from_namespace(namespace).display()
                    );
                }
            },
        }
    }

    fn statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;
        self.compiler.panic = false;

        match &statement.kind {
            Use { .. } | EmptyStatement => {}

            Blob { name, fields } => {
                todo!();
            }

            IsCheck { lhs, rhs } => {
                todo!();
            }

            #[rustfmt::skip]
            Definition { ident, kind, value, .. } => {
                let slot = self.compiler.define(&ident.name, *kind, statement.span);
                write!(self, "local");
                self.write_slot(slot);
                self.expression(value, ctx);
                self.compiler.activate(slot);
            }

            #[rustfmt::skip]
            Assignment { target, value, kind } => {
                self.assignable(target, ctx);
                write!(self, "=");
                assert!(matches!(kind, Op::Add), "Only support nop right now");
                self.expression(value, ctx);
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
            }

            Block { statements } => {
                for stmt in statements.iter() {
                    self.statement(stmt, ctx);
                }
            }

            Loop { condition, body } => {
                todo!();
            }

            #[rustfmt::skip]
            If { condition, pass, fail } => {
                todo!();
            }

            Continue {} => {
                todo!();
            }

            Break {} => {
                todo!();
            }

            Unreachable {} => {
                write!(self, "assert(false, \"unreachable\")");
            }

            Ret { value } => {
                write!(self, "return");
                self.expression(value, ctx);
            }
        }
        write!(self, ";");
    }

    pub fn compile(
        &mut self,
        statement: &Statement,
        namespace: usize,
    ) {
        let ctx = Context {
            namespace,
            frame: 0,
        };
        self.statement(&statement, ctx);
    }

    pub fn preamble(
        &mut self,
        span: Span,
        num_constants: usize,
    ) {
    }

    pub fn postamble(
        &mut self,
        span: Span,
    ) {
    }
}

// TODO(ed): This should move to the typechecker - since we always want this check.
fn all_paths_return(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Use { .. }
        | StatementKind::Blob { .. }
        | StatementKind::IsCheck { .. }
        | StatementKind::Assignment { .. }
        | StatementKind::Definition { .. }
        | StatementKind::StatementExpression { .. }
        | StatementKind::Unreachable
        | StatementKind::Continue
        | StatementKind::Break
        | StatementKind::EmptyStatement => false,

        StatementKind::If { pass, fail, .. } => all_paths_return(pass) && all_paths_return(fail),

        StatementKind::Loop { body, .. } => all_paths_return(body),
        StatementKind::Block { statements } => statements.iter().any(all_paths_return),

        StatementKind::Ret { .. } => true,
    }
}
