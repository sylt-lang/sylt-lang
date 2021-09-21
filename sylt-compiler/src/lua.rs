use sylt_parser::expression::ComparisonKind;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind,
    Span, Statement, StatementKind,
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

#[derive(Debug, Copy, Clone)]
struct LuaContext {
    namespace: NamespaceID,
}

impl From<LuaContext> for Context {
    fn from(ctx: LuaContext) -> Self {
        Context {
            namespace: ctx.namespace,
            scope: 0,
            frame: 0,
        }
    }
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

    fn assignable(&mut self, ass: &Assignable, ctx: LuaContext) -> Option<usize> {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
            }
            Call(f, expr) => {
            }
            ArrowCall(pre, f, expr) => {
            }
            Access(a, field) => {
            }
            Index(a, b) => {
            }
            Expression(expr) => {
            }
        }
        None
    }

    fn bin_op(&mut self, a: &Expression, b: &Expression, op: &str, ctx: LuaContext) {
        self.expression(&a, ctx);
        write!(self, op);
        self.expression(&b, ctx);
    }

    fn expression(&mut self, expression: &Expression, ctx: LuaContext) {
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

            // AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span, ctx),

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

            // Duplicate(a) => self.un_op(a, &[Op::Copy(1)], expression.span, ctx),

            Parenthesis(expr) => self.expression(expr, ctx),

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
                println!("???");
                self.statement(body, ctx);
            }

            // Blob { blob, fields } => {
            // }

            // Tuple(x) | List(x) | Set(x) | Dict(x) => {
            // }

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
        ctx: LuaContext,
        namespace: usize,
    ) -> Option<usize> {
        None
    }

    fn set_identifier(&mut self, name: &str, span: Span, ctx: LuaContext, namespace: usize) {
    }

    fn statement(&mut self, statement: &Statement, ctx: LuaContext) {
        use StatementKind::*;
        self.compiler.panic = false;

        match &statement.kind {
            Use { .. } | EmptyStatement => {}

            Blob { name, fields } => {
            }

            IsCheck { lhs, rhs } => {
            }

            #[rustfmt::skip]
            Definition { ident, kind, value, .. } => {
                self.expression(value, ctx);
            }

            #[rustfmt::skip]
            Assignment { target, value, kind } => {
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
            }

            #[rustfmt::skip]
            If { condition, pass, fail } => {
            }

            Continue {} => {
            }

            Break {} => {
            }

            Unreachable {} => {
            }

            Ret { value } => {
            }
        }
        write!(self, ";");
    }

    pub fn compile(
        &mut self,
        statement: &Statement,
        namespace: usize,
    ) {
        let ctx = LuaContext {
            namespace,
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
