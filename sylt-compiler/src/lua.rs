// TODO(ed)
//  x Blob instantiating
//  x Port the tests
//  x Port more foreign functions
//      x Figure out a way to include these foreign functions
//  x Typecheck before compiling - so we have all the information we need
//  - Ripout the type-stuff
//  - Annotate declarations with the resolved types
//  - The indexing problem
//  - Typechecker finds the wrong blob - use_import.sy testfile

use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use sylt_parser::expression::ComparisonKind;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Op, Span, Statement, StatementKind,
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
    loops: Vec<usize>,
    pub file: File,
}

impl<'t> LuaCompiler<'t> {
    pub(crate) fn new(compiler: &'t mut Compiler, file: &Path) -> Self {
        let file = File::create(&file).unwrap();
        Self {
            compiler,
            loops: Vec::new(),
            file,
        }
    }

    fn write(&mut self, msg: String) {
        self.file.write_all(msg.as_ref()).unwrap();
        if msg == ";" {
            self.file.write_all(b"\n").unwrap();
        } else {
            self.file.write_all(b" ").unwrap();
        }
    }

    fn write_global(&mut self, slot: usize) {
        write!(self, "GLOBAL_{}", slot);
    }

    fn write_slot(&mut self, slot: VarSlot) {
        write!(self, "local_{}", slot);
    }

    fn assignable(&mut self, ass: &Assignable, ctx: Context) -> Option<usize> {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                self.read_identifier(&ident.name, ass.span, ctx, ctx.namespace);
            }
            Call(f, expr) => {
                self.assignable(f, ctx);
                write!(self, "(");
                for (i, e) in expr.iter().enumerate() {
                    if i != 0 {
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
                // TODO(ed): This won't work for tuples and dicts at
                // the same time. We need to handle them differently and only
                // the typechecker knows what is what.
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
            Parenthesis(expr) => {
                write!(self, "(");
                self.expression(expr, ctx);
                write!(self, ")");
            }

            Get(a) => {
                self.assignable(a, ctx);
            }

            TypeConstant(_) => {
                error!(
                    self.compiler,
                    ctx, expression.span, "Type constants are not supported in the lua-compiler"
                );
            }

            Add(a, b) => self.bin_op(a, b, "+", ctx),
            Sub(a, b) => self.bin_op(a, b, "-", ctx),
            Mul(a, b) => self.bin_op(a, b, "*", ctx),
            Div(a, b) => self.bin_op(a, b, "/", ctx),

            Comparison(a, cmp, b) => match cmp {
                Equals => self.bin_op(a, b, "==", ctx),
                NotEquals => self.bin_op(a, b, "~=", ctx),
                Greater => self.bin_op(a, b, ">", ctx),
                GreaterEqual => self.bin_op(a, b, ">=", ctx),
                Less => self.bin_op(a, b, "<", ctx),
                LessEqual => self.bin_op(a, b, "<=", ctx),
                In => {
                    write!(self, "__contains(");
                    self.expression(a, ctx);
                    write!(self, ",");
                    self.expression(b, ctx);
                    write!(self, ")");
                }
            },

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

            IfExpression {
                condition,
                pass,
                fail,
            } => {
                write!(self, "(function ()");
                write!(self, "if");
                self.expression(condition, ctx);
                write!(self, "then");
                write!(self, "return");
                self.expression(pass, ctx);
                write!(self, "else");
                write!(self, "return");
                self.expression(fail, ctx);
                write!(self, "end");
                write!(self, "end)()");
            }

            Function {
                name: _,
                params,
                ret: _,
                body,
            } => {
                // TODO(ed): We don't use multiple frames here...
                let s = self.compiler.frames.last().unwrap().variables.len();
                write!(self, "function (");
                for (i, e) in params.iter().enumerate() {
                    if i != 0 {
                        write!(self, ",");
                    }
                    let slot = self
                        .compiler
                        .define(&e.0.name, VarKind::Const, expression.span);
                    self.compiler.activate(slot);
                    self.write_slot(slot);
                }
                write!(self, ")");
                self.statement(body, ctx);
                write!(self, "end");
                write!(self, ";");
                self.compiler
                    .frames
                    .last_mut()
                    .unwrap()
                    .variables
                    .truncate(s);
            }

            Tuple(xs) => {
                write!(self, "__TUPLE { ");
                for x in xs {
                    self.expression(x, ctx);
                    write!(self, " , ");
                }
                write!(self, "}");
            }

            List(xs) => {
                write!(self, "__LIST { ");
                for x in xs {
                    self.expression(x, ctx);
                    write!(self, " , ");
                }
                write!(self, "}");
            }

            Set(xs) => {
                write!(self, "__SET { ");
                for x in xs {
                    write!(self, "[");
                    self.expression(x, ctx);
                    write!(self, "]");
                    write!(self, " = true , ");
                }
                write!(self, "}");
            }

            Dict(xs) => {
                write!(self, "__DICT { ");
                for (k, v) in xs.iter().zip(xs.iter().skip(1)) {
                    write!(self, "[");
                    self.expression(k, ctx);
                    write!(self, "]");
                    write!(self, "=");
                    self.expression(v, ctx);
                    write!(self, ",");
                }
                write!(self, "}");
            }

            Blob { blob: _, fields } => {
                // TODO(ed): Know which blob something is?
                write!(self, "__BLOB { ");
                for (k, v) in fields.iter() {
                    write!(self, "{} =", k);
                    self.expression(v, ctx);
                    write!(self, ",");
                }
                write!(self, "}");
            }

            Float(a) => write!(self, "{}", a),
            Bool(a) => write!(self, "{}", a),
            Int(a) => write!(self, "{}", a),
            Str(a) => write!(self, "\"{}\"", a),
            Nil => write!(self, "nil"),
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
                Some(Name::External(_)) => {
                    write!(self, "{}", name);
                }
                Some(Name::Namespace(new_namespace)) => return Some(new_namespace),
                None => {
                    if let Some((_, _, _)) = self.compiler.functions.get(name) {
                        // Same as external - but defined from sylt-std
                        write!(self, "{}", name);
                    } else {
                        error!(
                            self.compiler,
                            ctx, span, "No identifier found named: '{}'", name
                        );
                    }
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
                        error!(
                            self.compiler,
                            ctx, span, "Cannot mutate constant '{}'", name
                        );
                    } else {
                        self.write_global(slot);
                    }
                }
                _ => {
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

    fn outer_statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;
        self.compiler.panic = false;

        match &statement.kind {
            Use { .. } | Blob { .. } | EmptyStatement => {}

            IsCheck { lhs, rhs } => {
                let lhs = self.compiler.resolve_type(lhs, ctx.into());
                let rhs = self.compiler.resolve_type(rhs, ctx.into());
                if let Err(msg) = rhs.fits(&lhs) {
                    error!(
                        self.compiler,
                        ctx, statement.span, "Is-check failed - {}", msg
                    );
                }
            }

            ExternalDefinition { .. } => {}

            #[rustfmt::skip]
            Definition { ident, value, .. } => {
                self.set_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                write!(self, "=");
                self.compiler.frames.push(Frame::new("/expr/", statement.span));
                // Only reachable form the outside so we know these frames
                let ctx = Context { frame: self.compiler.frames.len() - 1, ..ctx };
                self.expression(value, ctx);
                self.compiler.frames.pop();
            }

            #[rustfmt::skip]
            x => {
                unreachable!("Not a valid outer statement {:?}", x)
            }
        }
        write!(self, ";");
    }

    fn statement(&mut self, statement: &Statement, ctx: Context) {
        use StatementKind::*;
        self.compiler.panic = false;

        match &statement.kind {
            Use { .. } | Blob { .. } | EmptyStatement => {}

            IsCheck { .. } => {
                error!(
                    self.compiler,
                    ctx, statement.span, "is-checks only valid in outer-scope"
                );
            }

            #[rustfmt::skip]
            Definition { ident, kind, value, .. } => {
                let slot = self.compiler.define(&ident.name, *kind, statement.span);
                write!(self, "local");
                self.write_slot(slot);
                write!(self, "=");
                self.expression(value, ctx);
                self.compiler.activate(slot);
            }

            ExternalDefinition { .. } => {
                error!(
                    self.compiler,
                    ctx, statement.span, "External definitions must lie in the outmost scope"
                );
            }

            #[rustfmt::skip]
            Assignment { target, value, kind } => {
                if *kind == Op::Nop {
                    self.assignable(target, ctx);
                    write!(self, "=");
                    self.expression(value, ctx);
                } else {
                    let op = match kind {
                        Op::Nop => unreachable!(),
                        Op::Add => "+",
                        Op::Sub => "-",
                        Op::Mul => "*",
                        Op::Div => "/",
                    };

                    match &target.kind {
                        // TODO(ed): Warn about calls?
                        AssignableKind::Access(rest, field) => {
                            write!(self, "do local tmp_ass =");
                            self.assignable(rest, ctx);
                            write!(self, ";");
                            write!(self, "tmp_ass . {} = tmp_ass . {} {}", field.name, field.name, op);
                            write!(self, "(");
                            self.expression(value, ctx);
                            write!(self, ")");
                            write!(self, ";");
                            write!(self, "end");
                        }
                        AssignableKind::Index(rest, index) => {
                            write!(self, "do local tmp_ass =");
                            self.assignable(rest, ctx);
                            write!(self, ";");
                            write!(self, "local tmp_expr =");
                            self.expression(index, ctx);
                            write!(self, ";");
                            write!(self, "tmp_ass [ tmp_expr ] = tmp_ass [ tmp_expr ] {}", op);
                            write!(self, "(");
                            self.expression(value, ctx);
                            write!(self, ")");
                            write!(self, ";");
                            write!(self, "end");
                        }
                        _ => {
                            self.assignable(target, ctx);
                            write!(self, "=");
                            self.assignable(target, ctx);
                            write!(self, op);
                            self.expression(value, ctx);
                        }
                    }
                }
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
            }

            Block { statements } => {
                // TODO(ed): Some of these blocks are wrong - but it should still work.
                let s = self.compiler.frames.last().unwrap().variables.len();
                write!(self, "do");
                for stmt in statements.iter() {
                    self.statement(stmt, ctx);
                }
                write!(self, "end");
                self.compiler
                    .frames
                    .last_mut()
                    .unwrap()
                    .variables
                    .truncate(s);
            }

            Loop { condition, body } => {
                write!(self, "while");
                self.expression(condition, ctx);
                write!(self, "do");
                self.loops.push(0);
                write!(self, ";");
                self.statement(body, ctx);
                let l = self.loops.len();
                if self.loops.pop().unwrap() > 0 {
                    write!(self, "::CONTINUE_{}::", l);
                    write!(self, ";");
                }
                write!(self, "end");
                write!(self, ";");
            }

            If { condition, pass, fail } => {
                write!(self, "if");
                self.expression(condition, ctx);
                write!(self, "then");
                write!(self, ";");
                self.statement(pass, ctx);
                write!(self, "else");
                write!(self, ";");
                self.statement(fail, ctx);
                write!(self, "end");
                write!(self, ";");
            }

            Continue => {
                write!(self, "goto");
                let cont = self.loops.len();
                *self.loops.last_mut().unwrap() += 1;
                write!(self, "CONTINUE_{}", cont);
                write!(self, ";");
            }

            Break => {
                write!(self, "break");
                write!(self, ";");
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

    pub fn compile(&mut self, statement: &Statement, namespace: usize) {
        let ctx = Context {
            namespace,
            frame: 0,
        };
        self.outer_statement(&statement, ctx);
    }

    pub fn preamble(&mut self, _span: Span, _num_constants: usize) {
        write!(self, include_str!("preamble.lua"));
    }

    pub fn postamble(&mut self, span: Span) {
        let ctx = Context {
            frame: self.compiler.frames.len() - 1,
            namespace: 0,
        };
        self.read_identifier("start", span, ctx, 0);
        write!(self, "()");
        write!(self, ";");
    }
}
