use std::rc::Rc;
use sylt_common::error::Error;
use sylt_common::{Block, Op, Value};
use sylt_parser::expression::ComparisonKind;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Op as ParserOp, Span, Statement,
    StatementKind, TypeAssignable, TypeAssignableKind, VarKind,
};

use crate::*;

#[derive(Debug, Copy, Clone)]
struct LoopFrame {
    continue_addr: usize,
    break_addr: usize,
    stack_size: usize,
}

#[derive(Debug, Copy, Clone)]
struct BytecodeContext {
    block_slot: BlockID,
    namespace: NamespaceID,
    scope: usize,
    frame: usize,
}

impl From<BytecodeContext> for Context {
    fn from(ctx: BytecodeContext) -> Self {
        Context { namespace: ctx.namespace, frame: ctx.frame }
    }
}

pub struct BytecodeCompiler<'t> {
    compiler: &'t mut Compiler,

    pub blocks: Vec<Block>,
    loops: Vec<LoopFrame>,
}

impl<'t> BytecodeCompiler<'t> {
    pub(crate) fn new(compiler: &'t mut Compiler) -> Self {
        Self { compiler, blocks: Vec::new(), loops: Vec::new() }
    }

    fn add_op(&mut self, ctx: BytecodeContext, span: Span, op: Op) -> usize {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .add(op, span.line_start)
    }

    fn patch(&mut self, ctx: BytecodeContext, ip: usize, op: Op) {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .ops[ip] = op;
    }

    fn next_ip(&mut self, ctx: BytecodeContext) -> usize {
        self.blocks
            .get_mut(ctx.block_slot)
            .expect("Invalid block id")
            .curr()
    }

    fn push_frame_and_block(
        &mut self,
        ctx: BytecodeContext,
        name: &str,
        span: Span,
    ) -> BytecodeContext {
        let file_as_path = PathBuf::from(self.compiler.file_from_namespace(ctx.namespace));

        let block = Block::new(&name, ctx.namespace, &file_as_path);
        self.blocks.push(block);

        self.compiler.frames.push(Frame::new(name, span));
        BytecodeContext {
            block_slot: self.blocks.len() - 1,
            frame: self.compiler.frames.len() - 1,
            ..ctx
        }
    }

    fn emit_pop_until_size(&mut self, ctx: BytecodeContext, span: Span, target_size: usize) {
        let vars: Vec<_> = self.compiler.frames[ctx.frame]
            .variables
            .iter()
            .skip(target_size)
            .rev()
            .cloned()
            .collect();
        for var in &vars {
            if var.captured {
                self.add_op(ctx, span, Op::PopUpvalue);
            } else {
                self.add_op(ctx, span, Op::Pop);
            }
        }
    }

    fn pop_until_size(&mut self, ctx: BytecodeContext, span: Span, target_size: usize) {
        self.emit_pop_until_size(ctx, span, target_size);
        self.compiler.frames[ctx.frame]
            .variables
            .truncate(target_size);
    }

    fn assignable(&mut self, ass: &Assignable, ctx: BytecodeContext) -> Option<usize> {
        use AssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                return self.read_identifier(&ident.name, ass.span, ctx, ctx.namespace);
            }
            Variant { variant, value, .. } => {
                let variant = self
                    .compiler
                    .constant(Value::String(Rc::new(variant.name.clone())));
                self.add_op(ctx, ass.span, variant);
                self.expression(value, ctx);
                self.add_op(ctx, ass.span, Op::Tag);
            }
            Call(f, expr) => {
                self.assignable(f, ctx);
                for expr in expr.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(ctx, ass.span, Op::Call(expr.len()));
            }
            ArrowCall(pre, f, expr) => {
                self.expression(pre, ctx);
                self.assignable(f, ctx);
                self.add_op(ctx, ass.span, Op::Swap);
                for expr in expr.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(ctx, ass.span, Op::Call(expr.len() + 1));
            }
            Access(a, field) => {
                if let Some(namespace) = self.assignable(a, ctx) {
                    return self.read_identifier(&field.name, field.span, ctx, namespace);
                } else {
                    let slot = self.compiler.string(&field.name);
                    self.add_op(ctx, field.span, Op::GetField(slot));
                }
            }
            Index(a, b) => {
                self.assignable(a, ctx);
                if let ExpressionKind::Int(n) = b.kind {
                    self.add_op(ctx, ass.span, Op::GetConstIndex(n));
                } else {
                    self.expression(b, ctx);
                    self.add_op(ctx, ass.span, Op::GetIndex);
                }
            }
            Expression(expr) => {
                self.expression(expr, ctx);
            }
        }
        None
    }

    fn type_assignable(&mut self, ass: &TypeAssignable, ctx: BytecodeContext) -> Option<usize> {
        use TypeAssignableKind::*;

        match &ass.kind {
            Read(ident) => {
                return self.read_identifier(&ident.name, ass.span, ctx, ctx.namespace);
            }
            Access(a, field) => {
                if let Some(namespace) = self.type_assignable(a, ctx) {
                    return self.read_identifier(&field.name, field.span, ctx, namespace);
                }
            }
        }
        None
    }

    fn un_op(&mut self, a: &Expression, ops: &[Op], span: Span, ctx: BytecodeContext) {
        self.expression(&a, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn bin_op(
        &mut self,
        a: &Expression,
        b: &Expression,
        ops: &[Op],
        span: Span,
        ctx: BytecodeContext,
    ) {
        self.expression(&a, ctx);
        self.expression(&b, ctx);
        for op in ops {
            self.add_op(ctx, span, *op);
        }
    }

    fn push(&mut self, value: Value, span: Span, ctx: BytecodeContext) {
        let value = self.compiler.constant(value);
        self.add_op(ctx, span, value);
    }

    fn expression(&mut self, expression: &Expression, ctx: BytecodeContext) {
        use ComparisonKind::*;
        use ExpressionKind::*;

        match &expression.kind {
            Get(a) => {
                self.assignable(a, ctx);
            }

            Add(a, b) => self.bin_op(a, b, &[Op::Add], expression.span, ctx),
            Sub(a, b) => self.bin_op(a, b, &[Op::Sub], expression.span, ctx),
            Mul(a, b) => self.bin_op(a, b, &[Op::Mul], expression.span, ctx),
            Div(a, b) => self.bin_op(a, b, &[Op::Div], expression.span, ctx),

            Comparison(a, cmp, b) => match cmp {
                Equals => self.bin_op(a, b, &[Op::Equal], expression.span, ctx),
                NotEquals => self.bin_op(a, b, &[Op::Equal, Op::Not], expression.span, ctx),
                Greater => self.bin_op(a, b, &[Op::Greater], expression.span, ctx),
                GreaterEqual => self.bin_op(a, b, &[Op::Less, Op::Not], expression.span, ctx),
                Less => self.bin_op(a, b, &[Op::Less], expression.span, ctx),
                LessEqual => self.bin_op(a, b, &[Op::Greater, Op::Not], expression.span, ctx),
                In => self.bin_op(a, b, &[Op::Contains], expression.span, ctx),
            },

            AssertEq(a, b) => self.bin_op(a, b, &[Op::Equal, Op::Assert], expression.span, ctx),

            Neg(a) => self.un_op(a, &[Op::Neg], expression.span, ctx),

            And(a, b) => {
                self.expression(a, ctx);

                self.add_op(ctx, expression.span, Op::Copy(1));
                let jump = self.add_op(ctx, expression.span, Op::Illegal);
                self.add_op(ctx, expression.span, Op::Pop);

                self.expression(b, ctx);

                let op = Op::JmpFalse(self.next_ip(ctx));
                self.patch(ctx, jump, op);
            }
            Or(a, b) => {
                self.expression(a, ctx);

                self.add_op(ctx, expression.span, Op::Copy(1));
                let skip = self.add_op(ctx, expression.span, Op::Illegal);
                let jump = self.add_op(ctx, expression.span, Op::Illegal);

                let op = Op::JmpFalse(self.next_ip(ctx));
                self.patch(ctx, skip, op);
                self.add_op(ctx, expression.span, Op::Pop);

                self.expression(b, ctx);
                let op = Op::Jmp(self.next_ip(ctx));
                self.patch(ctx, jump, op);
            }
            Not(a) => self.un_op(a, &[Op::Not], expression.span, ctx),

            Parenthesis(expr) => self.expression(expr, ctx),

            IfExpression { condition, pass, fail } => {
                self.expression(condition, ctx);

                let skip = self.add_op(ctx, expression.span, Op::Illegal);

                self.expression(pass, ctx);
                let out = self.add_op(ctx, expression.span, Op::Illegal);
                let op = Op::JmpFalse(self.next_ip(ctx));
                self.patch(ctx, skip, op);

                self.expression(fail, ctx);
                let op = Op::Jmp(self.next_ip(ctx));
                self.patch(ctx, out, op);
            }

            Function { name, params, ret: _, body } => {
                let file = self.compiler.file_from_namespace(ctx.namespace).display();
                let name = format!("fn {} {}:{}", name, file, expression.span.line_start);

                // === Frame begin ===
                let inner_ctx = self.push_frame_and_block(ctx, &name, expression.span);
                for (ident, _) in params.iter() {
                    let param = self
                        .compiler
                        .define(&ident.name, VarKind::Const, ident.span);
                    self.compiler.activate(param);
                }

                self.statement(&body, inner_ctx);

                if !all_paths_return(&body) {
                    let nil = self.compiler.constant(Value::Nil);
                    self.add_op(inner_ctx, body.span, nil);
                    self.add_op(inner_ctx, body.span, Op::Return);
                }

                self.blocks[inner_ctx.block_slot].upvalues = self
                    .compiler
                    .pop_frame(inner_ctx.into())
                    .upvalues
                    .into_iter()
                    .map(|u| (u.parent, u.upupvalue, u.ty))
                    .collect();
                let function = Value::Function(Rc::new(Vec::new()), inner_ctx.block_slot);
                // === Frame end ===

                let function = self.compiler.constant(function);
                self.add_op(ctx, expression.span, function);
            }

            Blob { blob, fields } => {
                let name = format!("blob");

                // Set up closure for the self variable. The typechecker takes
                // the closure and self variable into account when solving the
                // types.
                let inner_ctx = self.push_frame_and_block(ctx, &name, expression.span);

                // Set self to nil so that we can capture it.
                self.push(Value::Nil, expression.span, inner_ctx);
                let slot = self
                    .compiler
                    .define("self", VarKind::Mutable, expression.span);
                self.compiler.activate(slot);

                // Initialize the blob. This may capture self.
                self.type_assignable(blob, inner_ctx);
                for (name, field) in fields.iter() {
                    let name = self.compiler.constant(Value::String(Rc::new(name.clone())));
                    self.add_op(inner_ctx, field.span, name);
                    self.expression(field, inner_ctx);
                }

                // Set self to the blob and return it.
                self.add_op(inner_ctx, expression.span, Op::Call(fields.len() * 2));
                self.set_identifier("self", expression.span, inner_ctx, inner_ctx.namespace);
                self.read_identifier("self", expression.span, inner_ctx, inner_ctx.namespace);
                self.add_op(inner_ctx, expression.span, Op::Return);

                self.blocks[inner_ctx.block_slot].upvalues = self
                    .compiler
                    .pop_frame(inner_ctx.into())
                    .upvalues
                    .into_iter()
                    .map(|u| (u.parent, u.upupvalue, u.ty))
                    .collect();
                let function = Value::Function(Rc::new(Vec::new()), inner_ctx.block_slot);

                // Call the closure.
                let function = self.compiler.constant(function);
                self.add_op(ctx, expression.span, function);
                self.add_op(ctx, expression.span, Op::Call(0));
            }

            Tuple(x) | List(x) | Set(x) | Dict(x) => {
                for expr in x.iter() {
                    self.expression(expr, ctx);
                }
                self.add_op(
                    ctx,
                    expression.span,
                    match &expression.kind {
                        Tuple(_) => Op::Tuple(x.len()),
                        List(_) => Op::List(x.len()),
                        Set(_) => Op::Set(x.len()),
                        Dict(_) => Op::Dict(x.len()),
                        _ => unreachable!(),
                    },
                );
            }

            Float(a) => self.push(Value::Float(*a), expression.span, ctx),
            Bool(a) => self.push(Value::Bool(*a), expression.span, ctx),
            Int(a) => self.push(Value::Int(*a), expression.span, ctx),
            Str(a) => self.push(Value::String(Rc::new(a.clone())), expression.span, ctx),
            Nil => self.push(Value::Nil, expression.span, ctx),
        }
    }

    fn read_identifier(
        &mut self,
        name: &str,
        span: Span,
        ctx: BytecodeContext,
        namespace: usize,
    ) -> Option<usize> {
        match self.compiler.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                let op = Op::ReadUpvalue(up.slot);
                self.add_op(ctx, span, op);
            }

            Ok(Lookup::Variable(var)) => {
                let op = Op::ReadLocal(var.slot);
                self.add_op(ctx, span, op);
            }

            Err(()) => match self.compiler.namespaces[namespace].get(name) {
                Some(Name::Global(slot)) => {
                    let op = Op::ReadGlobal(*slot);
                    self.add_op(ctx, span, op);
                }
                Some(Name::External(_)) => {
                    error!(
                        self.compiler,
                        span, "External values aren't allowed when compiling to byte-code "
                    );
                }
                Some(Name::Blob(blob)) => {
                    let op = Op::Constant(*blob);
                    self.add_op(ctx, span, op);
                }
                Some(Name::Enum(enum_)) => {
                    let op = Op::Constant(*enum_);
                    self.add_op(ctx, span, op);
                }
                Some(Name::Namespace(new_namespace)) => return Some(*new_namespace),
                None => {
                    if let Some((slot, _, _)) = self.compiler.functions.get(name) {
                        let slot = *slot;
                        let op = self.compiler.constant(Value::ExternFunction(slot));
                        self.add_op(ctx, span, op);
                    } else {
                        error!(
                            self.compiler,
                            span,
                            "Cannot read '{}' in '{}'",
                            name,
                            self.compiler.file_from_namespace(namespace).display()
                        );
                    }
                }
            },
        }
        None
    }

    fn set_identifier(&mut self, name: &str, span: Span, ctx: BytecodeContext, namespace: usize) {
        match self.compiler.resolve_and_capture(name, ctx.frame, span) {
            Ok(Lookup::Upvalue(up)) => {
                let op = Op::AssignUpvalue(up.slot);
                self.add_op(ctx, span, op);
                return;
            }

            Ok(Lookup::Variable(var)) => {
                let op = Op::AssignLocal(var.slot);
                self.add_op(ctx, span, op);
                return;
            }

            Err(()) => match self.compiler.namespaces[namespace].get(name) {
                Some(Name::Global(slot)) => {
                    let var = &self.compiler.frames[0].variables[*slot];
                    if var.kind.immutable() && ctx.frame != 0 {
                        error!(self.compiler, span, "Cannot mutate constant '{}'", name);
                    } else {
                        let op = Op::AssignGlobal(var.slot);
                        self.add_op(ctx, span, op);
                    }
                }

                _ => {
                    error!(
                        self.compiler,
                        span,
                        "Cannot assign '{}' in '{}'",
                        name,
                        self.compiler.file_from_namespace(namespace).display()
                    );
                }
            },
        }
    }

    fn statement(&mut self, statement: &Statement, ctx: BytecodeContext) {
        use StatementKind::*;
        self.compiler.panic = false;

        match &statement.kind {
            Use { .. }
            | Enum { .. }
            | FromUse { .. }
            | Blob { .. }
            | IsCheck { .. }
            | EmptyStatement => {}

            #[rustfmt::skip]
            Definition { ident, kind, value, .. } => {
                // TODO(ed): Don't use type here - type check the tree first.
                self.expression(value, ctx);

                if ctx.frame == 0 {
                    // Global
                    self.set_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                } else {
                    // Local variable
                    let slot = self.compiler.define(&ident.name, *kind, statement.span);
                    self.compiler.activate(slot);
                }
            }

            ExternalDefinition { .. } => {
                // TODO(ed): Should they be? Is this how we should type the standard library?
                error!(
                    self.compiler,
                    statement.span, "External values aren't allowed when compiling to byte-code "
                );
            }

            #[rustfmt::skip]
            Assignment { target, value, kind } => {
                use AssignableKind::*;
                use ParserOp::*;

                let mutator = |kind| matches!(kind, Add | Sub | Mul | Div);

                let write_mutator_op = |comp: &mut Self, ctx, kind| {
                    let op = match kind {
                        Add => Op::Add,
                        Sub => Op::Sub,
                        Mul => Op::Mul,
                        Div => Op::Div,
                        Nop => {
                            return;
                        }
                    };
                    comp.add_op(ctx, statement.span, op);
                };

                match &target.kind {
                    Read(ident) => {
                        if mutator(*kind) {
                            self.read_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                        }
                        self.expression(value, ctx);

                        write_mutator_op(self, ctx, *kind);

                        self.set_identifier(&ident.name, statement.span, ctx, ctx.namespace);
                    }
                    Variant { .. } => {
                        error!(
                            self.compiler,
                            statement.span, "Cannot assign to enum-variant"
                        );
                    }
                    ArrowCall(..) | Call(..) => {
                        error!(
                            self.compiler,
                            statement.span, "Cannot assign to result from function call"
                        );
                    }
                    Access(a, field) => {
                        if let Some(namespace) = self.assignable(a, ctx) {
                            if mutator(*kind) {
                                self.read_identifier(&field.name, statement.span, ctx, namespace);
                            }
                            self.expression(value, ctx);

                            write_mutator_op(self, ctx, *kind);

                            self.set_identifier(&field.name, statement.span, ctx, namespace);
                        } else {
                            let slot = self.compiler.string(&field.name);

                            if mutator(*kind) {
                                self.add_op(ctx, statement.span, Op::Copy(1));
                                self.add_op(ctx, field.span, Op::GetField(slot));
                            }
                            self.expression(value, ctx);

                            write_mutator_op(self, ctx, *kind);

                            self.add_op(ctx, field.span, Op::AssignField(slot));
                        }
                    }
                    Index(a, b) => {
                        self.assignable(a, ctx);
                        self.expression(b, ctx);

                        if mutator(*kind) {
                            self.add_op(ctx, statement.span, Op::Copy(2));
                            self.add_op(ctx, statement.span, Op::GetIndex);
                        }
                        self.expression(value, ctx);
                        write_mutator_op(self, ctx, *kind);

                        self.add_op(ctx, statement.span, Op::AssignIndex);
                    }
                    Expression(_) => {
                        unreachable!("Cannot assign to 'AssignableKind::Expression'");
                    }
                }
            }

            StatementExpression { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Pop);
            }

            Block { statements } => {
                let stack_size = self.compiler.frames[ctx.frame].variables.len();

                for statement in statements {
                    self.statement(statement, ctx);
                }

                self.pop_until_size(ctx, statement.span, stack_size);
            }

            Loop { condition, body } => {
                let start = self.next_ip(ctx);
                self.expression(condition, ctx);
                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);

                // Skip the next op - it's for the break
                //  start: .. condition ..
                //         JmpFalse(over)
                //  break: Jmp(end)
                //   over: .. loop ..
                //    end: ..
                self.add_op(ctx, condition.span, Op::Jmp(jump_from + 3));
                let break_from = self.add_op(ctx, condition.span, Op::Illegal);

                let stack_size = self.compiler.frames[ctx.frame].variables.len();
                self.loops.push(LoopFrame {
                    continue_addr: start,
                    break_addr: break_from,
                    stack_size,
                });
                self.statement(body, ctx);
                self.loops.pop();

                self.add_op(ctx, body.span, Op::Jmp(start));
                let out = self.next_ip(ctx);
                self.patch(ctx, jump_from, Op::JmpFalse(out));
                self.patch(ctx, break_from, Op::Jmp(out));
            }

            #[rustfmt::skip]
            If { condition, pass, fail } => {
                self.expression(condition, ctx);

                let jump_from = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(pass, ctx);
                let jump_out = self.add_op(ctx, condition.span, Op::Illegal);
                self.statement(fail, ctx);

                self.patch(ctx, jump_from, Op::JmpFalse(jump_out + 1));

                let end = self.next_ip(ctx);
                self.patch(ctx, jump_out, Op::Jmp(end));
            }

            Continue {} => match self.loops.last().cloned() {
                Some(LoopFrame { stack_size, continue_addr, .. }) => {
                    self.emit_pop_until_size(ctx, statement.span, stack_size);
                    self.add_op(ctx, statement.span, Op::Jmp(continue_addr));
                }
                None => {
                    error!(
                        self.compiler,
                        statement.span, "`continue` statement not in a loop"
                    );
                }
            },

            Break {} => match self.loops.last().cloned() {
                Some(LoopFrame { stack_size, break_addr, .. }) => {
                    self.emit_pop_until_size(ctx, statement.span, stack_size);
                    self.add_op(ctx, statement.span, Op::Jmp(break_addr));
                }
                None => {
                    error!(
                        self.compiler,
                        statement.span, "`continue` statement not in a loop"
                    );
                }
            },

            Unreachable {} => {
                self.add_op(ctx, statement.span, Op::Unreachable);
            }

            Ret { value } => {
                self.expression(value, ctx);
                self.add_op(ctx, statement.span, Op::Return);
            }
        }
    }

    pub fn compile(&mut self, statement: &Statement, namespace: usize) {
        let ctx = BytecodeContext { block_slot: 0, frame: 0, scope: 0, namespace };
        self.statement(&statement, ctx);
    }

    pub fn preamble(&mut self, span: Span, num_constants: usize) {
        let name = "/preamble/";
        let block = Block::new(name, 0, &self.compiler.namespace_id_to_path[&0]);
        self.blocks.push(block);

        let nil = self.compiler.constant(Value::Nil);
        // TODO(ed): This context is completely bogus...
        let ctx = BytecodeContext { block_slot: 0, frame: 0, namespace: 0, scope: 0 };
        for _ in 0..num_constants {
            // Uninitalized values have the value Nil
            self.add_op(ctx, span, nil);
        }
    }

    pub fn postamble(&mut self, span: Span) {
        let ctx = BytecodeContext {
            block_slot: 0,
            frame: self.compiler.frames.len() - 1,
            namespace: 0,
            scope: 0,
        };

        self.read_identifier("start", Span::zero(0), ctx, 0);
        self.add_op(ctx, Span::zero(0), Op::Call(0));

        let nil = self.compiler.constant(Value::Nil);
        self.add_op(ctx, span, nil);
        self.add_op(ctx, span, Op::Return);

        self.compiler.pop_frame(ctx.into());
    }
}

// TODO(ed): This should move to the typechecker - since we always want this check.
fn all_paths_return(statement: &Statement) -> bool {
    match &statement.kind {
        StatementKind::Assignment { .. }
        | StatementKind::Blob { .. }
        | StatementKind::Enum { .. }
        | StatementKind::Break
        | StatementKind::Continue
        | StatementKind::Definition { .. }
        | StatementKind::EmptyStatement
        | StatementKind::ExternalDefinition { .. }
        | StatementKind::IsCheck { .. }
        | StatementKind::StatementExpression { .. }
        | StatementKind::Unreachable
        | StatementKind::FromUse { .. }
        | StatementKind::Use { .. } => false,

        StatementKind::If { pass, fail, .. } => all_paths_return(pass) && all_paths_return(fail),

        StatementKind::Loop { body, .. } => all_paths_return(body),
        StatementKind::Block { statements } => statements.iter().any(all_paths_return),

        StatementKind::Ret { .. } => true,
    }
}
