use std::collections::BTreeSet;
use std::{collections::HashMap, fmt::Display};

use crate::name_resolution::*;
use crate::ty::Type;
use crate::typechecker::TypeChecker;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum VarOrUpvalue {
    Var(Var),
    Upvalue(usize, Var),
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct Var(pub usize);

impl Var {
    pub fn format(self, var_to_name: &HashMap<Var, String>) -> String {
        match var_to_name.get(&self) {
            Some(name) => format!("V{}_{}", self.0, name),
            None => format!("V{}", self.0),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Label(pub usize);

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Label(n) = self;
        write!(f, "L{}", n)
    }
}

#[derive(Debug, Clone)]
pub enum IR {
    Nil(Var),
    Int(Var, i64),
    Float(Var, f64),
    Str(Var, String),
    Bool(Var, bool),
    Add(Var, Var, Var),
    Sub(Var, Var, Var),
    Mul(Var, Var, Var),
    Div(Var, Var, Var),
    Neg(Var, Var),

    Not(Var, Var),

    /// Variable to store in, function name, arity
    ExternalFunction(Var, String, usize),
    ExternalVar(Var, String),
    Call(Var, Var, Vec<Var>),

    Equals(Var, Var, Var),
    NotEquals(Var, Var, Var),
    Greater(Var, Var, Var),
    GreaterEqual(Var, Var, Var),
    Less(Var, Var, Var),
    LessEqual(Var, Var, Var),

    Assert(Var),

    List(Var, Vec<Var>),
    Tuple(Var, Vec<Var>),
    Blob(Var, Vec<(String, Var)>),
    Variant(Var, String, Var),

    // Name?
    Function(Vec<VarOrUpvalue>, Var, Vec<Var>),

    Index(Var, Var, Var),
    AssignIndex(Var, Var, Var),

    Access(Var, Var, String),
    AssignAccess(Var, String, Var),

    Label(Label),
    Goto(Label),
    Copy(Var, Var),
    /// Dest, UpvalueIndex, [Source] (Source is only used to count references because it's a lot
    /// easier.
    CopyUpvalue(Var, usize, Var),

    Define(Var),
    Assign(Var, Var),
    AssignUpvalue(Var, usize, Var),
    Return(Var),
    If(Var),
    HaltAndCatchFire(String),
    Loop,
    Break,
    Else,
    End,
    EndFunction,
}

#[derive(Debug, Clone, Copy)]
struct IRContext<'a> {
    closest_loop: Label,
    upvalues: &'a [usize],
}

impl<'a> IRContext<'a> {
    pub fn new(upvalues: &'a [usize]) -> Self {
        Self { closest_loop: Label(0), upvalues }
    }

    pub fn with_upvalues(self, upvalues: &'a [usize]) -> Self {
        Self { upvalues, ..self }
    }
}

struct IRCodeGen<'a> {
    #[allow(unused)]
    typechecker: &'a mut TypeChecker,

    var_to_name: HashMap<Var, String>,
    counter: usize,
}

fn get_upvalue_id(upvalues: &[usize], var: usize) -> Option<usize> {
    upvalues
        .iter()
        .enumerate()
        .find(|(_, x)| **x == var)
        .map(|(i, _)| i)
}

impl<'a> IRCodeGen<'a> {
    fn new(typechecker: &'a mut TypeChecker) -> Self {
        Self {
            // Temporary variables are placed after the stack allocated ones
            counter: typechecker.variables.len() + 1,
            var_to_name: HashMap::new(),
            typechecker,
        }
    }

    fn name_var(&mut self, var: Var, name: String) {
        self.var_to_name.insert(var, name);
    }

    fn var(&mut self) -> Var {
        let i = self.counter;
        self.counter += 1;
        Var(i)
    }

    fn label(&mut self) -> Label {
        let i = self.counter;
        self.counter += 1;
        Label(i)
    }

    fn expression_block(&mut self, out: Var, mut block: Vec<Statement>, ctx: IRContext) -> Vec<IR> {
        let value = match block.last().cloned() {
            Some(Statement::StatementExpression { value, .. }) => {
                block.pop();
                Some(value)
            }
            _ => None,
        };
        let ops = block
            .iter()
            .map(|stmt| self.statement(&stmt, ctx))
            .flatten()
            .collect();
        [
            ops,
            if let Some(value) = value {
                let (ops, var) = self.expression(&value, ctx);
                [ops, vec![IR::Assign(out, var)]].concat()
            } else {
                Vec::new()
            },
        ]
        .concat()
    }

    fn expression(&mut self, expr: &Expression, ctx: IRContext) -> (Vec<IR>, Var) {
        use Expression as E;
        use Statement as S;
        match &expr {
            E::ReadUpvalue { var, name, .. } => {
                let upvalue_index = get_upvalue_id(ctx.upvalues, *var).unwrap();
                let source = Var(*var);
                let dest = self.var();
                self.name_var(dest, name.clone());
                (vec![IR::CopyUpvalue(dest, upvalue_index, source)], dest)
            }

            E::Read { var, name, .. } => {
                let source = Var(*var);
                self.name_var(source, name.clone());
                let dest = self.var();
                self.name_var(dest, name.clone());
                (vec![IR::Copy(dest, source)], dest)
            }

            E::Variant { variant, value, .. } => {
                let (xops, x) = self.expression(&value, ctx);
                let out = self.var();
                (
                    [xops, vec![IR::Variant(out, variant.clone(), x)]].concat(),
                    out,
                )
            }

            E::Call { function, args, .. } => {
                let (fn_code, fn_var) = self.expression(function, ctx);
                let (code, args): (Vec<_>, Vec<_>) =
                    args.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();

                let var = self.var();
                (
                    [fn_code, code, vec![IR::Call(var, fn_var, args)]].concat(),
                    var,
                )
            }

            E::BlobAccess { value, field, .. } => {
                let (code, a) = self.expression(value, ctx);
                let b = self.var();
                ([code, vec![IR::Access(b, a, field.clone())]].concat(), b)
            }

            E::Index { value, index, .. } => {
                let (aops, a) = self.expression(&value, ctx);
                let (bops, b) = self.expression(&index, ctx);
                let c = self.var();

                ([aops, bops, vec![IR::Index(c, a, b)]].concat(), c)
            }

            E::BinOp { a, b, op: BinOp::AssertEq, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                (
                    [aops, bops, vec![IR::Equals(c, a, b), IR::Assert(c)]].concat(),
                    c,
                )
            }

            E::BinOp { a, b, op: BinOp::And, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                (
                    [
                        aops,
                        vec![IR::Bool(c, false), IR::If(a)],
                        bops,
                        vec![IR::Assign(c, b), IR::End],
                    ]
                    .concat(),
                    c,
                )
            }
            E::BinOp { a, b, op: BinOp::Or, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let neg_a = self.var();
                let c = self.var();
                (
                    [
                        aops,
                        vec![IR::Bool(c, true), IR::Not(neg_a, a), IR::If(neg_a)],
                        bops,
                        vec![IR::Assign(c, b), IR::End],
                    ]
                    .concat(),
                    c,
                )
            }

            E::BinOp { a, b, op, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let (bops, b) = self.expression(&b, ctx);
                let c = self.var();
                let ops = match op {
                    BinOp::Add => vec![IR::Add(c, a, b)],
                    BinOp::Sub => vec![IR::Sub(c, a, b)],
                    BinOp::Mul => vec![IR::Mul(c, a, b)],
                    BinOp::Div => vec![IR::Div(c, a, b)],
                    BinOp::Equals => vec![IR::Equals(c, a, b)],
                    BinOp::NotEquals => vec![IR::NotEquals(c, a, b)],
                    BinOp::Greater => vec![IR::Greater(c, a, b)],
                    BinOp::GreaterEqual => vec![IR::GreaterEqual(c, a, b)],
                    BinOp::Less => vec![IR::Less(c, a, b)],
                    BinOp::LessEqual => vec![IR::LessEqual(c, a, b)],
                    _ => unreachable!(),
                };
                ([aops, bops, ops].concat(), c)
            }

            E::UniOp { a, op: UniOp::Not, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let b = self.var();
                ([aops, vec![IR::Not(b, a)]].concat(), b)
            }

            E::UniOp { a, op: UniOp::Neg, .. } => {
                let (aops, a) = self.expression(&a, ctx);
                let b = self.var();
                ([aops, vec![IR::Neg(b, a)]].concat(), b)
            }

            E::If { branches, .. } => {
                let out = self.var();
                let code = branches
                    .iter()
                    .map(|IfBranch { condition, body, span: _ }| {
                        if let Some(cond) = condition {
                            let (expr, var) = self.expression(&cond, ctx);
                            let block = self.expression_block(out, body.clone(), ctx);
                            [expr, vec![IR::If(var)], block, vec![IR::Else]].concat()
                        } else {
                            let var = self.var();
                            let block = self.expression_block(out, body.clone(), ctx);
                            [vec![IR::Bool(var, true), IR::If(var)], block].concat()
                        }
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                (
                    [code, branches.iter().map(|_| IR::End).collect()].concat(),
                    out,
                )
            }

            E::Case { to_match, branches, fall_through, .. } => {
                let (cops, c) = self.expression(&to_match, ctx);
                let tag = self.var();
                let value = self.var();

                let out = self.var();

                let branches_code = branches
                    .iter()
                    .map(|CaseBranch { variable, pattern, body, .. }| {
                        let body = self.expression_block(out, body.clone(), ctx);

                        let exp_str = self.var();
                        let cmp = self.var();
                        [
                            if let Some(var) = variable {
                                vec![IR::Assign(Var(*var), value)]
                            } else {
                                Vec::new()
                            },
                            vec![
                                IR::Str(exp_str, pattern.name.clone()),
                                IR::Equals(cmp, exp_str, tag),
                                IR::If(cmp),
                            ],
                            body,
                            vec![IR::Else],
                        ]
                        .concat()
                    })
                    .flatten()
                    .collect();

                let fall_through_code = self.expression_block(
                    out,
                    fall_through.clone().unwrap_or_else(|| Vec::new()),
                    ctx,
                );

                let tag_index = self.var();
                let value_index = self.var();
                (
                    [
                        cops,
                        vec![
                            IR::Int(tag_index, 1),
                            IR::Index(tag, c, tag_index),
                            IR::Int(value_index, 2),
                            IR::Index(value, c, value_index),
                        ],
                        branches_code,
                        fall_through_code,
                        (0..branches.len()).map(|_| IR::End).collect(),
                    ]
                    .concat(),
                    out,
                )
            }

            E::Blob { self_var, fields, .. } => {
                let (fields, (code, exprs)): (Vec<_>, (Vec<_>, Vec<_>)) = fields
                    .iter()
                    .map(|(field, expr)| (field.clone(), self.expression(expr, ctx)))
                    .unzip();
                let code = code.concat();
                let fields: Vec<_> = fields.into_iter().zip(exprs.into_iter()).collect();
                let var = self.var();

                (
                    [
                        vec![IR::Define(Var(*self_var))],
                        code,
                        vec![IR::Blob(var, fields), IR::Assign(Var(*self_var), var)],
                    ]
                    .concat(),
                    var,
                )
            }

            E::Collection { collection: Collection::List, values, .. } => {
                let (code, values): (Vec<_>, Vec<_>) =
                    values.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::List(var, values)]].concat(), var)
            }

            E::Collection { collection: Collection::Tuple, values, .. } => {
                let (code, values): (Vec<_>, Vec<_>) =
                    values.iter().map(|expr| self.expression(expr, ctx)).unzip();
                let code = code.concat();
                let var = self.var();

                ([code, vec![IR::Tuple(var, values)]].concat(), var)
            }

            E::Function { body, params, upvalues, ty_id, .. } => {
                // Automatic dead-code elimination, if the function isn't called, we never generate
                // an instance.
                let (args, ret, instances) = match self.typechecker.find_type(*ty_id) {
                    Type::Function(args, ret, _, instances) => (args, ret, instances),
                    _ => unreachable!("Compiling a function that doesn't have a function type?"),
                };

                let baked_instances: BTreeSet<_> = instances
                    .iter()
                    .map(|(params, ret)| {
                        let params: Vec<_> = params
                            .iter()
                            .map(|p| self.typechecker.bake_type(*p))
                            .collect();
                        let ret = self.typechecker.bake_type(*ret);
                        (params, ret)
                    })
                    .collect();

                let args: Vec<_> = args
                    .iter()
                    .map(|x| self.typechecker.find(*x))
                    .collect();
                dbg!(&args);
                let ups: Vec<_> = upvalues
                    .iter()
                    .map(|u| {
                        self.typechecker.find_var(*u)
                    })
                    .collect();
                dbg!(&ups);
                let ret = self.typechecker.find(ret);
                dbg!(&ret);

                //
                // Some toughts:
                // Generating more functions.
                // 
                // I want to make sure I only generate each function once. I need to know all
                // instances of a function. When a function is returned as a value, it's not made
                // into an instance (maybe it should be?).
                // 
                // Functions inside functions needs to be generated in another way. To make sure
                // nothing is duplicated the types of the upvalues must be part of the key.
                // 
                // Maybe a stack of variables and their "known" types can solve this. We want to
                // generate code with these known types anyways.
                // 
                // These code-generation rules apply for built in opperators as well. Forexample `a
                // + b` should generate `a + b` and `strconcat(a, b, c)` depending on the context
                //
                // I also want to avoid propogating these types for each function and the like. The
                // typechecker already does this. Maybe the idea is tua actually use these types
                // from the typechecker somehow? This state needs to be copied somehow, and it
                // would be great if these states were combined eagerly (the way function calls
                // work probably cause a lot of the scaling errors in the typechecker.
                //
                // In short. I think there's a way to speed up the typechecker and get the
                // information I need. And I don't think it requires a lot of work. I just don't
                // know how to do it yet.

                // dbg!(&instances);
                // dbg!(&baked_instances);
                // TODO[et]: Check if there are Unknowns there

                let body = body.clone();
                let f = self.var();
                let params = params.iter().map(|(_, var, _, _)| Var(*var)).collect();
                let inner_ctx = ctx.with_upvalues(upvalues.as_slice());
                let body = body
                    .iter()
                    .map(|stmt| self.statement(stmt, inner_ctx))
                    .flatten()
                    .collect();

                let to_copy_over = upvalues
                    .iter()
                    // Is it an upvalue in the CURRENT context?
                    .map(|var| match get_upvalue_id(ctx.upvalues, *var) {
                        Some(x) => VarOrUpvalue::Upvalue(x, Var(*var)),
                        None => VarOrUpvalue::Var(Var(*var)),
                    })
                    .collect();
                (
                    [
                        vec![IR::Function(to_copy_over, f, params)],
                        body,
                        vec![IR::EndFunction],
                    ]
                    .concat(),
                    f,
                )
            }

            E::Float { value, .. } => {
                let var = self.var();
                (vec![IR::Float(var, *value)], var)
            }
            E::Str { value, .. } => {
                let var = self.var();
                (vec![IR::Str(var, value.into())], var)
            }

            E::Bool { value, .. } => {
                let a = self.var();
                (vec![IR::Bool(a, *value)], a)
            }

            E::Int { value, .. } => {
                let a = self.var();
                (vec![IR::Int(a, *value)], a)
            }

            E::Nil { .. } => {
                let a = self.var();
                (vec![IR::Nil(a)], a)
            }
        }
    }

    fn definition(&mut self, var: Var, value: &Expression, ctx: IRContext) -> Vec<IR> {
        if matches!(value, Expression::Function { .. }) {
            let (mut code, _) = self.expression(&value, ctx);
            if let IR::Function(upvalues, _, args) = &code[0] {
                code[0] = IR::Function(upvalues.clone(), var, args.clone());
            } else {
                unreachable!();
            }
            code
        } else {
            let (code, tmp) = self.expression(&value, ctx);
            [vec![IR::Define(var)], code, vec![IR::Assign(var, tmp)]].concat()
        }
    }

    fn statement(&mut self, stmt: &Statement, ctx: IRContext) -> Vec<IR> {
        use Expression as E;
        use Statement as S;
        match &stmt {
            S::Assignment { op, target, value, .. } => {
                let res = self.var();
                let (pre_code, current, post_code) = match &target {
                    E::Read { var, .. } => {
                        (Vec::new(), Var(*var), vec![IR::Assign(Var(*var), res)])
                    }
                    E::ReadUpvalue { var, name, .. } => {
                        let upvalue_index = get_upvalue_id(ctx.upvalues, *var).unwrap();
                        let source = Var(*var);
                        let dest = self.var();
                        self.name_var(dest, name.clone());
                        (
                            vec![IR::CopyUpvalue(dest, upvalue_index, source)],
                            dest,
                            vec![IR::AssignUpvalue(Var(*var), upvalue_index, res)],
                        )
                    }
                    E::Index { value, index, .. } => {
                        let (aops, a) = self.expression(value, ctx);
                        let (bops, b) = self.expression(index, ctx);
                        let c = self.var();

                        (
                            [aops, bops, vec![IR::Index(c, a, b)]].concat(),
                            c,
                            vec![IR::AssignIndex(a, b, res)],
                        )
                    }
                    E::BlobAccess { value, field, .. } => {
                        let (code, a) = self.expression(value, ctx);
                        let b = self.var();
                        (
                            [code, vec![IR::Access(b, a, field.clone())]].concat(),
                            b,
                            vec![IR::AssignAccess(a, field.clone(), res)],
                        )
                    }
                    E::Variant { .. }
                    | E::Call { .. }
                    | E::BinOp { .. }
                    | E::UniOp { .. }
                    | E::If { .. }
                    | E::Case { .. }
                    | E::Function { .. }
                    | E::Blob { .. }
                    | E::Collection { .. }
                    | E::Float { .. }
                    | E::Int { .. }
                    | E::Str { .. }
                    | E::Bool { .. }
                    | E::Nil { .. } => {
                        unreachable!("Not assignable, should be caught in the name_resolver")
                    }
                };
                let (code, var) = self.expression(&value, ctx);
                [
                    pre_code,
                    code,
                    vec![match op {
                        BinOp::Nop => IR::Assign(res, var),
                        BinOp::Add => IR::Add(res, current, var),
                        BinOp::Sub => IR::Sub(res, current, var),
                        BinOp::Mul => IR::Mul(res, current, var),
                        BinOp::Div => IR::Div(res, current, var),
                        _ => unreachable!(),
                    }],
                    post_code,
                ]
                .concat()
            }
            S::Definition { var, value, .. } => self.definition(Var(*var), value, ctx),
            S::Block { statements, .. } => {
                let stmt_code = statements
                    .iter()
                    .map(|stmt| self.statement(stmt, ctx))
                    .flatten()
                    .collect();
                stmt_code
            }

            S::Loop { condition, body, .. } => {
                let (cops, c) = self.expression(&condition, ctx);
                let l = self.label();
                let body = body
                    .iter()
                    .map(|stmt| self.statement(&stmt, IRContext { closest_loop: l, ..ctx }))
                    .flatten()
                    .collect();

                [
                    vec![IR::Loop, IR::Label(l)],
                    cops,
                    vec![IR::If(c), IR::Else, IR::Break, IR::End],
                    body,
                    vec![IR::End],
                ]
                .concat()
            }
            S::Break(..) => vec![IR::Break],
            S::Continue(..) => vec![IR::Goto(ctx.closest_loop)],
            S::Ret { value: Some(value), .. } => {
                let (aops, a) = self.expression(&value, ctx);
                [aops, vec![IR::Return(a)]].concat()
            }
            S::Ret { value: None, .. } => {
                // NOTE: In the runtime, we compile void to unit - don't tell Filip!
                let a = self.var();
                vec![IR::Nil(a), IR::Return(a)]
            }
            S::Unreachable(span) => {
                vec![IR::HaltAndCatchFire(format!(
                    "Reached unreachable code on line {}",
                    span.line_start
                ))]
            }

            S::StatementExpression { value, .. } => self.expression(value, ctx).0,

            S::Blob { .. } | S::Enum { .. } | S::ExternalDefinition { .. } => unreachable!(),
        }
    }

    fn compile(&mut self, stmt: &Statement) -> Vec<IR> {
        use Statement as S;
        let upvalues = Vec::new();
        let ctx = IRContext::new(&upvalues);
        match &stmt {
            S::ExternalDefinition { name, var, .. } => match self.typechecker.find_var_type(*var) {
                Type::Function(args, _, _, _) => {
                    vec![IR::ExternalFunction(Var(*var), name.clone(), args.len())]
                }
                _ => vec![IR::ExternalVar(Var(*var), name.clone())],
            },

            S::Definition { value, var, .. } => self.definition(Var(*var), value, ctx),

            // Invalid statements should be caught in the typechecker
            _ => Vec::new(),
        }
    }
}

#[sylt_macro::timed("intermediate::compile")]
pub(crate) fn compile(
    typechecker: &mut TypeChecker,
    statements: &Vec<Statement>,
) -> (Vec<IR>, HashMap<Var, String>) {
    let start = Var(typechecker
        .variables
        .iter()
        .find(|x| &x.name == "start" && x.is_global)
        .unwrap()
        .id);

    let mut gen = IRCodeGen::new(typechecker);

    let mut code: Vec<IR> = statements
        .iter()
        .map(|stmt| gen.compile(stmt))
        .flatten()
        .collect();

    let tmp = gen.var();
    code.push(IR::Call(tmp, start, Vec::new()));
    (code, gen.var_to_name)
}

// TODO(ed): We could remove more dead-code if we built a dependency-graph
// and removed all paths without side-effects, since they don't have
// an observable effect.
pub(crate) fn count_usages(ops: &[IR]) -> HashMap<Var, usize> {
    let mut table = HashMap::new();
    for op in ops {
        match op {
            IR::Nil(_)
            | IR::Int(_, _)
            | IR::Float(_, _)
            | IR::Str(_, _)
            | IR::Bool(_, _)
            | IR::Loop
            | IR::Break
            | IR::Else
            | IR::End
            | IR::EndFunction
            | IR::ExternalFunction(_, _, _)
            | IR::ExternalVar(_, _)
            | IR::Label(_)
            | IR::Goto(_)
            | IR::HaltAndCatchFire(_) => {}

            // We cannot optimize things that are defined.
            IR::Function(upvalues, a, _) => {
                for x in upvalues.iter() {
                    match x {
                        VarOrUpvalue::Upvalue(_, b) | VarOrUpvalue::Var(b) => {
                            *table.entry(*b).or_insert(0) += 2
                        }
                    }
                }
                *table.entry(*a).or_insert(0) += 2;
            }

            IR::Define(a) => {
                *table.entry(*a).or_insert(0) += 2;
            }

            IR::Add(_, a, b)
            | IR::Sub(_, a, b)
            | IR::Mul(_, a, b)
            | IR::Div(_, a, b)
            | IR::Equals(_, a, b)
            | IR::NotEquals(_, a, b)
            | IR::Greater(_, a, b)
            | IR::GreaterEqual(_, a, b)
            | IR::Less(_, a, b)
            | IR::LessEqual(_, a, b)
            | IR::Index(_, a, b)
            | IR::Assign(a, b)
            | IR::AssignUpvalue(a, _, b)
            | IR::AssignAccess(a, _, b)
            | IR::AssignIndex(_, a, b) => {
                *table.entry(*a).or_insert(0) += 1;
                *table.entry(*b).or_insert(0) += 1;
            }
            IR::Neg(_, a)
            | IR::Not(_, a)
            | IR::Assert(a)
            | IR::Variant(_, _, a)
            | IR::Access(_, a, _)
            | IR::Copy(_, a)
            | IR::CopyUpvalue(_, _, a)
            | IR::Return(a)
            | IR::If(a) => {
                *table.entry(*a).or_insert(0) += 1;
            }

            IR::Call(_, a, bs) => {
                *table.entry(*a).or_insert(0) += 1;
                for b in bs.iter() {
                    *table.entry(*b).or_insert(0) += 1;
                }
            }
            IR::List(_, xs) | IR::Tuple(_, xs) => {
                for x in xs.iter() {
                    *table.entry(*x).or_insert(0) += 1;
                }
            }
            IR::Blob(_, blob_vars) => {
                for (_, x) in blob_vars.iter() {
                    *table.entry(*x).or_insert(0) += 1;
                }
            }
        }
    }
    table
}
