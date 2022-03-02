use std::fmt::{self, Write};
use std::path::Path;
use sylt_common::{Error, Type as RuntimeType};
use sylt_parser::expression::ComparisonKind;
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op, Statement,
    StatementKind, Type, TypeAssignable, TypeAssignableKind, TypeConstraint, TypeKind, VarKind,
};

static INDENT: &'static str = "    ";

macro_rules! write_comma_separated {
    ($dest:expr, $indent:expr, $write:expr, $values:expr) => {
        let mut first = true;
        for value in $values {
            if !first {
                write!($dest, ", ")?;
            }
            first = false;
            $write($dest, $indent, value)?;
        }
    };
}

fn write_indents<W: Write>(dest: &mut W, indent: u32) -> fmt::Result {
    for _ in 0..indent {
        write!(dest, "{}", INDENT)?;
    }
    Ok(())
}

fn write_identifier<W: Write>(dest: &mut W, identifier: Identifier) -> fmt::Result {
    write!(dest, "{}", identifier.name)
}

fn write_parameters<W: Write>(
    dest: &mut W,
    indent: u32,
    parameters: Vec<(Identifier, Type)>,
) -> fmt::Result {
    let mut first = true;
    for (identifier, ty) in parameters {
        if !first {
            write!(dest, ", ")?;
        }
        first = false;
        write_identifier(dest, identifier)?;
        write!(dest, ": ")?;
        write_type(dest, indent, ty)?;
    }
    Ok(())
}

fn write_blob_fields<T, W: Write>(
    dest: &mut W,
    indent: u32,
    mut fields: Vec<(String, T)>,
    sub_write: fn(&mut W, u32, T) -> fmt::Result,
) -> fmt::Result {
    write!(dest, " {{")?;
    match fields.len() {
        0 => {
            write!(dest, " }}")?;
        }
        1 => {
            let (field, expr) = fields.pop().unwrap();
            write!(dest, " {}: ", field)?;
            sub_write(dest, indent, expr)?;
            write!(dest, " }}")?;
        }
        _ => {
            write!(dest, "\n")?;
            for (field, t) in fields {
                write_indents(dest, indent)?;
                write!(dest, "{}: ", field)?;
                sub_write(dest, indent, t)?;
                write!(dest, ",\n")?;
            }
            write_indents(dest, indent - 1)?;
            write!(dest, "}}")?;
        }
    }
    Ok(())
}

fn write_enum_variants<W: Write>(
    dest: &mut W,
    indent: u32,
    mut variants: Vec<(String, Type)>,
) -> fmt::Result {
    match variants.len() {
        0 => {
            write!(dest, "\n")?;
        }
        1 => {
            let (var, ty) = variants.pop().unwrap();
            write!(dest, " {} ", var)?;
            write_type(dest, indent, ty)?;
            write!(dest, " ")?;
        }
        _ => {
            write!(dest, "\n")?;
            for (var, ty) in variants {
                write_indents(dest, indent)?;
                write!(dest, "{} ", var)?;
                write_type(dest, indent, ty)?;
                write!(dest, ",\n")?;
            }
            write_indents(dest, indent - 1)?;
        }
    }
    write!(dest, "end")?;
    Ok(())
}

fn write_constraint<W: Write>(
    dest: &mut W,
    _indent: u32,
    constraint: (String, Vec<TypeConstraint>),
) -> fmt::Result {
    let (name, constraints) = constraint;
    write!(dest, "{}: ", name)?;
    for (i, constraint) in constraints.iter().enumerate() {
        if i != 0 {
            write!(dest, " + ")?;
        }

        write!(dest, "{}", constraint.name.name)?;
        for arg in constraint.args.iter() {
            write!(dest, " {}", arg.name)?;
        }
    }

    Ok(())
}

fn write_type<W: Write>(dest: &mut W, indent: u32, ty: Type) -> fmt::Result {
    match ty.kind {
        TypeKind::Implied => unreachable!(),
        TypeKind::Resolved(ty) => write!(dest, "{}", ty),
        TypeKind::UserDefined(assignable, args) => {
            write_type_assignable(dest, indent, assignable)?;
            write!(dest, "(")?;
            write_comma_separated!(
                dest,
                indent,
                &|dest: &mut W, _, arg| write_type(dest, indent, arg),
                args
            );
            write!(dest, ")")
        }
        TypeKind::Fn { constraints, params, ret, is_pure } => {
            if is_pure {
                write!(dest, "pu")?;
            } else {
                write!(dest, "fn")?;
            }
            if !constraints.is_empty() {
                write!(dest, "<")?;
                write_comma_separated!(dest, indent, write_constraint, constraints);
                write!(dest, ">")?;
            }
            if !params.is_empty() {
                write!(dest, " ")?;
                write_comma_separated!(dest, indent, write_type, params);
            }
            write!(dest, " -> ")?;
            write_type(dest, indent, *ret)
        }
        TypeKind::Tuple(types) => {
            write!(dest, "(")?;
            let len = types.len();
            write_comma_separated!(dest, indent, write_type, types);
            if len == 1 {
                write!(dest, ",")?;
            }
            write!(dest, ")")
        }
        TypeKind::List(ty) => {
            write!(dest, "[")?;
            write_type(dest, indent, *ty)?;
            write!(dest, "]")
        }
        TypeKind::Set(ty) => {
            write!(dest, "{{")?;
            write_type(dest, indent, *ty)?;
            write!(dest, "}}")
        }
        TypeKind::Dict(key, val) => {
            write!(dest, "{{")?;
            write_type(dest, indent, *key)?;
            write!(dest, ": ")?;
            write_type(dest, indent, *val)?;
            write!(dest, "}}")
        }
        TypeKind::Generic(ident) => write!(dest, "*{}", ident),
        TypeKind::Grouping(ty) => {
            write!(dest, "(")?;
            write_type(dest, indent, *ty)?;
            write!(dest, ")")
        }
    }
}

fn write_type_assignable<W: Write>(
    dest: &mut W,
    indent: u32,
    assignable: TypeAssignable,
) -> fmt::Result {
    match assignable.kind {
        TypeAssignableKind::Read(identifier) => write_identifier(dest, identifier),
        TypeAssignableKind::Access(accessable, ident) => {
            write_type_assignable(dest, indent, *accessable)?;
            write!(dest, ".")?;
            write_identifier(dest, ident)
        }
    }
}

fn write_assignable<W: Write>(dest: &mut W, indent: u32, assignable: Assignable) -> fmt::Result {
    match assignable.kind {
        AssignableKind::Variant { enum_ass, variant, value } => {
            write_assignable(dest, indent, *enum_ass)?;
            write!(dest, ".{} ", variant.name)?;
            write_expression(dest, indent, *value)
        }
        AssignableKind::Read(identifier) => write_identifier(dest, identifier),
        AssignableKind::Call(callable, args) => {
            write_assignable(dest, indent, *callable)?;
            write!(dest, "(")?;
            write_comma_separated!(dest, indent, write_expression, args);
            write!(dest, ")")
        }
        AssignableKind::ArrowCall(first, callable, rest) => {
            write_expression(dest, indent, *first)?;
            write!(dest, " -> ")?;
            write_assignable(dest, indent, *callable)?;
            write!(dest, "(")?;
            write_comma_separated!(dest, indent, write_expression, rest);
            write!(dest, ")")?;
            Ok(())
        }
        AssignableKind::Access(accessable, ident) => {
            write_assignable(dest, indent, *accessable)?;
            write!(dest, ".")?;
            write_identifier(dest, ident)
        }
        AssignableKind::Index(indexable, index) => {
            write_assignable(dest, indent, *indexable)?;
            write!(dest, "[")?;
            write_expression(dest, indent, *index)?;
            write!(dest, "]")
        }
        AssignableKind::Expression(expr) => write_expression(dest, indent, *expr),
    }
}

macro_rules! expr_binary_op {
    ($dest:expr, $indent:expr, $lhs:expr, $op:literal, $rhs:expr) => {
        write_expression($dest, $indent, $lhs)?;
        write!($dest, $op)?;
        write_expression($dest, $indent, $rhs)?;
    };
}

fn write_expression<W: Write>(dest: &mut W, indent: u32, expression: Expression) -> fmt::Result {
    match expression.kind {
        ExpressionKind::Get(assignable) => write_assignable(dest, indent, assignable)?,
        ExpressionKind::Add(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " + ", *rhs);
        }
        ExpressionKind::Sub(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " - ", *rhs);
        }
        ExpressionKind::Mul(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " * ", *rhs);
        }
        ExpressionKind::Div(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " / ", *rhs);
        }
        ExpressionKind::Neg(expr) => {
            write!(dest, "-")?;
            write_expression(dest, indent, *expr)?;
        }
        ExpressionKind::Comparison(lhs, cmp, rhs) => match cmp {
            ComparisonKind::Equals => {
                expr_binary_op!(dest, indent, *lhs, " == ", *rhs);
            }
            ComparisonKind::NotEquals => {
                expr_binary_op!(dest, indent, *lhs, " != ", *rhs);
            }
            ComparisonKind::Greater => {
                expr_binary_op!(dest, indent, *lhs, " > ", *rhs);
            }
            ComparisonKind::GreaterEqual => {
                expr_binary_op!(dest, indent, *lhs, " >= ", *rhs);
            }
            ComparisonKind::Less => {
                expr_binary_op!(dest, indent, *lhs, " < ", *rhs);
            }
            ComparisonKind::LessEqual => {
                expr_binary_op!(dest, indent, *lhs, " <= ", *rhs);
            }
            ComparisonKind::In => {
                expr_binary_op!(dest, indent, *lhs, " in ", *rhs);
            }
        },
        ExpressionKind::AssertEq(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " <=> ", *rhs);
        }
        ExpressionKind::And(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " and ", *rhs);
        }
        ExpressionKind::Or(lhs, rhs) => {
            expr_binary_op!(dest, indent, *lhs, " or ", *rhs);
        }
        ExpressionKind::Not(expr) => {
            write!(dest, "not ")?;
            write_expression(dest, indent, *expr)?;
        }
        ExpressionKind::Parenthesis(expr) => {
            write!(dest, "(")?;
            write_expression(dest, indent, *expr)?;
            write!(dest, ")")?;
        }
        ExpressionKind::If(branches) => {
            for (i, branch) in branches.into_iter().enumerate() {
                match (branch.condition, i == 0) {
                    (Some(expr), true) => {
                        write!(dest, "if ")?;
                        write_expression(dest, indent, expr)?;
                        write!(dest, " do\n")?;
                    }
                    (None, true) => unreachable!("The parser should never return this"),
                    (Some(expr), _) => {
                        write!(dest, "elif ")?;
                        write_expression(dest, indent, expr)?;
                        write!(dest, " do\n")?;
                    }
                    (None, _) => {
                        write!(dest, "else\n")?;
                    }
                }
                for stmt in branch.body {
                    write_statement(dest, indent + 1, stmt)?;
                }
            }
            write_indents(dest, indent)?;
            write!(dest, "end\n")?;
        }
        ExpressionKind::Case { to_match, branches, fall_through } => {
            write!(dest, "case ")?;
            write_expression(dest, indent, *to_match)?;
            write!(dest, " do\n")?;
            for branch in branches {
                write_indents(dest, indent + 1)?;
                write_identifier(dest, branch.pattern)?;
                if let Some(var) = branch.variable {
                    write!(dest, " ")?;
                    write_identifier(dest, var)?;
                }
                write!(dest, " ->\n")?;
                for stmt in branch.body.into_iter() {
                    write_statement(dest, indent + 1, stmt)?;
                }
                write_indents(dest, indent + 1)?;
                write!(dest, "end\n")?;
            }
            if let Some(fall_through) = fall_through {
                write_indents(dest, indent + 1)?;
                write!(dest, "else\n")?;
                for stmt in fall_through.into_iter() {
                    write_statement(dest, indent + 1, stmt)?;
                }
                write_indents(dest, indent + 1)?;
                write!(dest, "end\n")?;
            }
            write_indents(dest, indent)?;
            write!(dest, "end\n")?;
        }
        ExpressionKind::Function { name: _, params, ret, body, pure } => {
            if pure {
                write!(dest, "pu")?;
            } else {
                write!(dest, "fn")?;
            }
            if !params.is_empty() {
                write!(dest, " ")?;
            }
            write_parameters(dest, indent, params)?;
            if matches!(ret.kind, TypeKind::Resolved(RuntimeType::Void)) {
                write!(dest, " ")?;
            } else {
                write!(dest, " -> ")?;
                write_type(dest, indent, ret)?;
                write!(dest, " ")?;
            }

            write!(dest, "do\n")?;
            for s in merge_empty_statements(body) {
                write_statement(dest, indent + 1, s)?;
            }
            write_indents(dest, indent)?;
            // NOTE(ed): No newline here!
            write!(dest, "end")?;
        }
        ExpressionKind::Blob { blob, fields } => {
            write_type_assignable(dest, indent, blob)?;
            write_blob_fields(dest, indent + 1, fields, write_expression)?;
        }
        ExpressionKind::Tuple(exprs) => {
            let num_exprs = exprs.len();
            write!(dest, "(")?;
            write_comma_separated!(dest, indent, write_expression, exprs);
            if num_exprs == 1 {
                write!(dest, ",")?;
            }
            write!(dest, ")")?;
        }
        ExpressionKind::List(exprs) => {
            write!(dest, "[")?;
            write_comma_separated!(dest, indent, write_expression, exprs);
            write!(dest, "]")?;
        }
        ExpressionKind::Set(exprs) => {
            write!(dest, "{{")?;
            write_comma_separated!(dest, indent, write_expression, exprs);
            write!(dest, "}}")?;
        }
        ExpressionKind::Dict(exprs) => {
            write!(dest, "{{")?;
            if exprs.is_empty() {
                write!(dest, ":")?;
            } else {
                let mut first = true;
                let mut exprs = exprs.into_iter();
                while let Some(expr) = exprs.next() {
                    if !first {
                        write!(dest, ", ")?;
                    }
                    first = false;
                    write_expression(dest, indent, expr)?;
                    write!(dest, ": ")?;
                    write_expression(dest, indent, exprs.next().unwrap())?;
                }
            }
            write!(dest, "}}")?;
        }
        ExpressionKind::Float(f) => write!(dest, "{:?}", f)?,
        ExpressionKind::Int(i) => write!(dest, "{}", i)?,
        ExpressionKind::Str(s) => write!(dest, "\"{}\"", s)?,
        ExpressionKind::Bool(b) => write!(dest, "{}", b)?,
        ExpressionKind::Nil => write!(dest, "nil")?,
    }

    Ok(())
}

fn write_statement<W: Write>(dest: &mut W, indent: u32, statement: Statement) -> fmt::Result {
    for comment in &statement.comments {
        write_indents(dest, indent)?;
        write!(dest, "// {}\n", comment)?;
    }

    match statement.kind {
        StatementKind::Assignment { kind, target, value } => {
            write_indents(dest, indent)?;
            write_assignable(dest, indent, target)?;
            write!(
                dest,
                " {}= ",
                match kind {
                    Op::Nop => "",
                    Op::Add => "+",
                    Op::Sub => "-",
                    Op::Mul => "*",
                    Op::Div => "/",
                }
            )?;
            write_expression(dest, indent, value)?;
        }
        StatementKind::Block { statements } => {
            write_indents(dest, indent)?;
            write!(dest, "do\n")?;

            for s in merge_empty_statements(statements) {
                write_statement(dest, indent + 1, s)?;
            }

            write_indents(dest, indent)?;
            write!(dest, "end")?
        }
        StatementKind::Blob { name, fields, variables, external } => {
            write_indents(dest, indent)?;
            match external {
                true => write!(dest, "{} :: externblob", name)?,
                false => write!(dest, "{} :: blob", name)?,
            };
            if variables.len() > 0 {
                write!(dest, "(")?;
                write_comma_separated!(
                    dest,
                    indent,
                    &|dest: &mut W, _, var: Identifier| write!(dest, "*{}", var.name),
                    variables
                );
                write!(dest, ")")?;
            }
            let fields_as_tuples = fields.into_iter().map(|(k, v)| (k.name, v)).collect();
            write_blob_fields(dest, indent + 1, fields_as_tuples, write_type)?;
        }
        StatementKind::Enum { name, variants, variables } => {
            write_indents(dest, indent)?;
            write!(dest, "{} :: enum", name.name)?;
            if variables.len() > 0 {
                write!(dest, "(")?;
                write_comma_separated!(
                    dest,
                    indent,
                    &|dest: &mut W, _, var: Identifier| write!(dest, "*{}", var.name),
                    variables
                );
                write!(dest, ")")?;
            }
            let variants_as_tuples = variants.into_iter().map(|(k, v)| (k.name, v)).collect();
            write_enum_variants(dest, indent + 1, variants_as_tuples)?;
        }
        StatementKind::Break => {
            write_indents(dest, indent)?;
            write!(dest, "break")?
        }
        StatementKind::Continue => {
            write_indents(dest, indent)?;
            write!(dest, "continue")?
        }
        StatementKind::ExternalDefinition { ident, kind, ty } => {
            assert!(!matches!(ty.kind, TypeKind::Implied), "Should not parse");

            write_indents(dest, indent)?;
            write_identifier(dest, ident)?;
            write!(dest, ": ")?;
            write_type(dest, indent, ty)?;
            if kind.immutable() {
                write!(dest, " : ")?;
            } else {
                write!(dest, " = ")?;
            }
            write!(dest, "external")?;
        }
        StatementKind::Definition { ident, kind, ty, value } => {
            write_indents(dest, indent)?;
            write_identifier(dest, ident)?;
            if matches!(ty.kind, TypeKind::Implied) {
                write!(
                    dest,
                    "{}",
                    match kind {
                        VarKind::Const => " :: ",
                        VarKind::Mutable => " := ",
                    }
                )?;
            } else {
                write!(dest, ": ")?;
                write_type(dest, indent, ty)?;
                if kind.immutable() {
                    write!(dest, " : ")?;
                } else {
                    write!(dest, " = ")?;
                }
            }
            write_expression(dest, indent, value)?;
        }
        StatementKind::EmptyStatement => (),
        StatementKind::Loop { condition, body } => {
            write_indents(dest, indent)?;
            write!(dest, "loop ")?;
            write_expression(dest, indent, condition)?;
            write!(dest, " ")?;
            write_statement(dest, indent, *body)?;
        }
        StatementKind::Ret { value: Some(value) } => {
            write_indents(dest, indent)?;
            write!(dest, "ret ")?;
            write_expression(dest, indent, value)?;
        }
        StatementKind::Ret { value: None } => {
            write_indents(dest, indent)?;
            write!(dest, "ret")?;
        }
        StatementKind::StatementExpression { value } => {
            write_indents(dest, indent)?;
            write_expression(dest, indent, value)?;
        }
        StatementKind::Unreachable => {
            write_indents(dest, indent)?;
            write!(dest, "<!>")?;
        }
        StatementKind::Use { path, name, file: _ } => {
            write_indents(dest, indent)?;
            write!(dest, "use ")?;
            write_identifier(dest, path)?;
            if let NameIdentifier::Alias(alias) = name {
                write!(dest, " as ")?;
                write_identifier(dest, alias)?;
            }
        }
        StatementKind::FromUse { path, imports, file: _ } => {
            fn write_import<W: Write>(
                dest: &mut W,
                _indent: u32,
                import: (Identifier, Option<Identifier>),
            ) -> fmt::Result {
                write_identifier(dest, import.0.clone())?;
                if let Some(alias) = import.1 {
                    write!(dest, " as ")?;
                    write_identifier(dest, alias.clone())
                } else {
                    Ok(())
                }
            }
            write_indents(dest, indent)?;
            write!(dest, "from ")?;
            write_identifier(dest, path)?;
            write!(dest, " use ")?;
            if imports.len() == 1 {
                write_import(dest, indent, imports[0].clone())?;
            } else {
                write!(dest, "(")?;
                write_comma_separated!(dest, indent, write_import, imports);
                write!(dest, ")")?;
            }
        }
    }
    write!(dest, "\n")?;

    Ok(())
}

/// Replace consecutive empty statements with one empty statement with all comments of the previous statements.
fn merge_empty_statements(mut statements: Vec<Statement>) -> Vec<Statement> {
    // Reverse since
    // - we always want to remove and look at the first statement and
    // - pop() is faster than remove(0).
    statements.reverse();

    let mut ret = Vec::new();
    while let Some(mut statement) = statements.pop() {
        // Begin eating empty statements
        while matches!(
            statements.last().map(|s| &s.kind),
            Some(StatementKind::EmptyStatement)
        ) {
            statement
                .comments
                .append(&mut statements.pop().unwrap().comments);
        }
        ret.push(statement);
    }
    ret
}

fn format_module(module: Module) -> Result<String, fmt::Error> {
    let mut formatted = String::new();
    merge_empty_statements(module.statements)
        .into_iter()
        // Side effects incoming!
        .map(|s| {
            write_statement(&mut formatted, 0, s)?;
            write!(formatted, "\n")
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(formatted)
}

pub fn format(file: &Path) -> Result<String, Vec<Error>> {
    let mut tree = sylt_parser::tree(file, crate::read_file, false)?;
    Ok(format_module(tree.modules.remove(0).1).unwrap())
}
