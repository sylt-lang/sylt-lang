use std::fmt::{self, Write};
use std::path::PathBuf;
use sylt_common::{Error, Type as RuntimeType};
use sylt_parser::{Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op, Statement, StatementKind, Type, TypeKind, VarKind};

use crate::Args;

static INDENT: &'static str = "    ";

fn write_indents<W: Write>(dest: &mut W, indent: u32) -> fmt::Result {
    for _ in 0..indent {
        write!(dest, "{}", INDENT)?;
    }
    Ok(())
}

fn write_identifier<W: Write>(dest: &mut W, identifier: &Identifier) -> fmt::Result {
    write!(dest, "{}", identifier.name)
}

fn write_assignable<W: Write>(dest: &mut W, assignable: &Assignable) -> fmt::Result {
    match &assignable.kind {
        AssignableKind::Read(identifier) => write_identifier(dest, identifier),
        AssignableKind::Call(_, _) => todo!(),
        AssignableKind::ArrowCall(_, _, _) => todo!(),
        AssignableKind::Access(_, _) => todo!(),
        AssignableKind::Index(_, _) => todo!(),
        AssignableKind::Expression(_) => todo!(),
    }
}

fn write_runtime_type<W: Write>(dest: &mut W, ty: &RuntimeType) -> fmt::Result {
    match ty {
        RuntimeType::Ty => todo!(),
        RuntimeType::Field(_) => todo!(),
        RuntimeType::Void => write!(dest, "nil"),
        RuntimeType::Unknown => panic!(),
        RuntimeType::Int => write!(dest, "int"),
        RuntimeType::Float => write!(dest, "float"),
        RuntimeType::Bool => write!(dest, "bool"),
        RuntimeType::String => write!(dest, "str"),
        RuntimeType::Tuple(_) => todo!(),
        RuntimeType::Union(_) => todo!(),
        RuntimeType::List(_) => todo!(),
        RuntimeType::Set(_) => todo!(),
        RuntimeType::Dict(_, _) => todo!(),
        RuntimeType::Function(_, _) => todo!(),
        RuntimeType::Blob(_) => todo!(),
        RuntimeType::Instance(_) => todo!(),
        RuntimeType::ExternFunction(_) => todo!(),
        RuntimeType::Invalid => panic!(),
    }
}

fn write_type<W: Write>(dest: &mut W, ty: &Type) -> fmt::Result {
    match &ty.kind {
        TypeKind::Implied => unreachable!(),
        TypeKind::Resolved(ty) => write_runtime_type(dest, ty),
        TypeKind::UserDefined(assignable) => write_assignable(dest, assignable),
        TypeKind::Union(_, _) => todo!(),
        TypeKind::Fn(_, _) => todo!(),
        TypeKind::Tuple(_) => todo!(),
        TypeKind::List(_) => todo!(),
        TypeKind::Set(_) => todo!(),
        TypeKind::Dict(_, _) => todo!(),
    }
}

fn write_params<W: Write>(dest: &mut W, params: &[(Identifier, Type)]) -> fmt::Result {
    let mut first = true;
    for (identifier, ty) in params {
        if !first {
            write!(dest, ", ")?;
        }
        first = false;
        write_identifier(dest, identifier)?;
        write!(dest, ": ")?;
        write_type(dest, ty)?;
    }
    Ok(())
}

fn write_expression<W: Write>(dest: &mut W, expression: &Expression, indent: u32) -> fmt::Result {
    match &expression.kind {
        ExpressionKind::Get(_) => todo!(),
        ExpressionKind::TypeConstant(_) => todo!(),
        ExpressionKind::Add(_, _) => todo!(),
        ExpressionKind::Sub(_, _) => todo!(),
        ExpressionKind::Mul(_, _) => todo!(),
        ExpressionKind::Div(_, _) => todo!(),
        ExpressionKind::Neg(_) => todo!(),
        ExpressionKind::Is(_, _) => todo!(),
        ExpressionKind::Eq(_, _) => todo!(),
        ExpressionKind::Neq(_, _) => todo!(),
        ExpressionKind::Gt(_, _) => todo!(),
        ExpressionKind::Gteq(_, _) => todo!(),
        ExpressionKind::Lt(_, _) => todo!(),
        ExpressionKind::Lteq(_, _) => todo!(),
        ExpressionKind::AssertEq(_, _) => todo!(),
        ExpressionKind::In(_, _) => todo!(),
        ExpressionKind::And(_, _) => todo!(),
        ExpressionKind::Or(_, _) => todo!(),
        ExpressionKind::Not(_) => todo!(),
        ExpressionKind::IfExpression { condition, pass, fail } => todo!(),
        ExpressionKind::Duplicate(_) => todo!(),
        ExpressionKind::IfShort { condition, fail } => todo!(),
        ExpressionKind::Function { name: _, params, ret, body } => {
            write!(dest, "fn ")?;
            write_params(dest, params)?;
            if matches!(ret.kind, TypeKind::Resolved(RuntimeType::Void)) {
                write!(dest, " ")?;
            } else {
                write!(dest, " -> ")?;
                write_type(dest, ret)?;
                write!(dest, " ")?;
            }
            write_statement(dest, &*body, indent)
        }
        ExpressionKind::Instance { blob, fields } => todo!(),
        ExpressionKind::Tuple(_) => todo!(),
        ExpressionKind::List(_) => todo!(),
        ExpressionKind::Set(_) => todo!(),
        ExpressionKind::Dict(_) => todo!(),
        ExpressionKind::Float(_) => todo!(),
        ExpressionKind::Int(_) => todo!(),
        ExpressionKind::Str(_) => todo!(),
        ExpressionKind::Bool(_) => todo!(),
        ExpressionKind::Nil => todo!(),
    }
}

fn write_statement<W: Write>(dest: &mut W, statement: &Statement, indent: u32) -> fmt::Result {
    // Empty statements don't even deserve their own line!
    if matches!(statement.kind, StatementKind::EmptyStatement) {
        return Ok(());
    }

    write_indents(dest, indent)?;

    match &statement.kind {
        StatementKind::Assignment { kind, target, value } => {
            write_assignable(dest, target)?;
            write!(dest, " {}= ", match kind {
                Op::Nop => "",
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Div => "/",
            })?;
            write_expression(dest, value, indent)?;
        }
        StatementKind::Blob { name, fields } => todo!(),
        StatementKind::Block { statements } => {
            write!(dest, "{{\n")?;

            for s in statements {
                write_statement(dest, s, indent + 1)?;
                write!(dest, "\n")?;
            }

            write_indents(dest, indent)?;
            write!(dest, "}}")?;
        }
        StatementKind::Break => todo!(),
        StatementKind::Continue => todo!(),
        StatementKind::Definition { ident, kind, ty, value } => {
            write_identifier(dest, ident)?;
            if matches!(ty.kind, TypeKind::Implied) {
                write!(dest, " {} ", match kind {
                    VarKind::Const => "::",
                    VarKind::Mutable => ":=",
                    VarKind::ForceConst => unreachable!(),
                    VarKind::ForceMutable => unreachable!(),
                })?;
            } else {
                todo!()
            }
            write_expression(dest, value, indent)?;
        }
        StatementKind::EmptyStatement => unreachable!("Should be handled earlier"),
        StatementKind::If { condition, pass, fail } => todo!(),
        StatementKind::IsCheck { lhs, rhs } => todo!(),
        StatementKind::Loop { condition, body } => todo!(),
        StatementKind::Print { value } => todo!(),
        StatementKind::Ret { value } => todo!(),
        StatementKind::StatementExpression { value } => todo!(),
        StatementKind::Unreachable => {
            write!(dest, "<!>")?;
        }
        StatementKind::Use { file } => {
            write!(dest, "use ")?;
            write_identifier(dest, file)?;
        }
    }

    Ok(())
}

fn write_module(module: &Module) -> fmt::Result {
    let mut formatted = String::new();
    module
        .statements
        .iter()
        // Side effects incoming!
        .map(|s| {
            write_statement(&mut formatted, s, 0)?;
            write!(formatted, "\n")
        })
        .collect::<Result<Vec<_>, _>>()?;
    print!("{}", formatted);
    Ok(())
}

pub fn format(args: &Args) -> Result<(), Vec<Error>> {
    let tree = sylt_parser::tree(&PathBuf::from(args.args.first().expect("No file to run")))?;
    for (path, module) in &tree.modules {
        eprintln!("-- {}", path.display());
        write_module(module).unwrap();
    }
    Ok(())
}
