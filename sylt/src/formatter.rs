use std::fmt::{self, Write};
use std::path::PathBuf;
use sylt_common::{Error, Type as RuntimeType};
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op, Statement,
    StatementKind, Type, TypeKind, VarKind,
};

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

fn write_parameters<W: Write>(
    dest: &mut W,
    indent: u32,
    parameters: &[(Identifier, Type)],
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

fn write_arguments<W: Write>(dest: &mut W, indent: u32, arguments: &[Expression]) -> fmt::Result {
    let mut first = true;
    for arg in arguments {
        if !first {
            write!(dest, ", ")?;
        }
        first = false;
        write_expression(dest, indent, arg)?;
    }
    Ok(())
}

fn write_blob_instance_fields<W: Write>(
    dest: &mut W,
    indent: u32,
    fields: &[(String, Expression)],
) -> fmt::Result {
    todo!()
}

fn write_blob_type_fields<W: Write>(
    dest: &mut W,
    indent: u32,
    fields: &[(String, Type)],
) -> fmt::Result {
    todo!()
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

fn write_type<W: Write>(dest: &mut W, indent: u32, ty: &Type) -> fmt::Result {
    match &ty.kind {
        TypeKind::Implied => unreachable!(),
        TypeKind::Resolved(ty) => write_runtime_type(dest, ty),
        TypeKind::UserDefined(assignable) => write_assignable(dest, indent, assignable),
        TypeKind::Union(_, _) => todo!(),
        TypeKind::Fn(_, _) => todo!(),
        TypeKind::Tuple(_) => todo!(),
        TypeKind::List(_) => todo!(),
        TypeKind::Set(_) => todo!(),
        TypeKind::Dict(_, _) => todo!(),
    }
}

fn write_assignable<W: Write>(dest: &mut W, indent: u32, assignable: &Assignable) -> fmt::Result {
    match &assignable.kind {
        AssignableKind::Read(identifier) => write_identifier(dest, identifier),
        AssignableKind::Call(callable, args) => {
            write_assignable(dest, indent, callable)?;
            write!(dest, "(")?;
            write_arguments(dest, indent, args)?;
            write!(dest, ")")
        }
        AssignableKind::ArrowCall(first, callable, rest) => {
            write_expression(dest, indent, first)?;
            write!(dest, " -> ")?;
            write_assignable(dest, indent, callable)?;
            write!(dest, " ")?;
            write_arguments(dest, indent, rest)
        }
        AssignableKind::Access(accessable, ident) => {
            write_assignable(dest, indent, accessable)?;
            write!(dest, ".")?;
            write_identifier(dest, ident)
        }
        AssignableKind::Index(indexable, index) => {
            write_assignable(dest, indent, indexable)?;
            write!(dest, "[")?;
            write_expression(dest, indent, index)?;
            write!(dest, "]")
        }
        AssignableKind::Expression(expr) => write_expression(dest, indent, expr),
    }
}

macro_rules! expr_binary_op {
    ($dest:expr, $indent:expr, $lhs:expr, $op:literal, $rhs:expr) => {
        write_expression($dest, $indent, $lhs)?;
        write!($dest, $op)?;
        write_expression($dest, $indent, $rhs)?;
    };
}

fn write_expression<W: Write>(dest: &mut W, indent: u32, expression: &Expression) -> fmt::Result {
    match &expression.kind {
        ExpressionKind::Get(assignable) => write_assignable(dest, indent, assignable)?,
        ExpressionKind::TypeConstant(ty) => {
            write!(dest, ":")?;
            write_type(dest, indent, ty)?;
        }
        ExpressionKind::Add(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " + ", rhs);
        }
        ExpressionKind::Sub(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " - ", rhs);
        }
        ExpressionKind::Mul(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " * ", rhs);
        }
        ExpressionKind::Div(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " / ", rhs);
        }
        ExpressionKind::Neg(expr) => {
            write!(dest, "-")?;
            write_expression(dest, indent, expr)?;
        }
        ExpressionKind::Is(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " is ", rhs);
        }
        ExpressionKind::Eq(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " == ", rhs);
        }
        ExpressionKind::Neq(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " != ", rhs);
        }
        ExpressionKind::Gt(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " > ", rhs);
        }
        ExpressionKind::Gteq(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " >= ", rhs);
        }
        ExpressionKind::Lt(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " < ", rhs);
        }
        ExpressionKind::Lteq(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " <= ", rhs);
        }
        ExpressionKind::AssertEq(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " <=> ", rhs);
        }
        ExpressionKind::In(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " in ", rhs);
        }
        ExpressionKind::And(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " && ", rhs);
        }
        ExpressionKind::Or(lhs, rhs) => {
            expr_binary_op!(dest, indent, lhs, " || ", rhs);
        }
        ExpressionKind::Not(expr) => {
            write!(dest, "!")?;
            write_expression(dest, indent, expr)?;
        }
        ExpressionKind::IfExpression {
            condition,
            pass,
            fail,
        } => todo!(),
        ExpressionKind::Duplicate(_) => todo!(),
        ExpressionKind::IfShort { condition, fail } => todo!(),
        ExpressionKind::Function {
            name: _,
            params,
            ret,
            body,
        } => {
            write!(dest, "fn")?;
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
            write_statement(dest, indent, body)?;
        }
        ExpressionKind::Instance { blob, fields } => {
            write_assignable(dest, indent, blob)?;
            write!(dest, " {{\n")?;
            write_blob_instance_fields(dest, indent + 1, fields)?;
            write!(dest, "}}")?;
        }
        ExpressionKind::Tuple(_) => todo!(),
        ExpressionKind::List(_) => todo!(),
        ExpressionKind::Set(_) => todo!(),
        ExpressionKind::Dict(_) => todo!(),
        ExpressionKind::Float(f) => write!(dest, "{}", f)?,
        ExpressionKind::Int(i) => write!(dest, "{}", i)?,
        ExpressionKind::Str(s) => write!(dest, "\"{}\"", s)?,
        ExpressionKind::Bool(b) => write!(dest, "{}", if *b { "true" } else { "false" })?,
        ExpressionKind::Nil => write!(dest, "nil")?,
    }

    Ok(())
}

fn write_statement<W: Write>(dest: &mut W, indent: u32, statement: &Statement) -> fmt::Result {
    // Empty statements don't even deserve their own line!
    if matches!(statement.kind, StatementKind::EmptyStatement) {
        return Ok(());
    }

    match &statement.kind {
        StatementKind::Assignment {
            kind,
            target,
            value,
        } => {
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
        StatementKind::Blob { name, fields } => todo!(),
        StatementKind::Block { statements } => {
            write!(dest, "{{\n")?;

            for s in statements {
                if !matches!(s.kind, StatementKind::EmptyStatement) {
                    write_indents(dest, indent + 1)?;
                    write_statement(dest, indent + 1, s)?;
                    write!(dest, "\n")?;
                }
            }

            write_indents(dest, indent)?;
            write!(dest, "}}")?;
        }
        StatementKind::Break => todo!(),
        StatementKind::Continue => todo!(),
        StatementKind::Definition {
            ident,
            kind,
            ty,
            value,
        } => {
            write_identifier(dest, ident)?;
            if matches!(ty.kind, TypeKind::Implied) {
                write!(
                    dest,
                    " {} ",
                    match kind {
                        VarKind::Const => "::",
                        VarKind::Mutable => ":=",
                        VarKind::ForceConst => unreachable!(),
                        VarKind::ForceMutable => unreachable!(),
                    }
                )?;
            } else {
                todo!()
            }
            write_expression(dest, indent, value)?;
        }
        StatementKind::EmptyStatement => unreachable!("Should be handled earlier"),
        StatementKind::If {
            condition,
            pass,
            fail,
        } => {
            write!(dest, "if ")?;
            write_expression(dest, indent, condition)?;
            write!(dest, " ")?;
            write_statement(dest, indent, pass)?;
            if !matches!(fail.kind, StatementKind::EmptyStatement) {
                write!(dest, " else ")?;
                write_statement(dest, indent, fail)?;
            }
        }
        StatementKind::IsCheck { lhs, rhs } => todo!(),
        StatementKind::Loop { condition, body } => {
            write!(dest, "loop ")?;
            write_expression(dest, indent, condition)?;
            write!(dest, " ")?;
            write_statement(dest, indent, body)?;
        }
        StatementKind::Print { value } => {
            write!(dest, "print ")?;
            write_expression(dest, indent, value)?;
        }
        StatementKind::Ret { value } => {
            write!(dest, "ret ")?;
            write_expression(dest, indent, value)?;
        }
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
            write_statement(&mut formatted, 0, s)?;
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
