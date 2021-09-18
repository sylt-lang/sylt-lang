use std::fmt::{self, Write};
use std::path::PathBuf;
use sylt_common::{Error, Type as RuntimeType};
use sylt_parser::expression::ComparisonKind;
use sylt_parser::statement::NameIdentifier;
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op, Statement,
    StatementKind, Type, TypeKind, VarKind,
};

use crate::Args;

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

fn write_blob_fields<W: Write>(
    dest: &mut W,
    indent: u32,
    fields: Vec<(String, Expression)>,
) -> fmt::Result {
    for (field, expr) in fields {
        write_indents(dest, indent)?;
        write!(dest, "{}: ", field)?;
        write_expression(dest, indent, expr)?;
        write!(dest, ",\n")?;
    }
    Ok(())
}


fn simplify_type(ty: Type) -> Type {
    fn remove_duplicates(ty: Type, mut seen: Vec<Type>) -> Vec<Type> {
        match ty.kind {
            TK::Union(ty, rest) => {
                if seen.iter().find(|a| **a == *ty).is_none() {
                    seen.push(*ty);
                }
                remove_duplicates(*rest, seen)
            }
            _ => {
                if seen.iter().find(|a| **a == ty).is_none() {
                    seen.push(ty);
                }
                seen
            }
        }
    }

    use TypeKind as TK;
    match ty.kind {
        TK::Union(_, _) => {
            let without_dupes = remove_duplicates(ty.clone(), Vec::new());
            without_dupes.into_iter().reduce(|a, b| {
                // Swap order so we nest to the right
                Type { kind: TK::Union(Box::new(b), Box::new(a)), span: ty.span }
            }).unwrap() // We always get one type
        }

        TK::Fn(args, ret) =>
            Type { kind: TK::Fn(args.into_iter().map(simplify_type).collect(), Box::new(simplify_type(*ret))), ..ty },
        TK::Tuple(tys) =>
            Type { kind: TK::Tuple(tys.into_iter().map(simplify_type).collect()), ..ty },
        TK::List(a) =>
            Type { kind: TK::List(Box::new(simplify_type(*a))), ..ty },
        TK::Set(a) =>
            Type { kind: TK::Set(Box::new(simplify_type(*a))), ..ty },
        TK::Dict(a, b) =>
            Type { kind: TK::Dict(Box::new(simplify_type(*a)), Box::new(simplify_type(*b))), ..ty },

        TK::Implied
        | TK::UserDefined(_)
        | TK::Resolved(_)
        | TK::Generic(_) => ty,
    }
}

fn write_type<W: Write>(dest: &mut W, indent: u32, ty: Type) -> fmt::Result {
    let ty = simplify_type(ty);
    match ty.kind {
        TypeKind::Implied => unreachable!(),
        TypeKind::Resolved(ty) => write!(dest, "{}", ty),
        TypeKind::UserDefined(assignable) => write_assignable(dest, indent, assignable),
        TypeKind::Union(ty, rest) => {
            write_type(dest, indent, *ty)?;
            write!(dest, " | ")?;
            write_type(dest, indent, *rest)
        }
        TypeKind::Fn(params, ret) => {
            write!(dest, "fn")?;
            if !params.is_empty() {
                write!(dest, " ")?;
                write_comma_separated!(dest, indent, write_type, params);
            }
            write!(dest, " -> ")?;
            write_type(dest, indent, *ret)
        }
        TypeKind::Tuple(types) => {
            write!(dest, "(")?;
            write_comma_separated!(dest, indent, write_type, types);
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
        TypeKind::Generic(ident) => write_identifier(dest, ident),
    }
}

fn write_assignable<W: Write>(dest: &mut W, indent: u32, assignable: Assignable) -> fmt::Result {
    match assignable.kind {
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

fn write_arrow_call_no_lhs<W: Write>(dest: &mut W, indent: u32, expr: Expression) -> fmt::Result {
    match expr.kind {
        ExpressionKind::Get(assignable) => match assignable.kind {
            AssignableKind::ArrowCall(lhs, callee, rest) => {
                write_arrow_call_no_lhs(dest, indent, *lhs)?;
                write!(dest, " -> ")?;
                write_assignable(dest, indent, *callee)?;
                write!(dest, "(")?;
                write_comma_separated!(dest, indent, write_expression, rest);
                write!(dest, ")")?;
            }
            _ => (),
        },
        _ => (),
    }
    Ok(())
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
        ExpressionKind::TypeConstant(ty) => {
            write!(dest, ":")?;
            write_type(dest, indent, ty)?;
        }
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
            ComparisonKind::Is => {
                expr_binary_op!(dest, indent, *lhs, " is ", *rhs);
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
        ExpressionKind::IfExpression {
            condition,
            pass,
            fail,
        } => {
            write_expression(dest, indent, *pass)?;
            write!(dest, " if ")?;
            write_expression(dest, indent, *condition)?;
            write!(dest, " else ")?;
            write_expression(dest, indent, *fail)?;
        }
        ExpressionKind::Duplicate(expr) => write_expression(dest, indent, *expr)?,
        ExpressionKind::IfShort {
            condition,
            fail,
            lhs,
        } => {
            write_expression(dest, indent, *lhs)?;
            write!(dest, " if")?;
            match condition.kind {
                ExpressionKind::Comparison(_lhs, cmp, rhs) => {
                    write!(
                        dest,
                        " {} ",
                        match cmp {
                            ComparisonKind::Equals => "==",
                            ComparisonKind::NotEquals => "!=",
                            ComparisonKind::Greater => ">",
                            ComparisonKind::GreaterEqual => ">=",
                            ComparisonKind::Less => "<",
                            ComparisonKind::LessEqual => "<=",
                            ComparisonKind::Is => "is",
                            ComparisonKind::In => "in",
                        }
                    )?;
                    write_expression(dest, indent, *rhs)?;
                }
                ExpressionKind::Get(ref assignable) => match &assignable.kind {
                    AssignableKind::ArrowCall(..) => write_arrow_call_no_lhs(dest, indent, *condition)?,
                    kind => panic!(
                        "only arrow calls are supported in a short if expression, not {:?}",
                        kind
                    ),
                },
                kind => {
                    panic!("unsupported condition in a short if expression: {:?}", kind);
                }
            }
            write!(dest, " else ")?;
            write_expression(dest, indent, *fail)?;
        }
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
            write_statement(dest, indent, *body)?;
        }
        ExpressionKind::Blob { blob, fields } => {
            write_assignable(dest, indent, blob)?;
            write!(dest, " {{")?;
            if !fields.is_empty() {
                write!(dest, "\n")?;
                write_blob_fields(dest, indent + 1, fields)?;
                write_indents(dest, indent)?;
            }
            write!(dest, "}}")?;
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
        write!(dest, "// {}\n", comment)?;
        write_indents(dest, indent)?;
    }

    match statement.kind {
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
        StatementKind::Blob { name, fields } => {
            write!(dest, "{} :: blob {{", name)?;
            if !fields.is_empty() {
                write!(dest, "\n")?;
                for (field, ty) in fields {
                    write_indents(dest, indent + 1)?;
                    write!(dest, "{}: ", field)?;
                    write_type(dest, indent, ty)?;
                    write!(dest, ",\n")?;
                }
                write_indents(dest, indent)?;
            }
            write!(dest, "}}")?;
        }
        StatementKind::Block { statements } => {
            write!(dest, "do\n")?;

            for s in merge_empty_statements(statements) {
                write_indents(dest, indent + 1)?;
                write_statement(dest, indent + 1, s)?;
                write!(dest, "\n")?;
            }

            write_indents(dest, indent)?;
            write!(dest, "end")?;
        }
        StatementKind::Break => write!(dest, "break")?,
        StatementKind::Continue => write!(dest, "continue")?,
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
                    "{}",
                    match kind {
                        VarKind::Const => " :: ",
                        VarKind::Mutable => " := ",
                        VarKind::ForceConst => unreachable!("can't force an implied type"),
                        VarKind::ForceMutable => unreachable!("can't force an implied type"),
                    }
                )?;
            } else {
                write!(dest, ": ")?;
                if kind.force() {
                    write!(dest, "!")?;
                }
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
        StatementKind::If {
            condition,
            pass,
            fail,
        } => {
            if matches!(fail.kind, StatementKind::EmptyStatement) {
                for comment in &fail.comments {
                    write!(dest, "// {}\n", comment)?;
                    write_indents(dest, indent)?;
                }
            }

            write!(dest, "if ")?;
            write_expression(dest, indent, condition)?;
            write!(dest, " ")?;
            write_statement(dest, indent, *pass)?;
            if !matches!(fail.kind, StatementKind::EmptyStatement) {
                write!(dest, " else ")?;
                write_statement(dest, indent, *fail)?;
            }
        }
        StatementKind::IsCheck { lhs, rhs } => {
            write!(dest, ":")?;
            write_type(dest, indent, lhs)?;
            write!(dest, " is :")?;
            write_type(dest, indent, rhs)?;
        }
        StatementKind::Loop { condition, body } => {
            write!(dest, "loop ")?;
            write_expression(dest, indent, condition)?;
            write!(dest, " ")?;
            write_statement(dest, indent, *body)?;
        }
        StatementKind::Ret { value } => {
            write!(dest, "ret ")?;
            write_expression(dest, indent, value)?;
        }
        StatementKind::StatementExpression { value } => write_expression(dest, indent, value)?,
        StatementKind::Unreachable => {
            write!(dest, "<!>")?;
        }
        StatementKind::Use {
            path,
            name,
            file: _,
        } => {
            write!(dest, "use ")?;
            write_identifier(dest, path)?;
            if let NameIdentifier::Alias(alias) = name {
                write!(dest, " as ")?;
                write_identifier(dest, alias)?;
            }
        }
    }

    Ok(())
}

/// Replace consecutive empty statements with one empty statement with all comments of the previous statements.
//TODO(gu): Rewrite the formatter to use moves instead of borrows. Then we wouldn't need to clone when passing
//          into this function.
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

pub fn format(args: &Args) -> Result<String, Vec<Error>> {
    let mut tree = sylt_parser::tree(
        &PathBuf::from(args.args.first().expect("No file to run")),
        crate::read_file,
    )?;
    Ok(format_module(tree.modules.remove(0).1).unwrap())
}

#[cfg(test)]
macro_rules! test_formatter_on_file {
    ($fn:ident, $path:literal, $print:expr, $errs:pat) => {
        #[test]
        fn $fn() {
            use std::path::{Path, PathBuf};
            #[allow(unused_imports)]
            use sylt_common::{
                error::{Error, RuntimeError, TypeError},
                Type,
            };
            #[allow(unused_imports)]
            use sylt_tokenizer::Span;

            let path = format!("../{}", $path);

            // Run the file before the formatter.
            let mut args = $crate::Args::default();
            args.args = vec![path.clone()];
            let before = $crate::run_file(&args, ::sylt_std::sylt::_sylt_link());
            // If the test fails here, we already have / will have prettified output.
            assert!(
                matches!(before.err().unwrap_or(Vec::new()).as_slice(), $errs),
                "the test failed before the formatter was called"
            );

            // We now know that before contains $errs exactly.

            // Format the file.
            match $crate::formatter::format(&args) {
                Ok(formatted) => {
                    let formatted_path = PathBuf::from(&path).canonicalize().unwrap();
                    let read_formatted_or_file = |path: &Path| {
                        if path.canonicalize().unwrap() == formatted_path {
                            Ok(formatted.clone())
                        } else {
                            $crate::read_file(path)
                        }
                    };

                    // Try to run the file again, this time with pretty "got/expected"-output.
                    let after = $crate::run_file_with_reader(
                        &args,
                        ::sylt_std::sylt::_sylt_link(),
                        read_formatted_or_file,
                    );
                    eprintln!("The test output changed between before and after formatting");
                    $crate::assert_errs!(after, $errs);
                }
                Err(errs) => {
                    eprintln!("The formatter couldn't parse the file but the syntax errors");
                    eprintln!("changed between before and after formatting.");
                    let errs: Result<(), _> = Err(errs); //TODO(gu): Result<!, _> ;)
                    $crate::assert_errs!(errs, $errs);
                }
            }
        }
    };
}

#[cfg(test)]
sylt_macro::find_tests!(test_formatter_on_file);
