use sylt_tokenizer::Token as T;

use crate::expect;

use super::{Context, ParseResult, Span};

#[derive(Debug, Clone)]
pub enum Type {
    /// The void type
    Void { span: Span },
    /// The integer type
    Int { span: Span },
    /// The float type
    Float { span: Span },
    /// The boolean type
    Bool { span: Span },
    /// The string type
    String { span: Span },

    Tuple { span: Span, types: Vec<Type>},
}

impl<'a> Type {
    pub fn parse(ctx: Context<'a>) -> ParseResult<'a, Type> {
        let old_ctx = ctx;
        let (ctx, token, span) = ctx.eat();

        let span = span.clone();

        match token {
            T::VoidType => Ok((ctx, Type::Void { span })),
            T::IntType => Ok((ctx, Type::Int { span })),
            T::FloatType => Ok((ctx, Type::Float { span })),
            T::BoolType => Ok((ctx, Type::Bool { span })),
            T::StrType => Ok((ctx, Type::String { span })),

            T::LeftBracket => list(old_ctx),
            T::LeftBrace => set_or_dict(old_ctx),
            T::LeftParen => tuple(old_ctx),

            _ => panic!(),
        }
    }

    pub fn span(&'a self) -> &'a Span {
        type_span(self)
    }
}

/// Parse a tuple
///
/// Example context
/// ```
/// ( int, int )
/// ^
/// ```
fn tuple<'a>(ctx: Context<'a>) -> ParseResult<'a, Type> {
    expect!(ctx, T::LeftParen);
    let start_span = ctx.span();
    let ctx = ctx.step();

    let mut types: Vec<Type> = Vec::new();

    let mut ctx = ctx;

    while !matches!(ctx.token(), T::RightParen) {
        if !types.is_empty() {
            expect!(ctx, T::Comma);
            ctx = ctx.step();
        }

        if matches!(ctx.token(), T::RightParen) {
            break;
        }

        let (next_ctx, ty) = Type::parse(ctx)?;
        types.push(ty);
        ctx = next_ctx;
    }

    let (ctx, token, end_span) = ctx.eat();
    assert!(matches!(token, T::RightParen));

    Ok((ctx, Type::Tuple {
        types,
        span: start_span.start..end_span.end,
    }))
}

/// Parse a set or a dict
///
/// Example context
/// ```
/// { int }
/// ^
/// ```
fn set_or_dict<'a>(ctx: Context<'a>) -> ParseResult<'a, Type> {
    todo!()
}

/// Parse a list
///
/// Example context
/// ```
/// { int }
/// ^
/// ```
fn list<'a>(ctx: Context<'a>) -> ParseResult<'a, Type> {
    todo!()
}

/// Parse a function
///
/// Example context
/// ```
/// fn a: int -> int do 1 end
/// ^^
/// ```
fn function<'a>(ctx: Context<'a>) -> ParseResult<'a, Type> {
    todo!()
}

fn type_span<'a>(ty: &'a Type) -> &'a Span {
    match ty {
        Type::Void { span } => span,
        Type::Int { span } => span,
        Type::Float { span } => span,
        Type::Bool { span } => span,
        Type::String { span } => span,
        Type::Tuple { span, types } => span,
    }
}
