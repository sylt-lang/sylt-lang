use sylt_tokenizer::Token as T;

use crate::{expect, step_expect};

use super::{Context, ParseResult, Span};

#[derive(Debug, Clone)]
pub enum Type {
    /// The void type
    Void {
        span: Span,
    },
    /// The integer type
    Int {
        span: Span,
    },
    /// The float type
    Float {
        span: Span,
    },
    /// The boolean type
    Bool {
        span: Span,
    },
    /// The string type
    String {
        span: Span,
    },

    Tuple {
        span: Span,
        types: Vec<Type>,
    },
}

impl<'a> Type {
    /// Parse a type
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
            T::LeftParen => tuple_or_type(old_ctx),

            _ => panic!(),
        }
    }

    /// Get the span of the type
    pub fn span(&'a self) -> &'a Span {
        type_span(self)
    }
}

/// Parse a tuple
///
/// # Tuple
/// ```
/// ( int, int )
/// ^
/// ```
/// ```
/// (int,)
/// ^
/// ```
///
/// # Type
/// ```
/// (int)
/// ^
/// ```
fn tuple_or_type<'a>(ctx: Context<'a>) -> ParseResult<'a, Type> {
    let start_span = ctx.span();

    let mut ctx = step_expect!(ctx, T::LeftParen);

    // If right paren, empty tuple
    if matches!(ctx.token(), T::RightParen) {
        let (ctx, _, end_span) = ctx.eat();
        return Ok((
            ctx,
            Type::Tuple {
                span: start_span.start..end_span.end,
                types: Vec::new(),
            },
        ));
    }

    // Get all types in tuple
    let mut types: Vec<Type> = Vec::new();
    loop {
        // Parse the type
        let (next_ctx, ty) = Type::parse(ctx)?;
        ctx = next_ctx;
        types.push(ty);

        // Eat the next token
        let (next_ctx, token, span) = ctx.eat();
        ctx = next_ctx;

        // If we have a comma => may be trailing or loop again
        if matches!(token, T::Comma) {
            // It might be a trailing comma, check it
            if matches!(ctx.token(), T::RightParen) {
                let (ctx, token, end_span) = ctx.eat();
                return Ok((
                    ctx,
                    Type::Tuple { span: start_span.start..end_span.end, types },
                ));
            }
        } else if matches!(token, T::RightParen) {
            // The tuple is terminated, but may be single type
            if types.len() == 1 {
                return Ok((ctx, types.pop().unwrap()));
            } else {
                return Ok((ctx, Type::Tuple { span: start_span.start..span.end, types }));
            }
        } else {
            todo!("No separator or tuple termination")
        }
    }
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

/// Get the span of the type
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
