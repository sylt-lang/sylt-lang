use sylt_tokenizer::Token as T;

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
}

fn tuple(old_ctx: Context) -> Result<(Context, Type), (Context, super::ParseErr)> {
    todo!()
}

fn set_or_dict(old_ctx: Context) -> Result<(Context, Type), (Context, super::ParseErr)> {
    todo!()
}

fn list(old_ctx: Context) -> Result<(Context, Type), (Context, super::ParseErr)> {
    todo!()
}
