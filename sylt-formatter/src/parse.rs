use std::{ops::Range, slice};

use sylt_tokenizer::Token;

#[derive(Clone, Copy, Debug)]
struct Context<'a> {
    position: usize,
    tokens: &'a [(Token, Range<usize>)],
}

impl<'a> Context<'a> {
    fn new(tokens: &'a [(Token, Range<usize>)]) -> Self {
        Self { position: 0, tokens }
    }

    fn peek(self) -> &'a Token {
        self.peek_ahead(0)
    }

    fn peek_ahead(self, lookahead: usize) -> &'a Token {
        &self.tokens[self.position + lookahead].0
    }

    fn span(self) -> &'a Range<usize> {
        self.span_ahead(0)
    }

    fn span_ahead(self, lookahead: usize) -> &'a Range<usize> {
        &self.tokens[self.position + lookahead].1
    }

    fn eat(self) -> (Self, &'a Token, &'a Range<usize>) {
        (
            Self { position: self.position + 1, tokens: self.tokens },
            self.peek(),
            self.span(),
        )
    }
}

#[derive(Debug)]
pub struct Module<'a> {
    statements: Vec<Statement<'a>>,
}

#[derive(Debug)]
pub struct ParseErr {}

#[derive(Debug)]
pub enum Expression<'a> {
    Int(i64, &'a Range<usize>),
    Float(f64, &'a Range<usize>),
}

#[derive(Debug)]
pub enum Statement<'a> {
    Definition {
        var: (&'a String, &'a Range<usize>),
        expr: Expression<'a>,
    },
}

pub fn parse_module<'a>(tokens: &'a [(Token, Range<usize>)]) -> Result<Module<'a>, ParseErr> {
    let ctx = Context::new(tokens);
    let (statement, ctx) = parse_statement(ctx).unwrap();

    Ok(Module { statements: vec![statement] })
}

type ParseResult<'a, T: 'a> = Result<(T, Context<'a>), (ParseErr, Context<'a>)>;

fn parse_statement<'a>(ctx: Context<'a>) -> ParseResult<'a, Statement> {
    let (ctx, token, name_span) = ctx.eat();

    let name = if let Token::Identifier(name) = token {
        name
    } else {
        panic!();
    };

    let (ctx, token, span) = ctx.eat();
    assert!(matches!(token, Token::ColonColon));

    let (expression, ctx) = parse_expression(ctx)?;

    Ok((
        Statement::Definition { var: (name, name_span), expr: expression },
        ctx,
    ))
}

fn parse_expression<'a>(ctx: Context<'a>) -> ParseResult<'a, Expression> {
    match ctx.eat() {
        (ctx, Token::Int(v), span) => Ok((Expression::Int(*v, span), ctx)),
        _ => panic!(),
    }
}
