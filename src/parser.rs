use chumsky::prelude::*;

#[derive(Debug, Clone)]
pub struct Module {
    name: Ident,
    body: Vec<Def>,
}

#[derive(Debug, Clone)]
pub struct Ident {
    str: String,
}

#[derive(Debug, Clone)]
pub enum Def {
    Const { name: Ident, ty: Type, value: Expr },
}

#[derive(Debug, Clone)]
pub enum Expr {
    Int(i64),
    Var(Ident),
    Call(Ident, Vec<Expr>),

    Un(UnOp, Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    Neg,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
}

#[derive(Debug, Clone)]
pub enum Type {
    Int,
}

pub fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    let name = filter(|c: &char| c.is_alphabetic() && c.is_lowercase())
        .then(filter(|c: &char| c.is_ascii_alphabetic()).repeated())
        .map(|(c, mut cs)| {
            cs.insert(0, c);
            Ident { str: cs.into_iter().collect() }
        });

    let expr = recursive(|expr| {
        let int = text::int(10)
            .padded()
            .map(|s: String| s.parse::<i64>().unwrap())
            .map(|s: i64| Expr::Int(s));

        let term = choice((
            int,
            name.map(|n| Expr::Var(n)),
            expr.delimited_by(just("("), just(")")).padded(),
        ));

        let op = |c| just(c).padded();

        let unary = op('-')
            .repeated()
            .then(term)
            .foldr(|_op, rhs| Expr::Un(UnOp::Neg, Box::new(rhs)));

        let product = unary
            .clone()
            .then(
                (op('*').to(BinOp::Mul))
                    .or(op('/').to(BinOp::Div))
                    .then(unary)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| Expr::Bin(op, Box::new(lhs), Box::new(rhs)));

        let sum = product
            .clone()
            .then(
                (op('+').to(BinOp::Add))
                    .or(op('-').to(BinOp::Sub))
                    .then(product)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| Expr::Bin(op, Box::new(lhs), Box::new(rhs)));

        sum
    });

    expr.then_ignore(end())
}
