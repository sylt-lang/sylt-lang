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
    parse_expr()
}

pub fn parse_expr() -> impl Parser<char, Expr, Error = Simple<char>> {
    let name = filter(|c: &char| (c.is_alphabetic() && c.is_lowercase()) || c == &'_')
        .then(filter(|c: &char| (c.is_alphanumeric() && c.is_ascii_alphabetic()) || c == &'_').repeated())
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
            expr.clone().delimited_by(just("("), just(")")).padded(),
        ));

        let op = |c| just(c).padded();

        let unary = op('!')
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

        let call =
            name.then(expr.padded().repeated().at_least(1))
                .map(|(f, args)| Expr::Call(f, args) );

        choice((call, sum))
    });

    expr.then_ignore(end())
}

#[cfg(test)]
mod test {

    use super::parse_expr;
    use chumsky::Parser;

    fn check_expr_no_syntax_error(src: &str) {
        let res = parse_expr().parse(src);
        assert!(
            res.is_ok(),
            "ERR:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
            src,
            res
        );
    }

    macro_rules! expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                check_expr_no_syntax_error($src);
            }
        };
    }

    fn check_expr_and_expect_syntax_error(src: &str) {
        let res = parse_expr().parse(src);
        assert!(
            res.is_err(),
            "ERR:\n{:?}\ngave:\n{:?}\nbut expected ERROR\n-----------\n",
            src,
            res
        );
    }

    macro_rules! no_expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                check_expr_and_expect_syntax_error($src);
            }
        };
    }

    expr_t!(int, "1");
    expr_t!(large_int, "123123");
    expr_t!(ident, "a");
    expr_t!(long_ident1, "abcde");
    expr_t!(long_ident2, "a_b_c");
    expr_t!(long_ident3, "_a_b_c");
    expr_t!(long_ident4, "snakeCase");
    expr_t!(neg1, "!1");
    expr_t!(neg2, "!(1 + 1)");
    expr_t!(add1, "1 + 1");
    expr_t!(add2, "1 + 1 + 1 + 1");
    expr_t!(sub1, "1 - 1");
    expr_t!(sub2, "1 - 1 - 1 - 1");
    expr_t!(mul1, "1 * 1");
    expr_t!(mul2, "1 * 1 * 1 * 1");
    expr_t!(div1, "1 / 1");
    expr_t!(div2, "1 / 1 / 1 / 1");
    expr_t!(mixed1, "1 * (2 + 3)");
    expr_t!(mixed2, "1 * (2 + 3) + 1");
    expr_t!(mixed3, "1 * (2 + 3) + 1");
    expr_t!(mixed4, "a * (a + 3) + a");
    expr_t!(mixed_ws1, "1*(    2 +  3  )+1");
    expr_t!(mixed_ws2, "1   *    (    2        +3)+1");

    // Probably controversial!
    expr_t!(call1, "a 1 2 3");
    expr_t!(call2, "a (1 + 2 + 3) (2 * 3) 3");
    expr_t!(call3, "f a + 1 b");

    no_expr_t!(il_ident1, "A");
    no_expr_t!(il_ident2, "Abcedef");
}
