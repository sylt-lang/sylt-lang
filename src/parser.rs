use chumsky::prelude::*;

// #[derive(Debug, Clone)]
// pub struct Module {
//     name: Ident,
//     body: Vec<Def>,
// }

#[derive(Debug, Clone)]
pub struct Name {
    str: String,
}

#[derive(Debug, Clone)]
pub struct ProperName {
    str: String,
}

#[derive(Debug, Clone)]
pub enum Def {
    Def {
        ty: Type,
        name: Name,
        args: Vec<Name>,
        value: Expr,
    },
    Type {
        name: ProperName,
        args: Vec<Name>,
        ty: Type,
    },
}

#[derive(Debug, Clone)]
pub enum Expr {
    EInt(i64),
    Var(Name),
    Call(Name, Vec<Expr>),

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
    TEmpty,
    TCustom(ProperName, Vec<Type>),
    TVar(Name),
    TFunction(Box<Type>, Box<Type>),
}

pub fn parser() -> impl Parser<char, Type, Error = Simple<char>> + Clone {
    parse_type().then_ignore(parse_expr())
}

pub fn name() -> impl Parser<char, Name, Error = Simple<char>> + Clone {
    filter(|c: &char| (c.is_alphabetic() && c.is_lowercase()) || c == &'_')
        .then(
            filter(|c: &char| (c.is_alphanumeric() && c.is_ascii_alphabetic()) || c == &'_')
                .repeated(),
        )
        .map(|(c, mut cs)| {
            cs.insert(0, c);
            Name { str: cs.into_iter().collect() }
        })
}

pub fn proper_name() -> impl Parser<char, ProperName, Error = Simple<char>> + Clone {
    filter(|c: &char| c.is_alphabetic() && c.is_uppercase())
        .then(
            filter(|c: &char| (c.is_alphanumeric() && c.is_ascii_alphabetic()) || c == &'_')
                .repeated(),
        )
        .map(|(c, mut cs)| {
            cs.insert(0, c);
            ProperName { str: cs.into_iter().collect() }
        })
}

pub fn parse_def() -> impl Parser<char, Def, Error = Simple<char>> + Clone {
    let def = just("def")
        .padded()
        .ignore_then(name())
        .then(
            just(":")
                .padded()
                .ignore_then(parse_type().or(empty().to(Type::TEmpty)))
                .then_ignore(just(":").padded()),
        )
        .then(name().padded().repeated())
        .then(just("=").padded().ignore_then(parse_expr()))
        .map(|(((name, ty), args), value)| Def::Def { name, ty, args, value });

    let ty = just("type")
        .padded()
        .ignore_then(proper_name())
        .then(name().padded().repeated())
        .then(just("=").padded().ignore_then(parse_type()))
        .map(|((name, args), ty)| Def::Type { name, ty, args });

    choice((def, ty))
}

pub fn parse_type() -> impl Parser<char, Type, Error = Simple<char>> + Clone {
    recursive(|ty| {
        let term = choice((
            just("_").padded().to(Type::TEmpty),
            name().map(|var| Type::TVar(var)),
            proper_name()
                .then(ty.clone().padded().repeated())
                .padded()
                .map(|(name, args)| Type::TCustom(name, args)),
            ty.clone().delimited_by(just("("), just(")")).padded(),
        ));
        choice((
            term.clone()
                .then(just("->").padded().ignore_then(ty.clone()))
                .map(|(a, b)| Type::TFunction(Box::new(a), Box::new(b))),
            term,
        ))
    })
}

pub fn parse_expr() -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    let int = text::int(10)
        .padded()
        .map(|s: String| s.parse::<i64>().unwrap())
        .map(|s: i64| Expr::EInt(s));

    let op = |c| just(c).padded();

    recursive(|expr| {
        let term = choice((
            int,
            name().map(|n| Expr::Var(n)),
            expr.clone().delimited_by(just("("), just(")")).padded(),
        ));

        // Maybe a pipe function? :o
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

        let call = name()
            .then(expr.padded().repeated().at_least(1))
            .map(|(f, args)| Expr::Call(f, args));

        choice((call, sum))
    })
}

#[cfg(test)]
mod test {

    use super::*;
    use chumsky::Parser;

    macro_rules! expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let res = parse_expr().then_ignore(end()).parse(src);
                assert!(
                    res.is_ok(),
                    "ERR EXPR:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
                    src,
                    res
                );
            }
        };
    }

    macro_rules! no_expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let res = parse_expr().then_ignore(end()).parse(src);
                assert!(
                    res.is_err(),
                    "NO ERR EXPR:\n{:?}\ngave:\n{:?}\nbut expected ERROR\n-----------\n",
                    src,
                    res
                );
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

    // Probably controversial! This is a good idea, since now functions cannot be whatever they
    // want to be.
    expr_t!(call1, "a 1 2 3");
    expr_t!(call2, "a (1 + 2 + 3) (2 * 3) 3");
    expr_t!(call3, "f a + 1 b");

    no_expr_t!(il_ident1, "A");
    no_expr_t!(il_ident2, "Abcedef");
    no_expr_t!(il_call1, "(a + a) a b c");
    no_expr_t!(il_call2, "(f) a b c");
    no_expr_t!(il_call3, "1 + f a b");

    macro_rules! type_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let res = parse_type().then_ignore(end()).parse(src);
                assert!(
                    res.is_ok(),
                    "ERR TYPE:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
                    src,
                    res
                );
            }
        };
    }

    macro_rules! no_type_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let res = parse_type().then_ignore(end()).parse(src);
                assert!(
                    res.is_err(),
                    "ERR TYPE:\n{:?}\ngave:\n{:?}\nbut expected ERR\n-----------\n",
                    src,
                    res
                );
            }
        };
    }

    type_t!(t_int, "Int");
    type_t!(t_float, "Float");
    type_t!(t_string, "String");
    type_t!(t_custom, "Array Int");
    type_t!(t_custom_nested, "Array Float Int");
    type_t!(t_with_paren1, "A (B) C");
    type_t!(t_with_paren2, "A (B C)");
    type_t!(t_function, "A -> B -> C");
    type_t!(t_function_nested1, "A -> (B F -> D) -> C");
    type_t!(t_function_nested2, "A -> _");
    type_t!(t_function_nested3, "A -> (B _)");
    type_t!(t_function_nested4, "a -> b");
    type_t!(t_function_nested5, "A a B");

    no_type_t!(ill_paren, "(");

    macro_rules! def_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let res = parse_def().then_ignore(end()).parse(src);
                assert!(
                    res.is_ok(),
                    "ERR DEF:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
                    src,
                    res
                );
            }
        };
    }

    def_t!(d_var1, "def a : Int : = 1");
    def_t!(d_var2, "def a : Int : = 1 + 1");
    def_t!(d_fun1, "def a : Int -> Int : a = 1 + a");
    def_t!(d_fun2, "def a : Array a -> List a : a = a - a");
    def_t!(d_fun3, "def a : Array a -> List a : a b c d e f = 1");
    def_t!(
        d_fun4,
        "def a\n:    Array a   \n -> List a : \n a b \n c d e f \n = 1"
    );

    def_t!(d_ty1, "type Abc = Int");
    def_t!(d_ty2, "type Abc a = Int");
    def_t!(d_ty3, "type Abc a b c d e = Int");
}
