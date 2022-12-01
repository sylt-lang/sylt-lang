#![allow(dead_code)]

use std::{iter::Peekable, mem::swap};

use crate::lexer::Token;

#[derive(Debug, Clone, Copy)]
pub struct Span(usize, usize);

#[derive(Debug, Clone)]
pub struct Name<'t> {
    str: &'t str,
    span: Span,
}

#[derive(Debug, Clone)]
pub struct ProperName<'t> {
    str: &'t str,
    span: Span,
}

#[derive(Debug, Clone)]
pub enum Def<'t> {
    Def {
        ty: Type<'t>,
        name: Name<'t>,
        args: Vec<Name<'t>>,
        value: Expr<'t>,
        span: Span,
    },
    Type {
        name: ProperName<'t>,
        args: Vec<Name<'t>>,
        ty: Type<'t>,
        span: Span,
    },
    Enum {
        name: ProperName<'t>,
        args: Vec<Name<'t>>,
        constructors: Vec<EnumConst<'t>>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct EnumConst<'t> {
    name: ProperName<'t>,
    ty: Type<'t>,
    span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr<'t> {
    EInt(i64, Span),
    Var(Name<'t>, Span),
    Call(Name<'t>, Vec<Expr<'t>>, Span),

    Un(UnOp, Box<Expr<'t>>),
    Bin(BinOp, Box<Expr<'t>>, Box<Expr<'t>>),
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Neg(Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add(Span),
    Sub(Span),
    Div(Span),
    Mul(Span),
    Call(Span),
}

#[derive(Debug, Clone)]
pub enum Type<'t> {
    TEmpty(Span),
    TCustom {
        name: ProperName<'t>,
        args: Vec<Type<'t>>,
        span: Span,
    },
    TVar(Name<'t>, Span),
    TFunction(Box<Type<'t>>, Box<Type<'t>>, Span),
}

#[derive(Clone, Debug)]
pub enum Error {
    Msg {
        msg: &'static str,
        span: Span,
        token: Option<String>,
        annotations: Vec<String>,
    },

    EoF {
        span: Span,
        annotations: Vec<String>,
    },
}
fn err_eof<'t, A>(span: Span) -> ParseResult<'t, A> {
    Err(Error::EoF { span, annotations: vec![] })
}

fn err_msg<'t, A>(msg: &'static str, span: Span) -> ParseResult<'t, A> {
    Err(Error::Msg { msg, span, token: None, annotations: vec![] })
}

fn err_msg_token<'t, A>(msg: &'static str, token: Option<Token<'t>>, span: Span) -> ParseResult<'t, A> {
    Err(Error::Msg { msg, span, token: token.map(|t| t.describe()), annotations: vec![] })
}


pub struct Lex<'t> {
    lexer: logos::Lexer<'t, Token<'t>>,
    buffer: (Span, Option<Token<'t>>),
}

impl<'t> Lex<'t> {
    pub fn new(lexer: logos::Lexer<'t, Token<'t>>) -> Self {
        let mut lexer = Self { lexer, buffer: (Span(0, 0), None) };
        lexer.feed();
        lexer
    }

    fn feed(&mut self) -> (Span, Option<Token<'t>>) {
        let t = self.lexer.next();
        let s = {
            let s = self.lexer.span();
            Span(s.start, s.end)
        };
        // TODOp[et]:
        let mut holder = (s, t);
        swap(&mut self.buffer, &mut holder);
        return holder;
    }

    pub fn span(&self) -> Span {
        return self.buffer.0;
    }

    pub fn peek(&self) -> &(Span, Option<Token<'t>>) {
        &self.buffer
    }

    pub fn next(&mut self) -> (Span, Option<Token<'t>>) {
        if self.buffer.1.is_none() {
            self.feed();
        }
        self.feed()
    }

    pub fn is_eof(&self) -> bool {
        self.buffer.1.is_none()
    }
}

pub type ParseResult<'t, A> = Result<A, Error>;


#[derive(PartialEq, PartialOrd, Clone, Copy, Debug)]
enum Prec {
    // Highest
    Factor,
    Term,
    Comp,
    BoolAnd,
    BoolOr,
    Call,

    No,
    // Lowest
}

fn next_prec(p: Prec) -> Prec {
    match p {
        Prec::Factor => Prec::Term,
        Prec::Term => Prec::Comp,
        Prec::Comp => Prec::BoolAnd,
        Prec::BoolAnd => Prec::BoolOr,
        Prec::BoolOr => Prec::Call,

        Prec::Call => Prec::No,

        Prec::No => Prec::No,
    }
}

fn op_to_prec(t: BinOp) -> Prec {
    match t {
        BinOp::Add(_) => Prec::Factor,
        BinOp::Sub(_) => Prec::Factor,

        BinOp::Mul(_) => Prec::Term,
        BinOp::Div(_) => Prec::Term,

        BinOp::Call(_) => Prec::Call,
    }
}

pub fn expr<'t>(lex: &mut Lex<'t>) -> ParseResult<'t, Expr<'t>> {
    parse_precedence(lex, Prec::No)
}

fn parse_precedence<'t>(lex: &mut Lex<'t>, prec: Prec) -> ParseResult<'t, Expr<'t>> {
    let mut lhs = prefix(lex)?;
    loop {
        dbg!(prec);
        match dbg!(peek_maybe_op(lex)) {
            Some(op) if op_to_prec(op) <= prec => {
                lex.next();
                let rhs = parse_precedence(lex, next_prec(op_to_prec(op)))?;
                lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs));
            }
            _ => {
                break Ok(lhs);
            }
        }
    }
}

fn peek_maybe_op<'t>(lex: &mut Lex<'t>) -> Option<BinOp> {
    let (span, token) = lex.peek();
    let out = match token {
        Some(Token::OpAdd) => BinOp::Add(*span),
        Some(Token::OpSub) => BinOp::Sub(*span),

        Some(Token::OpMul) => BinOp::Mul(*span),
        Some(Token::OpDiv) => BinOp::Div(*span),
        Some(Token::OpCall) => BinOp::Call(*span),

        _ => return None,
    };
    Some(out)
}

fn prefix<'t>(lex: &mut Lex<'t>) -> ParseResult<'t, Expr<'t>> {
    let (span, token) = lex.next();
    Ok(match token {
        None => return err_eof(span),
        Some(Token::OpNeg) => Expr::Un(UnOp::Neg(span), Box::new(prefix(lex)?)),
        Some(Token::Name(str)) => Expr::Var(Name { span, str }, span),
        Some(Token::Int(i)) => Expr::EInt(i.parse().expect("Error in Int regex!"), span),
        Some(Token::LParen) => {
            let expr = expr(lex)?;
            let (span_close, close) = lex.next();
            if let Some(Token::RParen) = close {
                expr
            } else {
                return err_msg_token("Expected a closing parenthasis here", close, span_close);
            }
        }
        t => return err_msg_token("Not a valid start of the expression", t, span),
    })
}

#[cfg(test)]
mod test {

    use super::*;
    use logos::Logos;

    macro_rules! expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let mut lex = Lex::new(Token::lexer($src));
                let res = expr(&mut lex);
                assert!(
                    res.is_ok(),
                    "ERR EXPR:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
                    src,
                    res
                );
                assert!(
                    lex.is_eof(),
                    "Didn't parse to end of expression! {:?} - {:?}\nGot: {:?}",
                    src,
                    lex.next(),
                    res,
                );
            }
        };
    }

    macro_rules! no_expr_t {
        ($name:ident, $src:literal) => {
            #[test]
            fn $name() {
                let src = $src;
                let mut lex = Lex::new(Token::lexer($src));
                let res = expr(&mut lex);
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

    // :O
    expr_t!(call1, "a ' 1 ' 2 ' 3");
    expr_t!(call2, "a ' (1 + 2 + 3) ' (2 * 3) ' 3");
    expr_t!(call3, "f ' a + 1 ' b");
    expr_t!(call4, "1 + f ' a ' b");

    no_expr_t!(il_ident1, "A");
    no_expr_t!(il_ident2, "Abcedef");

    //     macro_rules! type_t {
    //         ($name:ident, $src:literal) => {
    //             #[test]
    //             fn $name() {
    //                 let src = $src;
    //                 let res = parse_type().then_ignore(end()).parse(src);
    //                 assert!(
    //                     res.is_ok(),
    //                     "ERR TYPE:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
    //                     src,
    //                     res
    //                 );
    //             }
    //         };
    //     }
    //
    //     macro_rules! no_type_t {
    //         ($name:ident, $src:literal) => {
    //             #[test]
    //             fn $name() {
    //                 let src = $src;
    //                 let res = parse_type().then_ignore(end()).parse(src);
    //                 assert!(
    //                     res.is_err(),
    //                     "ERR TYPE:\n{:?}\ngave:\n{:?}\nbut expected ERR\n-----------\n",
    //                     src,
    //                     res
    //                 );
    //             }
    //         };
    //     }
    //
    //     type_t!(t_int, "Int");
    //     type_t!(t_float, "Float");
    //     type_t!(t_string, "String");
    //     type_t!(t_custom, "Array Int");
    //     type_t!(t_custom_nested, "Array Float Int");
    //     type_t!(t_with_paren1, "A (B) C");
    //     type_t!(t_with_paren2, "A (B C)");
    //     type_t!(t_function, "A -> B -> C");
    //     type_t!(t_function_nested1, "A -> (B F -> D) -> C");
    //     type_t!(t_function_nested2, "A -> _");
    //     type_t!(t_function_nested3, "A -> (B _)");
    //     type_t!(t_function_nested4, "a -> b");
    //     type_t!(t_function_nested5, "A a B");
    //
    //     no_type_t!(ill_paren, "(");
    //
    //     macro_rules! def_t {
    //         ($name:ident, $src:literal) => {
    //             #[test]
    //             fn $name() {
    //                 let src = $src;
    //                 let res = parse_def().then_ignore(end()).parse(src);
    //                 assert!(
    //                     res.is_ok(),
    //                     "ERR DEF:\n{:?}\ngave:\n{:?}\nbut expected OK\n-----------\n",
    //                     src,
    //                     res
    //                 );
    //             }
    //         };
    //     }
    //
    //     def_t!(d_var1, "def a : Int : = 1");
    //     def_t!(d_var2, "def a : Int : = 1 + 1");
    //     def_t!(d_fun1, "def a : Int -> Int : a = 1 + a");
    //     def_t!(d_fun2, "def a : Array a -> List a : a = a - a");
    //     def_t!(d_fun3, "def a : Array a -> List a : a b c d e f = 1");
    //     def_t!(
    //         d_fun4,
    //         "def a\n:    Array a   \n -> List a : \n a b \n c d e f \n = 1"
    //     );
    //
    //     def_t!(d_ty1, "type Abc = Int");
    //     def_t!(d_ty2, "type Abc a = Int");
    //     def_t!(d_ty3, "type Abc a b c d e = Int");
}
