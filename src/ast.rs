pub struct Module { name: Ident, body: Vec<Def> }

pub struct Ident<'a> { str: &'a str }

pub enum Def {
    Const { name: Ident, type: Type, value: Expr }
}

pub enum Expr {
    Int(i64),
}

pub enum Type {
    Int,
}


