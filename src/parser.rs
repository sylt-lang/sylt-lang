extern crate pom;
use pom::parser::*;

use crate::ast::*;

pub fn parser() -> impl Parser<char, Module, Error = Simple<Char>> {
}

