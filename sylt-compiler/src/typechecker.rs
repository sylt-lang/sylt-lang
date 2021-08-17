#![allow(unused_imports)]
use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use sylt_common::error::Error;
use sylt_common::prog::Prog;
use sylt_common::{Blob, Block, Op, RustFunction, Type, Value};
use sylt_parser::{
    Assignable, AssignableKind, Expression, ExpressionKind, Identifier, Module, Op as ParserOp,
    Span, Statement, StatementKind, Type as ParserType, TypeKind, VarKind, AST,
};

use crate::Compiler;

macro_rules! error {
    ($compiler:expr, $ctx:expr, $span:expr, $( $msg:expr ),+ ) => {
        if !$compiler.panic {
            $compiler.panic = true;

            let msg = format!($( $msg ),*).into();
            let err = Error::CompileError {
                file: $compiler.file_from_namespace($ctx.namespace).into(),
                span: $span,
                message: Some(msg),
            };
            $compiler.errors.push(err);
        }
    };
}

struct TypeChecker {
}

impl TypeChecker {
    fn new() -> Self {
        Self {
        }
    }

    fn check(self, tree: &AST, compiler: &mut Compiler) -> Result<(), Vec<Error>> {
        Ok(())
    }
}

pub(crate) fn check(tree: &AST, compiler: &mut Compiler) -> Result<(), Vec<Error>> {
    TypeChecker::new().check(tree, compiler)
}

