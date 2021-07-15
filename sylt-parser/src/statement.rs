use super::*;

/// The different kinds of [Statement]s.
///
/// There are both shorter statements like `a = b + 1` as well as longer
/// statements like `if a { ... } else { ...}`. The variants here include
/// examples of how they look in the code.
///
/// Note that this shouldn't be read as a formal language specification.
#[derive(Debug, Clone)]
pub enum StatementKind {
    /// "Imports" another file.
    ///
    /// `use <file>`.
    Use {
        file: Identifier,
    },

    /// Defines a new Blob.
    ///
    /// `A :: Blob { <field>.. }`.
    Blob {
        name: String,
        fields: HashMap<String, Type>,
    },

    /// Prints to standard out.
    ///
    /// `print <expression>`.
    Print {
        value: Expression,
    },

    /// Assigns to a variable (`a = <expression>`), optionally with an operator
    /// applied (`a += <expression>`)
    Assignment {
        kind: Op,
        target: Assignable,
        value: Expression,
    },

    /// Defines a new variable.
    ///
    /// Example: `a := <expression>`.
    ///
    /// Valid definition operators are `::`, `:=` and `: <type> =`.
    Definition {
        ident: Identifier,
        kind: VarKind,
        ty: Type,
        value: Expression,
    },

    /// Makes your code go either here or there.
    ///
    /// `if <expression> <statement> [else <statement>]`.
    If {
        condition: Expression,
        pass: Box<Statement>,
        fail: Box<Statement>,
    },

    /// Do something as long as something else evaluates to true.
    ///
    /// `loop <expression> <statement>`.
    Loop {
        condition: Expression,
        body: Box<Statement>,
    },

    /// Jump out of a loop.
    ///
    /// `break`.
    Break,

    /// Go back to the start of the loop.
    ///
    /// `continue`.
    Continue,

    /// Handles compile time checks of types.
    ///
    /// `:A is :B`
    IsCheck {
        lhs: Type,
        rhs: Type,
    },

    /// Returns a value from a function.
    ///
    /// `ret <expression>`.
    Ret {
        value: Expression,
    },

    /// Groups together statements that are executed after another.
    ///
    /// `{ <statement>.. }`.
    Block {
        statements: Vec<Statement>,
    },

    /// A free-standing expression. It's just a `<expression>`.
    StatementExpression {
        value: Expression,
    },

    /// Throws an error if it is ever evaluated.
    ///
    /// `<!>`.
    Unreachable,

    EmptyStatement,
}

/// What makes up a program. Contains any [StatementKind].
#[derive(Debug, Clone)]
pub struct Statement {
    pub span: Span,
    pub kind: StatementKind,
}

pub fn block_statement<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
    let span = ctx.span();
    let mut ctx = expect!(ctx, T::LeftBrace, "Expected '{{' at start of block");

    let mut errs = Vec::new();
    let mut statements = Vec::new();
    // Parse multiple inner statements until } or EOF
    while !matches!(ctx.token(), T::RightBrace | T::EOF) {
        match statement(ctx) {
            Ok((_ctx, stmt)) => {
                ctx = _ctx; // assign to outer
                statements.push(stmt);
            }
            Err((_ctx, mut err)) => {
                ctx = _ctx.pop_skip_newlines(false);  // assign to outer
                while !matches!(ctx.token(), T::Newline | T::EOF) {
                    ctx = ctx.skip(1);
                }
                ctx = ctx.skip_if(T::Newline);
                errs.append(&mut err);
            }
        }
    }

    let ctx = expect!(ctx, T::RightBrace, "Expected }} after block statement");
    if errs.is_empty() {
        #[rustfmt::skip]
        return Ok(( ctx, Statement { span, kind: StatementKind::Block { statements } }));
    } else {
        Err(( ctx, errs ))
    }
}

/// Parse a single [Statement].
pub fn statement<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
    use StatementKind::*;

    // Newlines have meaning in statements - thus they shouldn't be skipped.
    let (ctx, skip_newlines) = ctx.push_skip_newlines(false);

    let span = ctx.span();
    let (ctx, kind) = match &ctx.tokens[ctx.curr..] {
        [T::Newline, ..] => (ctx.skip(1), EmptyStatement),

        // Block: `{ <statements> }`
        [T::LeftBrace, ..] => match (block_statement(ctx), expression(ctx)) {
            (Ok((ctx, stmt)), _) => (ctx, stmt.kind),
            (_, Ok((ctx, value))) => (ctx, StatementExpression { value }),
            (Err((ctx, _)), Err(_)) => {
                raise_syntax_error!(ctx, "Neither a block nor a valid expression");
            }
        },

        // `use a`
        [T::Use, T::Identifier(name), ..] => (
            ctx.skip(2),
            Use {
                file: Identifier {
                    span: ctx.skip(1).span(),
                    name: name.clone(),
                },
            },
        ),

        // `: A is : B`
        [T::Colon, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, lhs) = parse_type(ctx)?;
            let ctx = expect!(ctx, T::Is, "Expected 'is' after first type in 'is-check' statement");
            let ctx = expect!(ctx, T::Colon, "Expected ':' - only type constant are allowed in 'is-check' statements");
            let (ctx, rhs) = parse_type(ctx)?;
            (ctx, IsCheck { lhs, rhs })
        }

        [T::Break, ..] => (ctx.skip(1), Break),
        [T::Continue, ..] => (ctx.skip(1), Continue),
        [T::Unreachable, ..] => (ctx.skip(1), Unreachable),

        [T::Print, ..] => {
            let (ctx, value) = expression(ctx.skip(1))?;
            (ctx, Print { value })
        }

        // `ret <expression>`
        [T::Ret, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, value) = if matches!(ctx.token(), T::Newline) {
                (
                    ctx,
                    Expression {
                        span: ctx.span(),
                        kind: ExpressionKind::Nil,
                    },
                )
            } else {
                expression(ctx)?
            };
            (ctx, Ret { value })
        }

        // `loop <expression> <statement>`, e.g. `loop a < 10 { a += 1 }`
        [T::Loop, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, condition) = if matches!(ctx.token(), T::LeftBrace) {
                (
                    ctx,
                    Expression { span: ctx.span(), kind: ExpressionKind::Bool(true), },
                )
            } else {
                expression(ctx)?
            };
            let (ctx, body) = statement(ctx)?;
            (
                ctx,
                Loop {
                    condition,
                    body: Box::new(body),
                },
            )
        }

        // `if <expression> <statement> [else <statement>]`. Note that the else is optional.
        [T::If, ..] => {
            let (ctx, skip_newlines) = ctx.push_skip_newlines(false);
            let (ctx, condition) = expression(ctx.skip(1))?;
            let ctx = ctx.pop_skip_newlines(skip_newlines);

            let (ctx, pass) = statement(ctx)?;
            // else?
            let (ctx, fail) = if matches!(ctx.token(), T::Else) {
                let (ctx, fail) = statement(ctx.skip(1))?;
                (ctx, fail)
            } else {
                // No else so we insert an empty statement instead.
                (
                    ctx,
                    Statement {
                        span: ctx.span(),
                        kind: EmptyStatement,
                    },
                )
            };

            (
                ctx,
                If {
                    condition,
                    pass: Box::new(pass),
                    fail: Box::new(fail),
                },
            )
        }

        // Blob declaration: `A :: blob { <fields> }
        [T::Identifier(name), T::ColonColon, T::Blob, ..] => {
            let name = name.clone();
            let ctx = expect!(ctx.skip(3), T::LeftBrace, "Expected '{{' to open blob");
            let (mut ctx, skip_newlines) = ctx.push_skip_newlines(true);

            let mut fields = HashMap::new();
            // Parse fields: `a: int`
            loop {
                match ctx.token().clone() {
                    T::Newline => {
                        ctx = ctx.skip(1);
                    }
                    // Done with fields.
                    T::RightBrace => {
                        break;
                    }

                    // Another one.
                    T::Identifier(field) => {
                        if fields.contains_key(&field) {
                            raise_syntax_error!(ctx, "Field '{}' is declared twice", field);
                        }
                        ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after field name");
                        let (_ctx, ty) = parse_type(ctx)?;
                        ctx = _ctx; // assign to outer
                        fields.insert(field, ty);

                        if !matches!(ctx.token(), T::Comma | T::RightBrace) {
                            raise_syntax_error!(ctx, "Expected a field deliminator ','");
                        }
                        ctx = ctx.skip_if(T::Comma);
                    }

                    _ => {
                        raise_syntax_error!(ctx, "Expected field name or '}}' in blob statement");
                    }
                }
            }

            let ctx = ctx.pop_skip_newlines(skip_newlines);
            let ctx = expect!(ctx, T::RightBrace, "Expected '}}' to close blob fields");
            (ctx, Blob { name, fields })
        }

        // Constant declaration, e.g. `a :: 1`.
        [T::Identifier(name), T::ColonColon, ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and `::`.
            let ctx = ctx.skip(2);

            // The value to assign.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind: VarKind::Const,
                    ty: Type {
                        span: ctx.span(),
                        kind: TypeKind::Implied,
                    },
                    value,
                },
            )
        }

        // Mutable declaration, e.g. `b := 2`.
        [T::Identifier(name), T::ColonEqual, ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and `:=`.
            let ctx = ctx.skip(2);

            // The value to assign.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind: VarKind::Mutable,
                    ty: Type {
                        span: ctx.span(),
                        kind: TypeKind::Implied,
                    },
                    value,
                },
            )
        }

        // Variable declaration with specified type, e.g. `c : int = 3` or `b : int | bool : false`.
        [T::Identifier(name), T::Colon, ..] => {
            let ident = Identifier {
                name: name.clone(),
                span: ctx.span(),
            };
            // Skip identifier and ':'.
            let ctx = ctx.skip(2);

            let (ctx, kind, ty) = {
                let forced = matches!(ctx.token(), T::Bang); // !int
                let ctx = ctx.skip_if(T::Bang);
                let (ctx, ty) = parse_type(ctx)?;
                let kind = match (ctx.token(), forced) {
                    (T::Colon, true) => VarKind::ForceConst,
                    (T::Equal, true) => VarKind::ForceMutable,
                    (T::Colon, false) => VarKind::Const,
                    (T::Equal, false) => VarKind::Mutable,
                    (t, _) => {
                        raise_syntax_error!(
                            ctx,
                            "Expected ':' or '=' for definition, but got '{:?}'",
                            t
                        );
                    }
                };
                // Skip `:` or `=`.
                (ctx.skip(1), kind, ty)
            };

            // The value to define the variable to.
            let (ctx, value) = expression(ctx)?;

            (
                ctx,
                Definition {
                    ident,
                    kind,
                    ty,
                    value,
                },
            )
        }

        // Expression or assignment. We try assignment first.
        _ => {
            /// `a = 5`.
            fn assignment<'t>(ctx: Context<'t>) -> ParseResult<'t, StatementKind> {
                // The assignable to assign to.
                let (ctx, target) = assignable(ctx)?;
                let kind = match ctx.token() {
                    T::PlusEqual => Op::Add,
                    T::MinusEqual => Op::Sub,
                    T::StarEqual => Op::Mul,
                    T::SlashEqual => Op::Div,
                    T::Equal => Op::Nop,

                    t => {
                        raise_syntax_error!(ctx, "No assignment operation matches '{:?}'", t);
                    }
                };
                // The expression to assign the assignable to.
                let (ctx, value) = expression(ctx.skip(1))?;
                Ok((
                    ctx,
                    Assignment {
                        kind,
                        target,
                        value,
                    },
                ))
            }

            match (assignment(ctx), expression(ctx)) {
                (Ok((ctx, kind)), _) => (ctx, kind),
                (_, Ok((ctx, value))) => (ctx, StatementExpression { value }),
                (Err((_, mut ass_errs)), Err((_, mut expr_errs))) => {
                    ass_errs.append(&mut expr_errs);
                    ass_errs.push(
                        syntax_error!(ctx, "Neither an assignment or a expression")
                    );
                    return Err((ctx, ass_errs));
                }
            }
        }
    };

    let ctx = ctx.skip_if(T::Newline);
    let ctx = ctx.pop_skip_newlines(skip_newlines);
    Ok((ctx, Statement { span, kind }))
}

/// Parse an outer statement.
///
/// Currently all statements are valid outer statements.
pub fn outer_statement<'t>(ctx: Context<'t>) -> ParseResult<Statement> {
    let (ctx, stmt) = statement(ctx)?;
    use StatementKind::*;
    match stmt.kind {
        #[rustfmt::skip]
        Blob { .. }
        | Definition { .. }
        | Use { .. }
        | IsCheck { .. }
        | EmptyStatement
        => Ok((ctx, stmt)),

        _ => raise_syntax_error!(ctx, "Not a valid outer statement"),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::StatementKind::*;

    // NOTE(ed): Expressions are valid statements! :D
    test!(statement, statement_expression: "1 + 1" => _);
    test!(statement, statement_print: "print 1" => _);
    test!(statement, statement_break: "break" => _);
    test!(statement, statement_continue: "continue" => _);
    test!(statement, statement_mut_declaration: "a := 1 + 1" => _);
    test!(statement, statement_const_declaration: "a :: 1 + 1" => _);
    test!(statement, statement_mut_type_declaration: "a :int= 1 + 1" => _);
    test!(statement, statement_const_type_declaration: "a :int: 1 + 1" => _);
    test!(statement, statement_force_mut_type_declaration: "a :!int= 1 + 1" => _);
    test!(statement, statement_force_const_type_declaration: "a :!int: 1 + 1" => _);
    test!(statement, statement_if: "if 1 { print a }" => _);
    test!(statement, statement_if_else: "if 1 { print a } else { print b }" => _);
    test!(statement, statement_loop: "loop 1 { print a }" => _);
    test!(statement, statement_loop_no_condition: "loop { print a }" => _);
    test!(statement, statement_ret: "ret 1 + 1" => _);
    test!(statement, statement_ret_newline: "ret \n" => _);
    test!(statement, statement_unreach: "<!>" => _);
    test!(statement, statement_blob_empty: "A :: blob {}" => _);
    test!(statement, statement_blob_comma: "A :: blob { a: int, b: int }" => _);
    test!(statement, statement_blob_comma_newline: "A :: blob { a: int,\n b: int }" => _);
    test!(statement, statement_assign: "a = 1" => _);
    test!(statement, statement_assign_index: "a.b = 1 + 2" => _);
    test!(statement, statement_add_assign: "a += 2" => _);
    test!(statement, statement_sub_assign: "a -= 2" => _);
    test!(statement, statement_mul_assign: "a *= 2" => _);
    test!(statement, statement_div_assign: "a /= 2" => _);
    test!(statement, statement_assign_call: "a().b() += 2" => _);
    test!(statement, statement_assign_call_index: "a.c().c.b /= 4" => _);
    test!(statement, statement_idek: "a'.c'.c.b()().c = 0" => _);

    test!(statement, statement_is_check: ":A is :B" => IsCheck { .. });
    test!(statement, statement_is_check_nested: ":A.c.d is :B.d.d" => IsCheck { .. });

    test!(statement, statement_if_newline: "if 1 \n\n+\n 1\n\n < 2 { }" => _);

    test!(statement, statement_skip_newline: "(1 \n\n+\n 1\n\n)" => _);
    test!(statement, statement_skip_newline_list: "[\n\n 1 \n\n,\n 1\n\n,]" => _);
    test!(statement, statement_skip_newline_set: "{\n\n 1 \n\n,\n 1\n\n,}" => _);
    test!(statement, statement_skip_newline_dict: "{\n\n 1: \n3\n,\n 1\n\n:1,}" => _);

    test!(outer_statement, outer_statement_blob: "B :: blob {}\n" => _);
    test!(outer_statement, outer_statement_blob_no_last_comma: "B :: blob { \na: A\n }\n" => _);
    test!(outer_statement, outer_statement_blob_yes_last_comma: "B :: blob { \na: A,\n }\n" => _);
    test!(outer_statement, outer_statement_declaration: "B :: fn -> {}\n" => _);
    test!(outer_statement, outer_statement_use: "use ABC\n" => _);
    test!(outer_statement, outer_statement_empty: "\n" => _);

    fail!(statement, statement_blob_newline: "A :: blob { a: int\n b: int }" => _);
}
