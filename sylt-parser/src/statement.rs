use super::*;

/// The different ways a namespace is introduced by a use statement.
#[derive(Debug, Clone, PartialEq)]
pub enum NameIdentifier {
    /// When the identifier is implicit from the path. For example, `use a/b` introduces `b`.
    Implicit(Identifier),
    /// When the identifier is an alias. For example, `use a/b as c` introduces `c`.
    Alias(Identifier),
}

/// The different kinds of [Statement]s.
///
/// There are both shorter statements like `a = b + 1` as well as longer
/// statements like `if a { ... } else { ...}`. The variants here include
/// examples of how they look in the code.
///
/// Note that this shouldn't be read as a formal language specification.
#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    /// "Imports" another file.
    ///
    /// `use <file>`.
    /// `use /<file>`.
    /// `use <folder>/`.
    /// `use <folder>/<file>`.
    /// `use / as <alias>`.
    /// `use <file> as <alias>`.
    /// `use <folder>/ as <alias>`.
    Use {
        path: Identifier,
        name: NameIdentifier,
        file: PathBuf,
    },

    /// "Imports" variables from another file.
    ///
    /// `from <file> use <var1>, <var2>
    From {
        path: Identifier,
        names: Vec<NameIdentifier>,
        file: PathBuf,
    },

    /// Defines a new Blob.
    ///
    /// `A :: blob { <field>.. }`.
    Blob {
        name: String,
        fields: HashMap<String, Type>,
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

    /// Defines a an external variable - here the type is required.
    ///
    /// Example: `a: int = external`.
    ///
    /// Valid definition operators are `: <type> :`, and `: <type> =`.
    ExternalDefinition {
        ident: Identifier,
        kind: VarKind,
        ty: Type,
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
    pub comments: Vec<String>,
}

impl PartialEq for Statement {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

pub fn path<'t>(ctx: Context<'t>) -> ParseResult<'t, Identifier> {
    let span = ctx.span();
    let mut ctx = ctx;
    let mut result = String::new();
    expect!(
        ctx,
        T::Slash | T::Identifier(_),
        "Expected identifier or slash at start of use path"
    );
    if matches!(ctx.token(), T::Slash) {
        result.push_str("/");
        ctx = ctx.skip(1);
    }
    while let T::Identifier(f) = ctx.token() {
        result.push_str(f);
        ctx = ctx.skip(1);
        if matches!(ctx.token(), T::Slash) {
            result.push_str("/");
            ctx = ctx.skip(1);
        }
    }

    Ok((ctx, Identifier { span, name: result }))
}

pub fn block<'t>(ctx: Context<'t>) -> ParseResult<'t, Vec<Statement>> {
    // To allow implicit block-openings, like "fn ->"
    let mut ctx = ctx.skip_if(T::Do);

    let mut errs = Vec::new();
    let mut statements = Vec::new();
    // Parse multiple inner statements until } or EOF
    while !matches!(ctx.token(), T::Else | T::End | T::EOF) {
        match statement(ctx) {
            Ok((_ctx, stmt)) => {
                ctx = _ctx; // assign to outer
                statements.push(stmt);
            }
            Err((_ctx, mut err)) => {
                ctx = _ctx.pop_skip_newlines(false); // assign to outer
                ctx = skip_until!(ctx, T::Newline).skip_if(T::Newline);
                errs.append(&mut err);
            }
        }
    }

    if errs.is_empty() {
        // Special case for chaining if-else-statements
        if !matches!(ctx.token(), T::End | T::Else) {
            syntax_error!(ctx, "Expected 'end' after block");
        }
        let ctx = ctx.skip_if(T::End);
        #[rustfmt::skip]
        return Ok(( ctx, statements ));
    } else {
        Err((ctx, errs))
    }
}

/// Parse a single [Statement].
pub fn statement<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
    use StatementKind::*;

    // Newlines have meaning in statements - thus they shouldn't be skipped.
    let (ctx, skip_newlines) = ctx.push_skip_newlines(false);

    // Get all comments since the last statement.
    let mut comments = ctx.comments_since_last_statement();
    let ctx = ctx.push_last_statement_location();

    let span = ctx.span();
    //NOTE(gu): Explicit lookahead.
    let (ctx, kind) = match &ctx.tokens_lookahead::<3>() {
        [T::End, ..] => {
            raise_syntax_error!(ctx, "No valid statement starts with 'end'");
        }

        [T::Else, ..] => {
            raise_syntax_error!(ctx, "No valid statement starts with 'else'");
        }

        [T::Newline, ..] => (ctx, EmptyStatement),

        // Block: `{ <statements> }`
        [T::Do, ..] => match (block(ctx), expression(ctx)) {
            (Ok((ctx, statements)), _) => (ctx, Block { statements }),
            (_, Ok((ctx, value))) => (ctx, StatementExpression { value }),
            (Err((_, mut stmt_errs)), Err((_, mut expr_errs))) => {
                let errs = vec![
                    syntax_error!(ctx, "Neither a valid block nor a valid expression - inspects the two errors below"),
                    stmt_errs.remove(0),
                    expr_errs.remove(0),
                ];
                let ctx = skip_until!(ctx, T::End);
                return Err((ctx, errs));
            }
        },

        // `use path/to/file`
        // `use path/to/file as alias`
        [T::Use, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, path_ident) = path(ctx)?;
            let path = &path_ident.name;
            let name = path
                .trim_start_matches("/")
                .trim_end_matches("/")
                .to_string();
            let file = {
                let parent = if path.starts_with("/") {
                    ctx.root
                } else {
                    ctx.file.parent().unwrap()
                };
                // Importing a folder is the same as importing exports.sy
                // in the folder.
                parent.join(if path == "/" {
                    format!("exports.sy")
                } else if path_ident.name.ends_with("/") {
                    format!("{}/exports.sy", name)
                } else {
                    format!("{}.sy", name)
                })
            };
            let (ctx, alias) = match &ctx.tokens_lookahead::<2>() {
                [T::As, T::Identifier(alias), ..] => (
                    ctx.skip(2),
                    NameIdentifier::Alias(Identifier {
                        span: ctx.skip(1).span(),
                        name: alias.clone(),
                    }),
                ),
                [T::As, ..] => raise_syntax_error!(ctx.skip(1), "Expected alias"),
                [..] => {
                    if path == "/" {
                        raise_syntax_error!(ctx, "Using root requires alias");
                    }
                    let span = if path.ends_with("/") {
                        ctx.prev().prev().span()
                    } else {
                        ctx.prev().span()
                    };
                    let name = PathBuf::from(&name)
                        .file_stem()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_string();
                    (ctx, NameIdentifier::Implicit(Identifier { span, name }))
                }
            };
            (ctx, Use { path: path_ident, name: alias, file })
        }

        // `from path/to/file use var`
        [T::From, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, path_ident) = path(ctx)?;
            let path = &path_ident.name;
            let name = path
                .trim_start_matches("/")
                .trim_end_matches("/")
                .to_string();
            let file = {
                let parent = if path.starts_with("/") {
                    ctx.root
                } else {
                    ctx.file.parent().unwrap()
                };
                // Importing a folder is the same as importing exports.sy
                // in the folder.
                parent.join(if path == "/" {
                    format!("exports.sy")
                } else if path_ident.name.ends_with("/") {
                    format!("{}/exports.sy", name)
                } else {
                    format!("{}.sy", name)
                })
            };
            let ctx = expect!(ctx, T::Use, "Expected 'use' after path");
            let mut names = Vec::new();
            let ctx = match ctx.tokens_lookahead::<1>() {
                [T::Identifier(name)] => {
                    names.push(NameIdentifier::Implicit(Identifier {
                        name: name.clone(),
                        span: ctx.span(),
                    }));
                    ctx.skip(1)
                }
                _ => raise_syntax_error!(ctx, "Expected identifier"),
            };
            (ctx, From { path: path_ident, names, file })
        }

        // `: A is : B`
        [T::Colon, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, lhs) = parse_type(ctx)?;
            let ctx = expect!(
                ctx,
                T::Is,
                "Expected 'is' after first type in 'is-check' statement"
            );
            let ctx = expect!(
                ctx,
                T::Colon,
                "Expected ':' - only type constant are allowed in 'is-check' statements"
            );
            let (ctx, rhs) = parse_type(ctx)?;
            (ctx, IsCheck { lhs, rhs })
        }

        [T::Break, ..] => (ctx.skip(1), Break),
        [T::Continue, ..] => (ctx.skip(1), Continue),
        [T::Unreachable, ..] => (ctx.skip(1), Unreachable),

        // `ret <expression>`
        [T::Ret, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, value) = if matches!(ctx.token(), T::Newline) {
                (
                    ctx,
                    Expression { span: ctx.span(), kind: ExpressionKind::Nil },
                )
            } else {
                expression(ctx)?
            };
            (ctx, Ret { value })
        }

        // `loop <expression> <statement>`, e.g. `loop a < 10 { a += 1 }`
        [T::Loop, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, condition) = if matches!(ctx.token(), T::Do) {
                (
                    ctx,
                    Expression { span: ctx.span(), kind: ExpressionKind::Bool(true) },
                )
            } else {
                expression(ctx)?
            };
            let (ctx, body) = statement(ctx)?;
            (ctx.prev(), Loop { condition, body: Box::new(body) })
        }

        // `if <expression> <statement> [else <statement>]`. Note that the else is optional.
        [T::If, ..] => {
            let (ctx, skip_newlines) = ctx.push_skip_newlines(true);
            let (ctx, condition) = expression(ctx.skip(1))?;
            let ctx = ctx.pop_skip_newlines(skip_newlines);

            fn statement_or_block<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
                if matches!(
                    ctx.token(),
                    T::Do | T::If | T::Loop | T::Break | T::Continue | T::Ret
                ) {
                    Ok(statement(ctx)?)
                } else {
                    let err_ctx = skip_until!(ctx, T::End);
                    let err = syntax_error!(
                        ctx,
                        "Expected \"do\" or a statement keyword, but found {:?}",
                        ctx.token()
                    );
                    Err((err_ctx, vec![err]))
                }
            }

            let (ctx, pass) = statement_or_block(ctx)?;
            // else?
            let (ctx, fail) = if matches!(ctx.token(), T::Else) {
                statement_or_block(ctx.skip(1))?
            } else {
                // No else so we insert an empty statement instead.
                (
                    ctx,
                    Statement {
                        span: ctx.span(),
                        kind: EmptyStatement,
                        comments: Vec::new(),
                    },
                )
            };

            (
                ctx.prev(),
                If {
                    condition,
                    pass: Box::new(pass),
                    fail: Box::new(fail),
                },
            )
        }

        // Blob declaration: `A :: blob { <fields> }
        [T::Identifier(name), T::ColonColon, T::Blob, ..] => {
            if !is_capitalized(name) {
                raise_syntax_error!(
                    ctx,
                    "User defined types have to start with a capital letter"
                );
            }
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
                        if field == "self" {
                            raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
                        }
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

        // Implied type declaration, e.g. `a :: 1` or `a := 1`.
        [T::Identifier(name), T::ColonColon | T::ColonEqual, ..] => {
            if name == "self" {
                raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
            }
            let ident = Identifier { name: name.clone(), span: ctx.span() };
            let ctx = ctx.skip(1);
            let kind = match ctx.token() {
                T::ColonColon => VarKind::Const,
                T::ColonEqual => VarKind::Mutable,
                _ => unreachable!(),
            };
            let ctx = ctx.skip(1);

            if matches!(ctx.token(), T::External) {
                raise_syntax_error!(ctx, "External definitons have to have a type");
            } else {
                let (ctx, value) = expression(ctx)?;
                (
                    ctx,
                    Definition {
                        ident,
                        kind,
                        ty: Type { span: ctx.span(), kind: TypeKind::Implied },
                        value,
                    },
                )
            }
        }

        // Variable declaration with specified type, e.g. `c : int = 3` or `b : int | bool : false`.
        [T::Identifier(name), T::Colon, ..] => {
            if name == "self" {
                raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
            }
            let ident = Identifier { name: name.clone(), span: ctx.span() };
            // Skip identifier and ':'.
            let ctx = ctx.skip(2);

            let (ctx, kind, ty) = {
                let (ctx, ty) = parse_type(ctx)?;
                let kind = match ctx.token() {
                    T::Colon => VarKind::Const,
                    T::Equal => VarKind::Mutable,
                    t => {
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

            if matches!(ctx.token(), T::External) {
                (ctx.skip(1), ExternalDefinition { ident, kind, ty })
            } else {
                // The value to define the variable to.
                let (ctx, value) = expression(ctx)?;

                (ctx, Definition { ident, kind, ty, value })
            }
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
                Ok((ctx, Assignment { kind, target, value }))
            }

            match (assignment(ctx), expression(ctx)) {
                (Ok((ctx, kind)), _) => (ctx, kind),
                (_, Ok((ctx, value))) => (ctx, StatementExpression { value }),
                (Err((_, mut ass_errs)), Err((_, mut expr_errs))) => {
                    ass_errs.append(&mut expr_errs);
                    ass_errs.push(syntax_error!(ctx, "Neither an assignment or an expression"));
                    return Err((ctx, ass_errs));
                }
            }
        }
    };

    // Newline, RightBrace and Else can end a statment.
    // If a statement does not end, we only report it as a missing newline.
    let ctx = if matches!(ctx.token(), T::End | T::Else) {
        ctx
    } else {
        expect!(ctx, T::Newline, "Expected newline to end statement")
    };
    let ctx = ctx.pop_skip_newlines(skip_newlines);
    comments.append(&mut ctx.comments_since_last_statement());
    let ctx = ctx.push_last_statement_location();
    Ok((ctx, Statement { span, kind, comments }))
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
        | ExternalDefinition { .. }
        | Use { .. }
        | From { .. }
        | IsCheck { .. }
        | EmptyStatement
        => Ok((ctx, stmt)),

        _ => raise_syntax_error!(ctx, "Not a valid outer statement"),
    }
}

#[cfg(test)]
mod test {
    use super::StatementKind::*;
    use super::*;

    // NOTE(ed): Expressions are valid statements! :D
    test!(statement, statement_expression: "1 + 1\n" => _);
    test!(statement, statement_break: "break\n" => _);
    test!(statement, statement_continue: "continue\n" => _);
    test!(statement, statement_mut_declaration: "a := 1 + 1\n" => _);
    test!(statement, statement_const_declaration: "a :: 1 + 1\n" => _);
    test!(statement, statement_mut_type_declaration: "a :int= 1 + 1\n" => _);
    test!(statement, statement_const_type_declaration: "a :int: 1 + 1\n" => _);
    test!(statement, statement_if: "if 1 do a end\n" => _);
    test!(statement, statement_if_else: "if 1 do a else do b end\n" => _);
    test!(statement, statement_loop: "loop 1 { a }\n" => _);
    test!(statement, statement_loop_no_condition: "loop do a end\n" => _);
    test!(statement, statement_ret: "ret 1 + 1\n" => _);
    test!(statement, statement_ret_newline: "ret \n" => _);
    test!(statement, statement_unreach: "<!>\n" => _);
    test!(statement, statement_blob_empty: "A :: blob {}\n" => _);
    test!(statement, statement_blob_comma: "A :: blob { a: int, b: int }\n" => _);
    test!(statement, statement_blob_comma_newline: "A :: blob { a: int,\n b: int }\n" => _);
    test!(statement, statement_assign: "a = 1\n" => _);
    test!(statement, statement_assign_index: "a.b = 1 + 2\n" => _);
    test!(statement, statement_add_assign: "a += 2\n" => _);
    test!(statement, statement_sub_assign: "a -= 2\n" => _);
    test!(statement, statement_mul_assign: "a *= 2\n" => _);
    test!(statement, statement_div_assign: "a /= 2\n" => _);
    test!(statement, statement_assign_call: "a().b() += 2\n" => _);
    test!(statement, statement_assign_call_index: "a.c().c.b /= 4\n" => _);
    test!(statement, statement_idek: "a'.c'.c.b()().c = 0\n" => _);

    test!(statement, statement_is_check: ":A is :B\n" => IsCheck { .. });
    test!(statement, statement_is_check_nested: ":a.c.D is :b.d.D\n" => IsCheck { .. });

    test!(statement, statement_if_newline: "if 1 \n\n+\n 1\n\n < 2 do end\n" => _);

    test!(statement, statement_skip_newline: "(1 \n\n+\n 1\n\n)\n" => _);
    test!(statement, statement_skip_newline_list: "[\n\n 1 \n\n,\n 1\n\n,]\n" => _);
    test!(statement, statement_skip_newline_set: "{\n\n 1 \n\n,\n 1\n\n,}\n" => _);
    test!(statement, statement_skip_newline_dict: "{\n\n 1: \n3\n,\n 1\n\n:1,}\n" => _);

    test!(outer_statement, outer_statement_blob: "B :: blob {}\n" => _);
    test!(outer_statement, outer_statement_blob_no_last_comma: "B :: blob { \na: A\n }\n" => _);
    test!(outer_statement, outer_statement_blob_yes_last_comma: "B :: blob { \na: A,\n }\n" => _);
    test!(outer_statement, outer_statement_declaration: "B :: fn -> do end\n" => _);
    test!(outer_statement, outer_statement_use: "use abc\n" => _);
    test!(outer_statement, outer_statement_use_rename: "use a as b\n" => _);
    test!(outer_statement, outer_statement_use_subdir: "use a/b/c/d/e\n" => _);
    test!(outer_statement, outer_statement_use_subdir_rename: "use a/b as c\n" => _);
    test!(outer_statement, outer_statement_empty: "\n" => _);

    fail!(statement, statement_blob_newline: "A :: blob { a: int\n b: int }\n" => _);
    fail!(statement, statement_blob_self: "A :: blob { self: int }" => _);
    fail!(statement, statement_assign_self_const: "self :: 1" => _);
    fail!(statement, statement_assign_self_var: "self := 1" => _);
    fail!(statement, statement_assign_self_type: "self: int = 1" => _);
}

impl Display for NameIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ident = match &self {
            NameIdentifier::Implicit(ident) => {
                write!(f, "Implicit(")?;
                ident
            }
            NameIdentifier::Alias(ident) => {
                write!(f, "Alias(")?;
                ident
            }
        };
        write!(f, "{})", ident.name)
    }
}
