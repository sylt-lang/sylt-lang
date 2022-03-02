use super::*;

/// The different ways a namespace is introduced by a use statement.
#[derive(Debug, Clone, PartialEq)]
pub enum NameIdentifier {
    /// When the identifier is implicit from the path. For example, `use a/b` introduces `b`.
    Implicit(Identifier),
    /// When the identifier is an alias. For example, `use a/b as c` introduces `c`.
    Alias(Identifier),
}

impl NameIdentifier {
    pub fn name(&self) -> &str {
        &self.ident().name
    }

    pub fn span(&self) -> &Span {
        &self.ident().span
    }

    pub fn ident(&self) -> &Identifier {
        match self {
            NameIdentifier::Implicit(i) | NameIdentifier::Alias(i) => &i,
        }
    }
}

type Alias = Identifier;

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
        file: FileOrLib,
    },

    /// "Imports" variables from another file.
    ///
    /// `from <file> use <var1>`.
    /// `from <file> use <var1>, <var2>`.
    /// `from <file> use (<var1>, <var2>)`.
    /// `from <file> use <var1> as <alias>`.
    FromUse {
        path: Identifier,
        imports: Vec<(Identifier, Option<Alias>)>,
        file: FileOrLib,
    },

    /// Defines a new Blob.
    ///
    /// `A :: blob { <field>.. }`.
    Blob {
        name: Identifier,
        variables: Vec<Identifier>,
        fields: HashMap<Identifier, Type>,
    },

    /// Defines a new Enum.
    ///
    /// `A :: enum <variant>.. end`.
    Enum {
        name: Identifier,
        variables: Vec<Identifier>,
        variants: HashMap<Identifier, Type>,
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

    /// Returns a value from a function.
    ///
    /// `ret [<expression>]`.
    Ret {
        value: Option<Expression>,
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

    Ok((ctx, Identifier::new(span, result)))
}

pub fn use_path<'t>(ctx: Context<'t>) -> ParseResult<'t, (Identifier, FileOrLib)> {
    let (ctx, path_ident) = path(ctx)?;
    let path = &path_ident.name;
    let name = path
        .trim_start_matches("/")
        .trim_end_matches("/")
        .to_string();
    let file = {
        if let Some(name) = library_name(&name) {
            FileOrLib::Lib(name)
        } else {
            let file = if let FileOrLib::File(file) = ctx.file {
                file
            } else {
                raise_syntax_error!(ctx, "Cannot import files from the standard library");
            };
            let parent = if path.starts_with("/") {
                ctx.root
            } else {
                file.parent().unwrap()
            };
            // Importing a folder is the same as importing exports.sy
            // in the folder.
            FileOrLib::File(parent.join(if path == "/" {
                format!("exports.sy")
            } else if path_ident.name.ends_with("/") {
                format!("{}/exports.sy", name)
            } else {
                format!("{}.sy", name)
            }))
        }
    };

    Ok((ctx, (path_ident, file)))
}

pub fn statement_or_block<'t>(ctx: Context<'t>) -> ParseResult<'t, Statement> {
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

pub fn block<'t>(ctx: Context<'t>) -> ParseResult<'t, Vec<Statement>> {
    // To allow implicit block-openings, like "fn ->"
    let mut ctx = ctx.skip_if(T::Do);

    let mut errs = Vec::new();
    let mut statements = Vec::new();
    // Parse multiple inner statements until } or EOF
    while !matches!(ctx.token(), T::Else | T::Elif | T::End | T::EOF) {
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
        if !matches!(ctx.token(), T::End | T::Else | T::Elif) {
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
        [T::Do, ..] => {
            let (ctx, statements) = block(ctx)?;
            (ctx, Block { statements })
        }

        // `use path/to/file`
        // `use path/to/file as alias`
        [T::Use, ..] => {
            let (ctx, (path_ident, file)) = use_path(ctx.skip(1))?;
            let path = &path_ident.name;
            let (ctx, alias) = match &ctx.tokens_lookahead::<2>() {
                [T::As, T::Identifier(alias), ..] => (
                    ctx.skip(2),
                    NameIdentifier::Alias(Identifier::new(ctx.skip(1).span(), alias.clone())),
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
                    let name = PathBuf::from(
                        &path
                            .trim_start_matches("/")
                            .trim_end_matches("/")
                            .to_string(),
                    )
                    .file_stem()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                    (ctx, NameIdentifier::Implicit(Identifier::new(span, name)))
                }
            };
            (ctx, Use { path: path_ident, name: alias, file })
        }

        // `from path/to/file use var`
        [T::From, ..] => {
            let (ctx, (path_ident, file)) = use_path(ctx.skip(1))?;
            let mut ctx = expect!(ctx, T::Use, "Expected 'use' after path");
            let mut imports = Vec::new();

            let paren = matches!(ctx.token(), T::LeftParen);
            let (ctx_, skip_paren) = if paren {
                ctx = ctx.skip(1);
                ctx.push_skip_newlines(true)
            } else {
                ctx.push_skip_newlines(false)
            };
            ctx = ctx_;
            loop {
                match ctx.token() {
                    T::RightParen | T::Newline => break,
                    T::Identifier(name) => {
                        let ident = Identifier::new(ctx.span(), name.clone());
                        ctx = ctx.skip(1);
                        let alias = if matches!(ctx.token(), T::As) {
                            ctx = ctx.skip(1);
                            let _alias = match ctx.token() {
                                T::Identifier(name) => {
                                    Some(Identifier::new(ctx.span(), name.clone()))
                                }
                                _ => raise_syntax_error!(ctx, "Expected identifier after 'as'"),
                            };
                            ctx = ctx.skip(1);
                            _alias
                        } else {
                            None
                        };

                        imports.push((ident, alias));

                        if !matches!(ctx.token(), T::Comma | T::RightParen | T::Newline) {
                            raise_syntax_error!(ctx, "Expected ',' after import");
                        }
                        ctx = ctx.skip_if(T::Comma);
                    }
                    _ => raise_syntax_error!(ctx, "Expected identifier"),
                };
            }
            if imports.is_empty() {
                raise_syntax_error!(ctx, "Something has to be imported in an import statement");
            }
            let ctx = ctx.pop_skip_newlines(skip_paren);
            let ctx = if paren {
                expect!(ctx, T::RightParen, "Expected ')' after import list")
            } else {
                ctx
            };
            (ctx, FromUse { path: path_ident, imports, file })
        }

        [T::Break, ..] => (ctx.skip(1), Break),
        [T::Continue, ..] => (ctx.skip(1), Continue),
        [T::Unreachable, ..] => (ctx.skip(1), Unreachable),

        // `ret [<expression>]`
        [T::Ret, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, value) = match expression(ctx) {
                Ok((ctx, value)) => (ctx, Some(value)),
                Err(_) => (ctx, None),
            };
            (ctx, Ret { value })
        }

        // `loop <expression> <statement>`, e.g. `loop a < 10 { a += 1 }`
        [T::Loop, ..] => {
            let ctx = ctx.skip(1);
            let (ctx, condition) = if matches!(ctx.token(), T::Do) {
                (ctx, Expression::new(ctx.span(), ExpressionKind::Bool(true)))
            } else {
                expression(ctx)?
            };
            let (ctx, body) = statement(ctx)?;
            (ctx.prev(), Loop { condition, body: Box::new(body) })
        }

        // Enum declaration: `Abc :: enum A, B, C end`
        [T::Identifier(enum_name), T::ColonColon, T::Enum, ..] => {
            if !is_capitalized(enum_name) {
                raise_syntax_error!(
                    ctx,
                    "User defined types have to start with a capital letter"
                );
            }
            let enum_name = Identifier::new(ctx.span(), enum_name.clone());
            let ctx = ctx.skip(3);
            let (ctx, skip_newlines) = ctx.push_skip_newlines(false);
            // Parse variables: `enum(*A)`
            fn item<'t>(ctx: Context<'t>) -> ParseResult<'t, Identifier> {
                let ctx = expect!(ctx, T::Star, "Type variables have to start with '*'");
                match ctx.eat() {
                    (T::Identifier(variant), span, ctx) => {
                        Ok((ctx, Identifier::new(span, variant.clone())))
                    }
                    _ => raise_syntax_error!(
                        ctx,
                        "Expected an identifier after '*' in type parameter"
                    ),
                }
            }

            let (ctx, variables) =
                parse_beg_end_comma_sep!(ctx, T::LeftParen, T::RightParen, &item)?;

            // Parse variants: `A(..), B(..)`
            let (ctx, items) = {
                fn sep<'t>(ctx: Context<'t>) -> ParseResult<'t, ()> {
                    let ctx = skip_while!(ctx, T::Newline);
                    let ctx = ctx.skip_if(T::Comma);
                    Ok((ctx, ()))
                }
                fn end<'t>(ctx: Context<'t>) -> ParseResult<'t, bool> {
                    let ctx = skip_while!(ctx, T::Newline);
                    match ctx.token() {
                        // Done with variants.
                        T::End => Ok((ctx.skip(1), true)),
                        _ => Ok((ctx, false)),
                    }
                }

                fn item<'t>(ctx: Context<'t>) -> ParseResult<'t, (Identifier, Type)> {
                    let ctx = skip_while!(ctx, T::Newline);
                    let (ctx, variant) = match ctx.eat() {
                        (T::Identifier(variant), span, ctx) => {
                            (ctx, Identifier::new(span, variant.clone()))
                        }
                        _ => raise_syntax_error!(
                            ctx,
                            "An enum variant has to start with a valid identifier"
                        ),
                    };
                    if !is_capitalized(&variant.name) {
                        raise_syntax_error!(
                            ctx,
                            "Enum variants have to start with a capital letter"
                        );
                    }
                    let (ctx, ty) = if matches!(ctx.token(), T::End | T::Comma | T::Newline) {
                        let ty = Type {
                            span: variant.span,
                            kind: TypeKind::Resolved(RuntimeType::Nil),
                        };
                        (ctx, ty)
                    } else {
                        let ctx = ctx.skip_if(T::Colon);
                        let (ctx, ty) = parse_type(ctx)?;
                        if !matches!(ctx.token(), T::Comma | T::End | T::Newline) {
                            raise_syntax_error!(ctx, "Expected a delimiter ','");
                        };
                        (ctx, ty)
                    };
                    Ok((ctx.skip_if(T::Comma), (variant, ty)))
                }
                parse_sep_end_by(ctx, sep, end, item)?
            };

            let mut variants = HashMap::new();
            for (variant, ty) in items {
                if variants.contains_key(&variant) {
                    let file = ctx.file.clone();
                    let span = variant.span;
                    let message = format!(
                        "The variant '{}' occures twice in the enum '{}'",
                        variant.name, enum_name.name
                    );
                    return Err((ctx, vec![Error::SyntaxError { file, span, message }]));
                }
                variants.insert(variant, ty);
            }

            let ctx = ctx.pop_skip_newlines(skip_newlines);
            (ctx, Enum { name: enum_name, variants, variables })
        }

        // Blob declaration: `A :: blob { <fields> }
        [T::Identifier(name), T::ColonColon, T::Blob, ..] => {
            if !is_capitalized(name) {
                raise_syntax_error!(
                    ctx,
                    "User defined types have to start with a capital letter"
                );
            }
            let name = Identifier::new(ctx.span(), name.clone());

            // Parse variables: `blob(*A)`
            fn item<'t>(ctx: Context<'t>) -> ParseResult<'t, Identifier> {
                let ctx = expect!(ctx, T::Star, "Type variables have to start with '*'");
                match ctx.eat() {
                    (T::Identifier(variant), span, ctx) => {
                        Ok((ctx, Identifier::new(span, variant.clone())))
                    }
                    _ => raise_syntax_error!(
                        ctx,
                        "Expected an identifier after '*' in type parameter"
                    ),
                }
            }

            let (ctx, variables) =
                parse_beg_end_comma_sep!(ctx.skip(3), T::LeftParen, T::RightParen, &item)?;

            let ctx = expect!(ctx, T::LeftBrace, "Expected '{{' to open blob");
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
                        let field = Identifier::new(ctx.span(), field.clone());
                        if field.name == "self" {
                            raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
                        }
                        if fields.contains_key(&field) {
                            raise_syntax_error!(ctx, "Field '{}' is declared twice", field.name);
                        }
                        ctx = expect!(ctx.skip(1), T::Colon, "Expected ':' after field name");
                        let (_ctx, ty) = parse_type(ctx)?;
                        ctx = _ctx; // assign to outer
                        fields.insert(field, ty);

                        if !matches!(ctx.token(), T::Comma | T::RightBrace) {
                            raise_syntax_error!(ctx, "Expected a field delimiter ','");
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
            (ctx, Blob { name, fields, variables })
        }

        // Implied type declaration, e.g. `a :: 1` or `a := 1`.
        [T::Identifier(name), T::ColonColon | T::ColonEqual, ..] => {
            if is_capitalized(name) {
                // raise_syntax_error!(ctx, "Variables have to start with a lowercase letter");
            }
            if name == "self" {
                raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
            }
            let ident = Identifier::new(ctx.span(), name.clone());
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
            if is_capitalized(name) {
                // raise_syntax_error!(ctx, "Variables have to start with a lowercase letter");
            }
            if name == "self" {
                raise_syntax_error!(ctx, "\"self\" is a reserved identifier");
            }
            let ident = Identifier::new(ctx.span(), name.clone());
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

        // Expression or assignment. We probe to find out which.
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

            // Probe if we should parse an assignable here.
            // If not, we parse an expression.
            let is_assignment = match assignable(ctx) {
                Ok((ctx, _)) => matches!(
                    ctx.token(),
                    T::PlusEqual | T::MinusEqual | T::StarEqual | T::SlashEqual | T::Equal
                ),
                _ => false,
            };

            if is_assignment {
                assignment(ctx)?
            } else {
                let (ctx, value) = expression(ctx)?;
                (ctx, StatementExpression { value })
            }
        }
    };

    // Newline, RightBrace and Else can end a statment.
    // If a statement does not end, we only report it as a missing newline.
    let ctx = if matches!(ctx.token(), T::End | T::Else | T::Elif) {
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
        | Enum { .. }
        | Definition { .. }
        | ExternalDefinition { .. }
        | Use { .. }
        | FromUse { .. }
        | EmptyStatement
        => Ok((ctx, stmt)),

        _ => raise_syntax_error!(ctx, "Not a valid outer statement"),
    }
}

#[cfg(test)]
mod test {
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
    test!(outer_statement, outer_statement_from: "from a/b use c\n" => _);
    test!(outer_statement, outer_statement_from_many: "from b use c,d,e,f,g,h\n" => _);
    test!(outer_statement, outer_statement_from_paren: "from / use (c\n,d\n)\n" => _);
    test!(outer_statement, outer_statement_from_paren_one: "from / use (c)\n" => _);
    test!(outer_statement, outer_statement_empty: "\n" => _);

    test!(outer_statement, outer_statement_enum: "A :: enum A, B end\n" => _);
    test!(outer_statement, outer_statement_enum_trailing_comma: "A :: enum A, B, end\n" => _);
    test!(outer_statement, outer_statement_enum_empty: "A :: enum end\n" => _);
    test!(outer_statement, outer_statement_enum_tuples: "A :: enum A(int, int), B(int,), C(), end\n" => _);
    test!(outer_statement, outer_statement_enum_newlines: "A :: enum A(int, int)\n\n B(int,)\n C()\n end\n" => _);

    fail!(statement, statement_blob_newline: "A :: blob { a: int\n b: int }\n" => _);
    fail!(statement, statement_blob_self: "A :: blob { self: int }" => _);
    fail!(statement, statement_assign_self_const: "self :: 1" => _);
    fail!(statement, statement_assign_self_var: "self := 1" => _);
    fail!(statement, statement_assign_self_type: "self: int = 1" => _);
    fail!(statement, outer_statement_from_invalid: "from b use a!" => _);
    fail!(statement, outer_statement_from_alias_invalid: "from b use a as !" => _);
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
