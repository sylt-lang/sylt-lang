use lazy_static::lazy_static;
use proc_macro::TokenStream;
use quote::quote;
use std::borrow::Cow;
use syn::{Expr, Pat, Token, parse::{Parse, ParseStream, Result}, parse_macro_input};

struct ExternBlock {
    pattern: Pat,
    _arrow: Token![->],
    return_ty: Expr,
    _fat_arrow: Token![=>],
    block: Expr,
    _comma: Token![,],
}

struct ExternFunction {
    function: syn::Ident,
    blocks: Vec<ExternBlock>
}

impl Parse for ExternBlock {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            pattern: input.parse()?,
            _arrow: input.parse()?,
            return_ty: input.parse()?,
            _fat_arrow: input.parse()?,
            block: input.parse()?,
            _comma: input.parse()?,
        })
    }
}

impl Parse for ExternFunction {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut res = Self {
            function: input.parse()?,
            blocks: Vec::new(),
        };
        while !input.is_empty() {
            res.blocks.push(input.parse()?);
        }
        Ok(res)
    }
}

#[proc_macro]
pub fn extern_function(tokens: TokenStream) -> TokenStream {
    let parsed: ExternFunction = parse_macro_input!(tokens);
    let function = parsed.function;

    let typecheck_blocks: Vec<_> = parsed.blocks.iter().map(|block| {
        let pat = block.pattern.clone();
        let ty = block.return_ty.clone();
        quote! {
            #pat => { Ok(sylt::Value::from(#ty)) }
        }
    }).collect();

    let eval_blocks: Vec<_> = parsed.blocks.iter().map(|block| {
        let pat = block.pattern.clone();
        let expr = block.block.clone();
        quote! {
            #pat => #expr
        }
    }).collect();

    let tokens = quote! {
        pub fn #function (
            __values: &[sylt::Value],
            __typecheck: bool
        ) -> ::std::result::Result<sylt::Value, sylt::error::ErrorKind>
        {
            if __typecheck {
                #[allow(unused_variables)]
                match __values {
                    #(#typecheck_blocks),*
                    _ => Err(sylt::error::ErrorKind::ExternTypeMismatch(
                        stringify!(#function).to_string(),
                        __values.iter().map(|v| sylt::Type::from(v)).collect()
                    ))
                }
            } else {
                match __values {
                    #(#eval_blocks),*
                    _ => Err(sylt::error::ErrorKind::ExternTypeMismatch(
                        stringify!(#function).to_string(),
                        __values.iter().map(|v| sylt::Type::from(v)).collect()
                    ))
                }
            }
        }
    };
    TokenStream::from(tokens)
}

type RustFunction = fn(&[Value], bool) -> Result<Value, ErrorKind>;

lazy_static! {
    static ref LINKED_FUNCTIONS: Mutex<Vec<(String, )>>
}

#[proc_macro_attribute]
pub fn extern_link(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let parsed: syn::ItemFn = parse_macro_input!(tokens);

    let name = if attr.is_empty() {
        Cow::Borrowed(&parsed.sig.ident)
    } else {
        let attr: syn::Ident = parse_macro_input!(attr);
        Cow::Owned(attr)
    };

    let tokens = quote! {
        #parsed


    };
    TokenStream::from(tokens)
}
