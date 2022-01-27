use quote::{quote, ToTokens};
use syn::parse_macro_input;

#[proc_macro_derive(Enumerate)]
pub fn derive_enumerate(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    assert!(!item.is_empty());
    let parsed: syn::ItemEnum = parse_macro_input!(item);

    let ident = parsed.ident;
    let match_from_usize: Vec<_> = parsed
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            quote! {
                #i => ::std::result::Result::Ok(#ident::#v),
            }
        })
        .collect();
    let match_from_ident: Vec<_> = parsed
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            quote! {
                #ident::#v => #i,
            }
        })
        .collect();

    let max = parsed.variants.len();

    let item = quote! {
        impl ::std::convert::TryFrom<usize> for #ident {
            type Error = ::std::string::String;

            fn try_from(u: usize) -> ::std::result::Result<Self, Self::Error> {
                match u {
                    #(#match_from_usize)*
                    u => ::std::result::Result::Err(format!("{} only has {} variants, tried {}", stringify!(#ident), #max, u)),
                }
            }
        }

        impl ::std::convert::From<#ident> for usize {
            fn from(s: #ident) -> Self {
                match s {
                    #(#match_from_ident)*
                }
            }
        }
    };
    proc_macro::TokenStream::from(item)
}

#[proc_macro_derive(Next)]
pub fn derive_next(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    assert!(!item.is_empty());
    let parsed: syn::ItemEnum = parse_macro_input!(item);

    let ident = parsed.ident.clone();

    let mut iter = parsed.variants.iter();
    let mut prev = iter.next().expect("Empty enum can't be Next");
    let mut match_arms: Vec<_> = iter
        .map(|v| {
            let tokens = quote! {
                #ident::#prev => #ident::#v,
            };
            prev = v;
            tokens
        })
        .collect();
    match_arms.push(quote! {
        #ident::#prev => #ident::#prev,
    });

    let item = quote! {
        impl Next for #ident {
            fn next(&self) -> Self {
                match self {
                    #(#match_arms)*
                }
            }
        }
    };
    proc_macro::TokenStream::from(item)
}

#[proc_macro_derive(Numbered)]
pub fn derive_numbered(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    assert!(!item.is_empty());
    let parsed: syn::ItemEnum = parse_macro_input!(item);

    let ident = parsed.ident.clone();

    let match_arms: Vec<_> = parsed
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let name = v.ident.clone();
            match v.fields {
                syn::Fields::Named(_) => {
                    quote! {
                        #ident::#name { .. } => #i,
                    }
                }
                syn::Fields::Unnamed(_) => {
                    quote! {
                        #ident::#name ( .. ) => #i,
                    }
                }
                syn::Fields::Unit => {
                    quote! {
                        #ident::#name => #i,
                    }
                }
            }
        })
        .collect();

    let item = quote! {
        impl Numbered for #ident {
            fn to_number(&self) -> usize {
                match self {
                    #(#match_arms)*
                }
            }
        }
    };
    proc_macro::TokenStream::from(item)
}

/// Timed macro
///
/// Time a function and print the output.
///
/// # Examples
///
/// ```
/// #[sylt_macro::timed]
/// fn hi() {
///     println!("Hi");
/// }
/// ```
/// will output `Time::hi = 123μ`
#[proc_macro_attribute]
pub fn timed(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let mut function = syn::parse::<syn::ItemFn>(item.clone()).expect("Could not parse function");

    // Get signature from attribute input or function signature
    let signature = if !attr.is_empty() {
        syn::parse::<syn::LitStr>(attr)
            .expect("Could not parse string")
            .value()
    } else {
        function.sig.ident.to_string()
    };

    let function_block = function.block;

    let new_function_block = quote! {
        {
            let __timer_start = std::time::SystemTime::now();

            let v = (move || {
                #function_block
            })();

            eprintln!("Time::{} = {:?}", #signature, __timer_start.elapsed().unwrap());

            return v;
        }
    };

    function.block = Box::new(syn::parse2(new_function_block).unwrap());

    function.into_token_stream().into()
}
