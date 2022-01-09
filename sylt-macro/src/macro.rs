use quote::quote;
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
