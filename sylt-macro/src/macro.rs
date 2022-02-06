use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse::Parser, parse_macro_input, punctuated::Punctuated, ExprPath, Token};

#[proc_macro_derive(Enumerate)]
pub fn derive_enumerate(item: TokenStream) -> TokenStream {
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
    TokenStream::from(item)
}

#[proc_macro_derive(Next)]
pub fn derive_next(item: TokenStream) -> TokenStream {
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
    TokenStream::from(item)
}

#[proc_macro_derive(Numbered)]
pub fn derive_numbered(item: TokenStream) -> TokenStream {
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
    TokenStream::from(item)
}

#[proc_macro]
pub fn timed_init(item: TokenStream) -> TokenStream {
    assert!(item.is_empty());

    TokenStream::from(quote! {
        #[doc(hidden)]
        #[derive(Debug)]
        pub struct __TimedState {
            t0: ::std::time::Instant,

            pub calls: ::std::vec::Vec<(
                // function identifier
                &'static ::std::primitive::str,
                // start
                ::std::time::Instant,
                // end
                ::std::time::Instant,
            )>,
        }

        #[doc(hidden)]
        pub(crate) struct __TimedHandle(&'static ::std::primitive::str, ::std::time::Instant);

        impl Drop for __TimedHandle {
            fn drop(&mut self) {
                let end = ::std::time::Instant::now();

                crate::__TIMED_STATE.with(|state| {
                    state.lock().unwrap().calls.push((
                        self.0.clone(),
                        self.1.clone(),
                        end,
                    ));
                });
            }
        }


        thread_local! {
            pub static __TIMED_STATE: ::std::sync::Mutex<(__TimedState)> =
                ::std::sync::Mutex::new(__TimedState {
                    t0: ::std::time::Instant::now(),
                    calls: ::std::vec::Vec::new(),
                }
            )
        }
    })
}

#[proc_macro]
pub fn timed_trace(item: TokenStream) -> TokenStream {
    let other_paths: Vec<ExprPath> = Punctuated::<ExprPath, Token![,]>::parse_terminated
        .parse(item)
        .unwrap()
        .iter()
        .cloned()
        .collect();

    TokenStream::from(quote! {
        {
            let (t0, mut calls) = crate::__TIMED_STATE.with(|state| {
                let state = state.lock().unwrap();
                (state.t0.clone(), state.calls.clone())
            });

            #(
                calls.extend(#other_paths::__TIMED_STATE.with(|state| {
                    state.lock().unwrap().calls.clone()
                }));
            )*

            let events = calls.iter().map(|call| {
                let (ident, start, end) = call;
                format!(
                    "{{\
                        \"name\": \"{}\", \
                        \"cat\": \"\", \
                        \"ph\": \"B\", \
                        \"ts\": {}, \
                        \"pid\": 1, \
                        \"tid\": 1, \
                        \"args\": {{}}\
                    }}\n,{{\
                        \"name\": \"{}\", \
                        \"cat\": \"\", \
                        \"ph\": \"E\", \
                        \"ts\": {}, \
                        \"pid\": 1, \
                        \"tid\": 1, \
                        \"args\": {{}}\
                    }}\n",
                    ident,
                    start.duration_since(t0).as_micros(),
                    ident,
                    end.duration_since(t0).as_micros(),
                )
            })
            .collect::<Vec<String>>()
            .join(",");
            format!("{{\"traceEvents\": [\n{}]}}", events)
        }
    })
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
pub fn timed(attr: TokenStream, item: TokenStream) -> TokenStream {
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
            let mut f = (move || {
                #function_block
            });

            // ensure timed state is initialized
            crate::__TIMED_STATE.with(|_| {});

            let start = ::std::time::Instant::now();
            let v = f();
            let end = ::std::time::Instant::now();

            crate::__TIMED_STATE.with(|state| {
                state.lock().unwrap().calls.push((
                    #signature,
                    start,
                    end,
                ));
            });

            return v;
        }
    };

    function.block = Box::new(syn::parse2(new_function_block).unwrap());

    function.into_token_stream().into()
}

#[proc_macro]
pub fn timed_handle(item: TokenStream) -> TokenStream {
    let signature = syn::parse::<syn::LitStr>(item)
        .expect("expected timing name")
        .value();
    TokenStream::from(quote! {
        crate::__TimedHandle(#signature, ::std::time::Instant::now())
    })
}

#[proc_macro]
pub fn timed_set_t0(item: TokenStream) -> TokenStream {
    assert!(item.is_empty());

    TokenStream::from(quote! {
        crate::__TIMED_STATE.with(|_| {})
    })
}
