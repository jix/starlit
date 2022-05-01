use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    Expr, ExprLit, Ident, Lit, LitStr, Token,
};

use crate::crate_path;

#[allow(clippy::large_enum_variant)]
enum LogArg {
    Message(String),
    Value(LogValueArg),
}

struct LogValueArg {
    name: Option<String>,
    expr: Expr,
}

impl LogArg {}

impl Parse for LogArg {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut name = None;

        let expr: Expr;

        if input.peek(Token![=]) {
            input.parse::<Token![=]>()?;
            expr = input.parse()?;

            name = Some(expr.to_token_stream().to_string())
        } else {
            if input.peek2(Token![=]) {
                if input.peek(Ident) {
                    name = Some(input.parse::<Ident>()?.to_string());
                    input.parse::<Token![=]>()?;
                } else if input.peek(LitStr) {
                    name = Some(input.parse::<LitStr>()?.value());
                    input.parse::<Token![=]>()?;
                }
            }

            expr = input.parse()?;
        }

        if let Expr::Lit(ExprLit {
            attrs,
            lit: Lit::Str(lit_str),
        }) = &expr
        {
            if attrs.is_empty() {
                return Ok(LogArg::Message(lit_str.value()));
            }
        }

        Ok(LogArg::Value(LogValueArg { name, expr }))
    }
}

#[allow(clippy::large_enum_variant)]
enum LogItem {
    Message(String),
    Value(Expr),
}

pub fn log_items(input: ParseStream) -> syn::Result<TokenStream> {
    let args = Punctuated::<LogArg, Token![,]>::parse_terminated(input)?;

    let mut items = vec![];
    for arg in args {
        match arg {
            LogArg::Message(msg) => items.push(LogItem::Message(msg)),
            LogArg::Value(LogValueArg { name, expr }) => {
                if let Some(mut name) = name {
                    name.push(':');
                    items.push(LogItem::Message(name));
                }
                items.push(LogItem::Value(expr));
            }
        }
    }

    let mut combined_items = vec![];

    for item in items {
        if let LogItem::Message(msg) = &item {
            if let Some(LogItem::Message(last_token)) = combined_items.last_mut() {
                last_token.push(' ');
                last_token.push_str(msg);
                continue;
            }
        }
        combined_items.push(item);
    }

    let mut steps = TokenStream::default();

    let target = Ident::new("target", Span::mixed_site());

    for item in combined_items {
        match item {
            LogItem::Message(msg) => steps.extend(quote! { #target.add_message(#msg); }),
            LogItem::Value(expr) => steps.extend(quote! { #target.add_value(&(#expr)); }),
        }
    }

    Ok(quote!(|#target| { #steps }))
}

pub fn log(level: &str, input: ParseStream) -> syn::Result<TokenStream> {
    let ctx: Ident = input.parse()?;
    input.parse::<Token![,]>()?;

    let items = log_items(input)?;

    let starlit = crate_path("starlit")?;
    let level = Ident::new(level, Span::call_site());
    Ok(quote! {{
        use #starlit::log::HasLogger;
        #ctx.logger().log(#starlit::log::LogLevel::#level, #items)
    }})
}
