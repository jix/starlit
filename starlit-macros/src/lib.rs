use quote::quote;
use syn::{parse_macro_input, DeriveInput};

mod bitfield;
mod transparent;

#[proc_macro_derive(Bitfield, attributes(bitfield))]
pub fn derive_bitfield(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match bitfield::derive_bitfield(parse_macro_input!(input as DeriveInput)) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

#[proc_macro_derive(Transparent)]
pub fn derive_transparent(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match transparent::derive_transparent(parse_macro_input!(input as DeriveInput)) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn crate_path(name: &str) -> syn::Result<proc_macro2::TokenStream> {
    let found_crate = proc_macro_crate::crate_name(name)
        .map_err(|err| syn::Error::new(proc_macro2::Span::call_site(), err.to_string()))?;
    Ok(match found_crate {
        proc_macro_crate::FoundCrate::Itself => quote!(crate),
        proc_macro_crate::FoundCrate::Name(name) => {
            let ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
            quote!( ::#ident )
        }
    })
}
