use quote::quote;
use syn::parse_macro_input;

mod bitfield;
mod log;
mod transparent;

#[proc_macro_derive(Bitfield, attributes(bitfield))]
pub fn derive_bitfield(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    parse_macro_input!(input with bitfield::derive_bitfield).into()
}

#[proc_macro_derive(Transparent)]
pub fn derive_transparent(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    parse_macro_input!(input with transparent::derive_transparent).into()
}

macro_rules! log_fn {
    ($name:ident, $level:ident) => {
        #[proc_macro]
        pub fn $name(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
            pub fn parse(input: syn::parse::ParseStream) -> syn::Result<proc_macro2::TokenStream> {
                log::log(stringify!($level), input)
            }
            parse_macro_input!(input with parse).into()
        }
    };
}

log_fn!(trace, Trace);
log_fn!(debug, Debug);
log_fn!(verbose, Verbose);
log_fn!(info, Info);

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
