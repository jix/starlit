use syn::{parse_macro_input, DeriveInput};

mod bitfield;

#[proc_macro_derive(Bitfield, attributes(bitfield))]
pub fn derive_bitfield(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match bitfield::derive_bitfield(parse_macro_input!(input as DeriveInput)) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}
