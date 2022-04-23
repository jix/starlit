use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{DeriveInput, Path, Token};

use crate::crate_path;

pub fn derive_transparent(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = input.ident;

    let struct_data = match input.data {
        syn::Data::Enum(enum_data) => {
            return Err(syn::Error::new_spanned(
                enum_data.enum_token,
                "`Transparent` cannot be derived for enums, only structs",
            ));
        }
        syn::Data::Union(union_data) => {
            return Err(syn::Error::new_spanned(
                union_data.union_token,
                "`Transparent` cannot be derived for unions, only structs",
            ));
        }
        syn::Data::Struct(struct_data) => struct_data,
    };

    let mut is_transparent = false;

    for attr in &input.attrs {
        if attr.path.is_ident("repr") {
            is_transparent |= attr.parse_args_with(check_repr_args)?;
        }
    }

    if !is_transparent {
        return Err(syn::Error::new(
            Span::call_site(),
            format!(
                "{:?}",
                "deriving `Transparent` requires `#[repr(transparent)]`"
            ),
        ));
    }

    let mut fields = struct_data.fields.into_iter();

    let inner_type = if let Some(field) = fields.next() {
        field.ty.to_token_stream()
    } else {
        quote!(())
    };

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let starlit = crate_path("starlit")?;

    Ok(quote! {
        unsafe impl #impl_generics #starlit::util::transparent::Transparent for #name #ty_generics
        where
            #where_clause
        {

        }

        impl #impl_generics #starlit::util::transparent::ConvertStorage for #name #ty_generics
        where
            #where_clause
        {
            type Storage = #inner_type;

            #[inline(always)]
            fn into_storage(self) -> Self::Storage {
                unsafe { ::std::mem::transmute(self) }
            }

            #[inline(always)]
            unsafe fn from_storage_unchecked(storage: Self::Storage) -> Self {
                ::std::mem::transmute(storage)
            }
        }

    })
}

fn check_repr_args(input: syn::parse::ParseStream) -> syn::Result<bool> {
    let mut is_transparent = false;
    while !input.is_empty() {
        let path = input.call(Path::parse_mod_style)?;
        if path.is_ident("transparent") || path.is_ident("C") {
            is_transparent = true;
        } else {
            return Err(syn::Error::new_spanned(
                path,
                "unsupported repr for `Transparent` derive",
            ));
        }
        if !input.is_empty() {
            input.parse::<Token![,]>()?;
        }
    }

    Ok(is_transparent)
}
