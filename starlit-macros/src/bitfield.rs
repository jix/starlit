use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::{
    bracketed, parse::Parse, punctuated::Punctuated, spanned::Spanned, token, DeriveInput, LitInt,
    LitStr, Member, Token, Type, Visibility,
};

pub fn derive_bitfield(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = input.ident;

    let struct_data = match input.data {
        syn::Data::Enum(enum_data) => {
            return Err(syn::Error::new_spanned(
                enum_data.enum_token,
                "`Bitfield` cannot be derived for enums, only structs",
            ));
        }
        syn::Data::Union(union_data) => {
            return Err(syn::Error::new_spanned(
                union_data.union_token,
                "`Bitfield` cannot be derived for unions, only structs",
            ));
        }
        syn::Data::Struct(struct_data) => struct_data,
    };

    let mut output = TokenStream::new();
    let mut impls = TokenStream::new();

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    for (field_nr, field) in struct_data.fields.into_iter().enumerate() {
        let field_name = field
            .ident
            .clone()
            .map_or(Member::Unnamed(field_nr.into()), Member::Named);

        let field_type = field.ty;

        for attr in field
            .attrs
            .iter()
            .filter(|attr| attr.path.is_ident("bitfield"))
        {
            let bitfields: Bitfields = attr.parse_args()?;
            let bitfields_span = bitfields.span();

            let mut offset = 0u32;

            for bitfield in bitfields.0 {
                let bitfield_span = bitfield.span();
                let width: u32 = bitfield.bits.base10_parse()?;

                if !(1..128).contains(&width) {
                    return Err(syn::Error::new_spanned(
                        bitfield.bits,
                        "bitfield width must be in range 1..128",
                    ));
                }

                if let Some(BitfieldAccess {
                    vis,
                    name: getter_name,
                    ty,
                    ..
                }) = bitfield.access
                {
                    let (getter_docs, setter_docs) = if !bitfield.docs.is_empty() {
                        let comment_chunks: Vec<_> = bitfield
                            .docs
                            .iter()
                            .map(|doc| doc.comment.value())
                            .collect();
                        let comment = comment_chunks.join("\n");

                        let getter_comment = format!("Returns {}", comment);
                        let setter_comment = format!("Sets {}", comment);
                        (
                            quote!(#[doc = #getter_comment]),
                            quote!(#[doc = #setter_comment]),
                        )
                    } else {
                        (quote!(), quote!())
                    };

                    let setter_name = format_ident!("set_{}", getter_name);

                    let mask_value = (u128::MAX) >> (128 - width);
                    let mask = quote_spanned!(bitfield_span => (#mask_value as #field_type));

                    if width == 1 {
                        impls.extend(quote_spanned!(bitfield_span =>
                            #getter_docs
                            #vis fn #getter_name(&self) -> #ty {
                                #[allow(clippy::all)]
                                {
                                    (self.#field_name & (1 << #offset) != 0) as #ty
                                }
                            }
                        ));
                    } else {
                        impls.extend(quote_spanned!(bitfield_span =>
                            #getter_docs
                            #vis fn #getter_name(&self) -> #ty {
                                #[allow(clippy::all)]
                                {
                                    ((self.#field_name >> #offset) & #mask) as #ty
                                }
                            }
                        ));
                    }
                    if bitfield.clamp.is_some() {
                        impls.extend(quote_spanned!(bitfield_span =>
                            #setter_docs
                            #vis fn #setter_name(&mut self, value: #ty) {
                                #[allow(clippy::all)]
                                {
                                    let value = value.clamp(0, #mask_value as #ty);
                                    self.#field_name = self.#field_name & !(#mask << #offset)
                                        | ((value as #field_type) << #offset)
                                }
                            }
                        ));
                    } else {
                        impls.extend(quote_spanned!(bitfield_span =>
                            #setter_docs
                            #vis fn #setter_name(&mut self, value: #ty) {
                                #[allow(clippy::all)]
                                {
                                    self.#field_name = self.#field_name & !(#mask << #offset)
                                        | ((value as #field_type & #mask) << #offset)
                                }
                            }
                        ));
                    }
                }

                offset += width;
            }

            if offset > 0 {
                let check_offset = offset - 1;

                output.extend(quote_spanned!(bitfields_span =>
                    #[allow(clippy::all)]
                    const _: #field_type = (1 as #field_type) << #check_offset;
                ));
            }
        }
    }

    output.extend(quote!(
        impl #impl_generics #name #ty_generics #where_clause {
            #impls
        }
    ));

    Ok(output)
}

#[derive(Debug)]
struct Bitfields(Punctuated<Bitfield, Token![,]>);

impl Parse for Bitfields {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self(Punctuated::parse_terminated(input)?))
    }
}

impl ToTokens for Bitfields {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens(tokens);
    }
}

mod kw {
    syn::custom_keyword!(doc);
    syn::custom_keyword!(clamp);
}

#[derive(Debug)]
struct Bitfield {
    docs: Vec<DocComment>,
    bits: LitInt,
    clamp: Option<kw::clamp>,
    access: Option<BitfieldAccess>,
}

impl Parse for Bitfield {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            docs: DocComment::parse_multiline(input)?,
            bits: input.parse()?,
            clamp: input.parse()?,
            access: input
                .lookahead1()
                .peek(Token![=>])
                .then(|| input.parse())
                .transpose()?,
        })
    }
}

impl ToTokens for Bitfield {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for comment in &self.docs {
            comment.to_tokens(tokens);
        }
        self.bits.to_tokens(tokens);
        self.clamp.to_tokens(tokens);
        self.access.to_tokens(tokens);
    }
}

#[derive(Debug)]
struct DocComment {
    pound_token: Token![#],
    bracket_token: token::Bracket,
    doc_token: kw::doc,
    equal_token: Token![=],
    comment: LitStr,
}

impl DocComment {
    fn parse_multiline(input: syn::parse::ParseStream) -> syn::Result<Vec<Self>> {
        let mut out = vec![];

        while input.lookahead1().peek(Token![#]) {
            out.push(Self::parse(input)?)
        }

        Ok(out)
    }
}

impl Parse for DocComment {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        #[allow(clippy::eval_order_dependence)]
        Ok(Self {
            pound_token: input.parse()?,
            bracket_token: bracketed!(content in input),
            doc_token: content.parse()?,
            equal_token: content.parse()?,
            comment: content.parse()?,
        })
    }
}

impl ToTokens for DocComment {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.pound_token.to_tokens(tokens);
        self.bracket_token.surround(tokens, |tokens| {
            self.doc_token.to_tokens(tokens);
            self.equal_token.to_tokens(tokens);
            self.comment.to_tokens(tokens);
        });
    }
}

#[derive(Debug)]
struct BitfieldAccess {
    arrow_token: Token![=>],
    vis: Visibility,
    name: Ident,
    colon_token: Token![:],
    ty: Type,
}

impl Parse for BitfieldAccess {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            arrow_token: input.parse()?,
            vis: input.parse()?,
            name: input.parse()?,
            colon_token: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl ToTokens for BitfieldAccess {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.arrow_token.to_tokens(tokens);
        self.vis.to_tokens(tokens);
        self.name.to_tokens(tokens);
        self.colon_token.to_tokens(tokens);
        self.ty.to_tokens(tokens);
    }
}
