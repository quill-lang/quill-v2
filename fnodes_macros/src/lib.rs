use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::{parse_macro_input, punctuated::Punctuated, DeriveInput, Token};

enum FieldsType {
    Named,
    Unnamed,
    Unit,
}

enum SexprParsableType {
    Atomic,
    List,
    Direct,
}

enum GenericType {
    Expr,
}

#[proc_macro_derive(ListSexpr, attributes(list_sexpr_keyword, atomic, list, direct))]
pub fn derive_list_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let keyword = input
        .attrs
        .iter()
        .find(|a| a.path.segments.len() == 1 && a.path.segments[0].ident == "list_sexpr_keyword")
        .expect("`list_sexpr_keyword` attribute required for ListSexpr")
        .parse_meta()
        .unwrap();
    let keyword = match keyword {
        syn::Meta::NameValue(nv) => match nv.lit {
            syn::Lit::Str(keyword) => keyword,
            _ => panic!(
                "expected a string literal for the keyword in the `list_sexpr_keyword` attribute"
            ),
        },
        _ => panic!(
            "expected an `=` symbol then a string literal for the keyword in the `list_sexpr_keyword` attribute"
        ),
    };

    let generics = input
        .generics
        .params
        .iter()
        .map(|generic| match generic {
            syn::GenericParam::Type(ty) => match &*ty.ident.to_string() {
                "E" => GenericType::Expr,
                _ => panic!("generics must be named `E` for expression"),
            },
            _ => panic!("the only generics allowed when deriving `ListSexpr` are types"),
        })
        .collect::<Vec<_>>();

    let data = match input.data {
        syn::Data::Struct(data) => data,
        _ => panic!("this derive macro can only be used on structs"),
    };
    let fields_type = match data.fields {
        syn::Fields::Named(_) => FieldsType::Named,
        syn::Fields::Unnamed(_) => FieldsType::Unnamed,
        syn::Fields::Unit => FieldsType::Unit,
    };
    let fields = data
        .fields
        .into_iter()
        .map(|field| {
            let ty = field
                .attrs
                .iter()
                .find_map(|a| {
                    if a.path.segments.len() == 1 {
                        match &*a.path.segments[0].ident.to_string() {
                            "atomic" => Some(SexprParsableType::Atomic),
                            "list" => Some(SexprParsableType::List),
                            "direct" => Some(SexprParsableType::Direct),
                            _ => None,
                        }
                    } else {
                        None
                    }
                })
                .expect("`atomic`, `list`, or `direct` attribute required for all fields in `ListSexpr`");
            (field, ty)
        })
        .collect::<Vec<_>>();

    let mut parse_list_force_arity = Punctuated::<Ident, Token![,]>::new();
    for (i, _) in fields.iter().enumerate() {
        parse_list_force_arity.push(Ident::new(&format!("v{}", i), keyword.span()));
    }
    let mut parse_list_fields = Punctuated::<TokenStream, Token![,]>::new();
    for (i, (field, ty)) in fields.iter().enumerate() {
        let start = match &field.ident {
            Some(ident) => quote! { #ident: },
            None => TokenStream::new(),
        };
        let v = Ident::new(&format!("v{}", i), keyword.span());
        match ty {
            SexprParsableType::Atomic => parse_list_fields.push(quote! {
                #start crate::AtomicSexprWrapper::parse(ctx, db, #v)?
            }),
            SexprParsableType::List => parse_list_fields.push(quote! {
                #start crate::ListSexprWrapper::parse(ctx, db, #v)?
            }),
            SexprParsableType::Direct => todo!(),
        }
    }
    let parse_list_result = match fields_type {
        FieldsType::Named => {
            quote! {
                Ok(Self { #parse_list_fields })
            }
        }
        FieldsType::Unnamed => {
            quote! {
                Ok(Self ( #parse_list_fields ))
            }
        }
        FieldsType::Unit => quote! {
            Ok(Self)
        },
    };

    let name = input.ident;
    let serialise = TokenStream::new();

    let generics_options = if !generics.is_empty() {
        let node_generics = generics
            .iter()
            .map(|generic| match generic {
                GenericType::Expr => quote! { crate::expr3::Expr },
            })
            .collect::<Vec<_>>();
        let value_generics = generics
            .iter()
            .map(|generic| match generic {
                GenericType::Expr => quote! { crate::expr3::PartialValue },
            })
            .collect::<Vec<_>>();
        vec![node_generics, value_generics]
    } else {
        vec![Vec::new()]
    };

    let mut output = TokenStream::new();
    for generics_option in generics_options {
        let generic_arguments = if generics_option.is_empty() {
            TokenStream::new()
        } else {
            let mut args = Punctuated::<TokenStream, Token![,]>::new();
            for arg in generics_option {
                args.push(arg);
            }
            quote! { < #args > }
        };
        output.extend(quote! {
            impl crate::ListSexpr for #name #generic_arguments {
                const KEYWORD: Option<&'static str> = Some(#keyword);

                fn parse_list(
                    ctx: &mut crate::SexprParseContext,
                    db: &dyn crate::SexprParser,
                    span: ::fcommon::Span,
                    args: Vec<crate::SexprNode>,
                ) -> Result<Self, crate::ParseError> {
                    use crate::serialise::SexprParsable;
                    let [#parse_list_force_arity] = crate::force_arity(span, args)?;
                    #parse_list_result
                }

                fn serialise(
                    &self,
                    ctx: &crate::SexprSerialiseContext,
                    db: &dyn crate::SexprParser,
                ) -> Vec<crate::SexprNode> {
                    // Vec::new()
                    #serialise
                    todo!()
                }
            }
        });
    }

    output.into()
}
