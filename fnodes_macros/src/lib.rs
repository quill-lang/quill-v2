use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{
    parse::Parse, parse_macro_input, punctuated::Punctuated, spanned::Spanned, DeriveInput, Token,
};

enum FieldsType {
    Named,
    Unnamed,
    Unit,
}

enum SexprParsableType {
    Atomic,
    List,
    /// Like List, but doesn't wrap the result in another SexprNode.
    ListFlatten,
    Direct,
}

#[proc_macro_derive(
    ExprVariant,
    attributes(
        list_sexpr_keyword,
        atomic,
        list,
        direct,
        list_flatten,
        sub_expr,
        sub_expr_flatten,
        sub_exprs_flatten,
    )
)]
pub fn derive_expr_variant(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
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
            syn::Lit::Str(keyword) => Some(keyword),
            _ => panic!(
                "expected a string literal for the keyword in the `list_sexpr_keyword` attribute"
            ),
        },
        syn::Meta::Path(_) => None,
        _ => panic!(
            "expected either nothing or an `=` symbol then a string literal for the keyword in the `list_sexpr_keyword` attribute"
        ),
    };
    let keyword_value = if let Some(keyword) = keyword.clone() {
        quote!(Some(#keyword))
    } else {
        quote!(None)
    };

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
        .iter()
        .map(|field| {
            let ty = field
                .attrs
                .iter()
                .find_map(|a| {
                    if a.path.segments.len() == 1 {
                        match &*a.path.segments[0].ident.to_string() {
                            "atomic" => Some(SexprParsableType::Atomic),
                            "list" => Some(SexprParsableType::List),
                            "list_flatten" => Some(SexprParsableType::ListFlatten),
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

    let name = input.ident;

    let parse_list_fields = parse_list_fields(&fields);

    let parse_list_init = if fields
        .iter()
        .any(|(_, field_ty)| matches!(field_ty, SexprParsableType::ListFlatten))
    {
        quote!()
    } else {
        quote! {
            let [#parse_list_force_arity] = crate::force_arity(span, args)?;
        }
    };

    let mut serialise = TokenStream::new();
    for (i, (field, field_ty)) in fields.iter().enumerate() {
        let val = match &field.ident {
            Some(ident) => quote!(&self.#ident),
            None => {
                let i = syn::Index::from(i);
                quote!(&self.#i)
            }
        };
        match field_ty {
            SexprParsableType::Atomic => serialise.extend(quote! {
                result.push(crate::AtomicSexprWrapper::serialise_into_node(db, #val));
            }),
            SexprParsableType::List => serialise.extend(quote! {
                result.push(crate::ListSexprWrapper::serialise_into_node(db, #val));
            }),
            SexprParsableType::ListFlatten => serialise.extend(quote! {
                result.extend((#val).serialise(db));
            }),
            SexprParsableType::Direct => serialise.extend(quote! {
                result.push(crate::SexprSerialisable::serialise(#val, db));
            }),
        };
    }

    let mut output = TokenStream::new();

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

    output.extend(quote! {
        impl crate::ListSexpr for #name {
            const KEYWORD: Option<&'static str> = #keyword_value;

            fn parse_list(
                db: &dyn crate::SexprParser,
                span: ::fcommon::Span,
                args: Vec<crate::SexprNode>,
            ) -> Result<Self, crate::ParseError> {
                use crate::serialise::SexprParsable;
                #parse_list_init
                #parse_list_result
            }

            fn serialise(
                &self,
                db: &dyn crate::SexprParser,
            ) -> Vec<crate::SexprNode> {
                let mut result = Vec::new();
                #serialise;
                result
            }
        }
    });

    let mut sub_expressions = Punctuated::<TokenStream, Token![;]>::new();
    let mut sub_expressions_mut = Punctuated::<TokenStream, Token![;]>::new();

    // We can make sub_expressions functions.
    for (field_index, field) in data.fields.iter().enumerate() {
        let field_name = field
            .ident
            .as_ref()
            .map(|name| quote!(#name))
            .unwrap_or_else(|| {
                let field_index = syn::Index::from(field_index);
                quote!(#field_index)
            });

        if field
            .attrs
            .iter()
            .any(|attr| attr.path == Ident::new("sub_expr", Span::call_site()).into())
        {
            sub_expressions.push(quote! {
                result.push(&*self.#field_name);
            });
            sub_expressions_mut.push(quote! {
                result.push(&mut *self.#field_name);
            });
        } else if field
            .attrs
            .iter()
            .any(|attr| attr.path == Ident::new("sub_exprs_flatten", Span::call_site()).into())
        {
            sub_expressions.push(quote! {
                result.extend((&self.#field_name).iter().flat_map(|x| x.sub_expressions()));
            });
            sub_expressions_mut.push(quote! {
                result.extend((&mut self.#field_name).iter_mut().flat_map(|x| x.sub_expressions_mut()));
            });
        } else if field
            .attrs
            .iter()
            .any(|attr| attr.path == Ident::new("sub_expr_flatten", Span::call_site()).into())
        {
            sub_expressions.push(quote! {
                result.extend((&self.#field_name).sub_expressions());
            });
            sub_expressions_mut.push(quote! {
                result.extend((&mut self.#field_name).sub_expressions_mut());
            });
        }
    }

    output.extend(quote! {
        impl crate::expr::ExpressionVariant for #name {
            fn sub_expressions(&self) -> Vec<&Expr> {
                let mut result = Vec::new();
                #sub_expressions;
                result
            }

            fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
                let mut result = Vec::new();
                #sub_expressions_mut;
                result
            }
        }
    });

    // let result = output.into();
    // eprintln!("{}", result);
    // result

    output.into()
}

fn parse_list_fields(
    fields: &[(&syn::Field, SexprParsableType)],
) -> Punctuated<TokenStream, Token![,]> {
    let mut parse_list_fields = Punctuated::<TokenStream, Token![,]>::new();
    for (i, (field, ty)) in fields.iter().enumerate() {
        let start = match &field.ident {
            Some(ident) => quote! { #ident: },
            None => TokenStream::new(),
        };
        let v = Ident::new(&format!("v{}", i), Span::call_site());
        let field_ty = &field.ty;
        match ty {
            SexprParsableType::Atomic => parse_list_fields.push(quote! {
                #start crate::AtomicSexprWrapper::parse(db, #v)?
            }),
            SexprParsableType::List => parse_list_fields.push(quote! {
                #start crate::ListSexprWrapper::parse(db, #v)?
            }),
            SexprParsableType::ListFlatten => parse_list_fields.push(quote! {
                #start <_ as crate::ListSexpr>::parse_list(db, span, args)?
            }),
            SexprParsableType::Direct => parse_list_fields.push(quote! {
                #start #field_ty::parse(db, #v)?
            }),
        }
    }
    parse_list_fields
}

struct ExprVariants {
    expr_contents_name: Ident,
    variants: Punctuated<ExprVariant, Token![,]>,
}

impl Parse for ExprVariants {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let expr_contents_name = input.parse::<Ident>()?;
        input
            .parse_terminated(ExprVariant::parse)
            .map(|variants| ExprVariants {
                expr_contents_name,
                variants,
            })
    }
}

struct ExprVariant {
    nullary: bool,
    name: Ident,
}

impl Parse for ExprVariant {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let (name, nullary) = {
            let name = input.parse::<Ident>()?;
            if name == "nullary" {
                (input.parse::<Ident>()?, true)
            } else {
                (name, false)
            }
        };
        Ok(ExprVariant { nullary, name })
    }
}

#[proc_macro]
pub fn gen_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as ExprVariants);
    let expr_contents_name = input.expr_contents_name;

    let mut node_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        node_variants.push(if variant.nullary {
            quote!(#name)
        } else {
            quote!(#name(#name))
        });
    }

    let mut gen_from_impls = TokenStream::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        if variant.nullary {
            gen_from_impls.extend(quote!{
                impl TryFrom<#expr_contents_name> for #name {
                    type Error = &'static str;
                    fn try_from(value: #expr_contents_name) -> Result<Self, Self::Error> {
                        if let #expr_contents_name::#name = value { Ok(#name) } else { Err(value.variant_keyword()) }
                    }
                }

                impl From<#name> for #expr_contents_name {
                    fn from(value: #name) -> #expr_contents_name {
                        #expr_contents_name::#name
                    }
                }
            });
        } else {
            gen_from_impls.extend(quote!{
                impl TryFrom<#expr_contents_name> for #name {
                    type Error = &'static str;
                    fn try_from(value: #expr_contents_name) -> Result<Self, Self::Error> {
                        if let #expr_contents_name::#name(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
                    }
                }

                impl From<#name> for #expr_contents_name {
                    fn from(value: #name) -> #expr_contents_name {
                        #expr_contents_name::#name(value)
                    }
                }
            });
        }
    }

    let mut node_variant_keywords = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        if variant.nullary {
            node_variant_keywords.push(quote!(Self::#name => #name::KEYWORD.unwrap()));
        } else {
            node_variant_keywords.push(quote!(Self::#name(_) => #name::KEYWORD.unwrap()));
        }
    }

    let mut parse_expr_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        parse_expr_variants
            .push(quote!( #name::KEYWORD => #name::parse_list(db, span, args)?.into() ));
    }

    let mut serialise_expr_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        let (variant, serialise) = if variant.nullary {
            (quote!(Self::#name), quote!(#name.serialise(db)))
        } else {
            (quote!(Self::#name(val)), quote!(val.serialise(db)))
        };
        serialise_expr_variants.push(quote! {
            #variant => {
                let mut result = #serialise;
                result.insert(0, SexprNode {
                    contents: SexprNodeContents::Atom(#name::KEYWORD.unwrap().to_string()),
                    span: 0..0
                });
                result
            }
        });
    }

    let mut process_sub_expressions = Punctuated::<TokenStream, Token![,]>::new();
    let mut process_sub_expressions_mut = Punctuated::<TokenStream, Token![,]>::new();
    Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        if variant.nullary {
            process_sub_expressions.push(quote! {
                Self::#name => Vec::new()
            });
            process_sub_expressions_mut.push(quote! {
                Self::#name => Vec::new()
            });
        } else {
            process_sub_expressions.push(quote! {
                Self::#name(val) => val.sub_expressions()
            });
            process_sub_expressions_mut.push(quote! {
                Self::#name(val) => val.sub_expressions_mut()
            });
        };
    }

    let expr = quote! {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum #expr_contents_name {
            #node_variants
        }

        #gen_from_impls

        impl #expr_contents_name {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    #node_variant_keywords
                }
            }
        }

        impl ListSexpr for #expr_contents_name {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
                if args.is_empty() {
                    return Err(ParseError {
                        span,
                        reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                            expected: "<any expression>",
                        },
                    });
                }

                let first = args.remove(0);
                let keyword = if let SexprNodeContents::Atom(value) = &first.contents {
                    value.as_str()
                } else {
                    return Err(ParseError {
                        span: first.span.clone(),
                        reason: ParseErrorReason::ExpectedKeywordFoundList {
                            expected: "<any expression>",
                        },
                    });
                };

                // Reduce the span to only contain the arguments, not the keyword.
                let span = (first.span.end + 1)..span.end - 1;

                Ok(match Some(keyword) {
                    #parse_expr_variants,
                    _ => {
                        return Err(ParseError {
                            span: first.span.clone(),
                            reason: ParseErrorReason::WrongKeyword {
                                expected: "<any expression>",
                                found: keyword.to_string(),
                            },
                        })
                    }
                })
            }

            fn serialise(&self, db: &dyn SexprParser) -> Vec<SexprNode> {
                // TODO: expr infos
                match self {
                    #serialise_expr_variants
                }
            }
        }

        impl #expr_contents_name {
            pub fn sub_expressions(&self) -> Vec<&Expr> {
                match self {
                    #process_sub_expressions
                }
            }

            pub fn sub_expressions_mut(&mut self) -> Vec<&mut Expr> {
                match self {
                    #process_sub_expressions_mut
                }
            }
        }
    };

    // let result = expr.into();
    // eprintln!("{}", result);
    // result

    expr.into()
}
