use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{
    parse::Parse, parse_macro_input, punctuated::Punctuated, spanned::Spanned, DeriveInput,
    Generics, Token,
};

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
    Name,
    QualifiedName,
    Component,
}

fn convert_generics(generics: &Generics) -> Vec<GenericType> {
    generics
        .params
        .iter()
        .map(|generic| match generic {
            syn::GenericParam::Type(ty) => match &*ty.ident.to_string() {
                "E" => GenericType::Expr,
                "N" => GenericType::Name,
                "Q" => GenericType::QualifiedName,
                "C" => GenericType::Component,
                _ => panic!(
                    "generics must be named `E`, `N`, `Q`, or `C`, for expression, name, qualified name, or component"
                ),
            },
            _ => panic!("the only generics allowed when deriving `ListSexpr` are types"),
        })
        .collect()
}

fn write_node_generic(generic: &GenericType) -> TokenStream {
    match generic {
        GenericType::Expr => quote! { crate::expr::Expr },
        GenericType::Name => quote! { crate::expr::Name },
        GenericType::QualifiedName => quote! { crate::expr::QualifiedName },
        GenericType::Component => {
            quote! { crate::expr::Component<crate::expr::Name, crate::expr::Expr> }
        }
    }
}

fn write_node_generics(generics: &[GenericType]) -> Punctuated<TokenStream, Token![,]> {
    generics.iter().map(write_node_generic).collect()
}

fn write_value_generic(generic: &GenericType) -> TokenStream {
    match generic {
        GenericType::Expr => quote! { crate::expr::PartialValue },
        GenericType::Name => quote! { crate::expr::Str },
        GenericType::QualifiedName => quote! { ::fcommon::Path },
        GenericType::Component => {
            quote! { crate::expr::ComponentContents<crate::expr::Str, crate::expr::PartialValue> }
        }
    }
}

fn write_value_generics(generics: &[GenericType]) -> Punctuated<TokenStream, Token![,]> {
    generics.iter().map(write_value_generic).collect()
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

    let generics = convert_generics(&input.generics);

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

    let name = input.ident;
    let serialise = TokenStream::new();

    let generics_options = if !generics.is_empty() {
        let node_generics = write_node_generics(&generics);
        let value_generics = write_value_generics(&generics);

        let node_parse_list_fields = parse_list_fields(&fields, keyword.clone(), true);
        let value_parse_list_fields = parse_list_fields(&fields, keyword, false);

        vec![
            (node_generics, node_parse_list_fields),
            (value_generics, value_parse_list_fields),
        ]
    } else {
        let parse_list_fields = parse_list_fields(&fields, keyword, false);
        vec![(Punctuated::new(), parse_list_fields)]
    };

    let mut output = TokenStream::new();
    for (generics_option, parse_list_fields) in generics_options {
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
                const KEYWORD: Option<&'static str> = #keyword_value;

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

fn parse_list_fields(
    fields: &[(syn::Field, SexprParsableType)],
    keyword: Option<syn::LitStr>,
    use_node_generics: bool,
) -> Punctuated<TokenStream, Token![,]> {
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
            SexprParsableType::Direct => {
                let direct_ty = match &field.ty {
                    syn::Type::Path(path) => {
                        if path.path == Ident::new("E", Span::call_site()).into() {
                            Box::new(if use_node_generics {
                                write_node_generic(&GenericType::Expr)
                            } else {
                                write_value_generic(&GenericType::Expr)
                            }) as Box<dyn quote::ToTokens>
                        } else if path.path == Ident::new("N", Span::call_site()).into() {
                            Box::new(if use_node_generics {
                                write_node_generic(&GenericType::Name)
                            } else {
                                write_value_generic(&GenericType::Name)
                            }) as Box<dyn quote::ToTokens>
                        } else if path.path == Ident::new("Q", Span::call_site()).into() {
                            Box::new(if use_node_generics {
                                write_node_generic(&GenericType::QualifiedName)
                            } else {
                                write_value_generic(&GenericType::QualifiedName)
                            }) as Box<dyn quote::ToTokens>
                        } else if path.path == Ident::new("C", Span::call_site()).into() {
                            Box::new(if use_node_generics {
                                write_node_generic(&GenericType::Component)
                            } else {
                                write_value_generic(&GenericType::Component)
                            }) as Box<dyn quote::ToTokens>
                        } else {
                            Box::new(field.ty.clone())
                        }
                    }
                    other => Box::new(other.clone()),
                };
                parse_list_fields.push(quote! {
                    #start #direct_ty::parse(ctx, db, #v)?
                })
            }
        }
    }
    parse_list_fields
}

struct ExprVariants {
    variants: Punctuated<ExprVariant, Token![,]>,
}

impl Parse for ExprVariants {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        input
            .parse_terminated(ExprVariant::parse)
            .map(|variants| ExprVariants { variants })
    }
}

struct ExprVariant {
    nullary: bool,
    name: Ident,
    generics: Vec<GenericType>,
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
        let generics = convert_generics(&Generics::parse(input)?);
        Ok(ExprVariant {
            nullary,
            name,
            generics,
        })
    }
}

#[proc_macro]
pub fn gen_expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as ExprVariants);

    let mut node_variants = Punctuated::<TokenStream, Token![,]>::new();
    let mut value_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        node_variants.push(if variant.nullary {
            quote!(#name)
        } else {
            let this_generics = write_node_generics(&variant.generics);
            quote!(#name(#name<#this_generics>))
        });
        value_variants.push(if variant.nullary {
            quote!(#name)
        } else {
            let this_generics = write_value_generics(&variant.generics);
            quote!(#name(#name<#this_generics>))
        });
    }

    let mut gen_from_impls = TokenStream::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        let generics = write_node_generics(&variant.generics);
        let ty = quote!(#name<#generics>);
        if variant.nullary {
            gen_from_impls.extend(quote!{
                impl TryFrom<ExprContents> for #ty {
                    type Error = &'static str;
                    fn try_from(value: ExprContents) -> Result<Self, Self::Error> {
                        if let ExprContents::#name = value { Ok(#name) } else { Err(value.variant_keyword()) }
                    }
                }

                impl From<#ty> for ExprContents {
                    fn from(value: #ty) -> ExprContents {
                        ExprContents::#name
                    }
                }
            });
        } else {
            gen_from_impls.extend(quote!{
                impl TryFrom<ExprContents> for #ty {
                    type Error = &'static str;
                    fn try_from(value: ExprContents) -> Result<Self, Self::Error> {
                        if let ExprContents::#name(x) = value { Ok(x) } else { Err(value.variant_keyword()) }
                    }
                }

                impl From<#ty> for ExprContents {
                    fn from(value: #ty) -> ExprContents {
                        ExprContents::#name(value)
                    }
                }
            });
        }
    }

    let mut node_variant_keywords = Punctuated::<TokenStream, Token![,]>::new();
    let mut value_variant_keywords = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        let generics = write_node_generics(&variant.generics);
        let path = quote!(#name::<#generics>);
        if variant.nullary {
            node_variant_keywords.push(quote!(Self::#name => #path::KEYWORD.unwrap()));
        } else {
            node_variant_keywords.push(quote!(Self::#name(_) => #path::KEYWORD.unwrap()));
        }

        let generics = write_value_generics(&variant.generics);
        let path = quote!(#name::<#generics>);
        if variant.nullary {
            value_variant_keywords.push(quote!(Self::#name => #path::KEYWORD.unwrap()));
        } else {
            value_variant_keywords.push(quote!(Self::#name(_) => #path::KEYWORD.unwrap()));
        }
    }

    let mut parse_expr_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        let generics = write_node_generics(&variant.generics);
        let path = quote!(#name::<#generics>);
        parse_expr_variants
            .push(quote!( #path::KEYWORD => #path::parse_list(ctx, db, span, args)?.into() ));
    }

    let mut serialise_expr_variants = Punctuated::<TokenStream, Token![,]>::new();
    for variant in &input.variants {
        let name = variant.name.clone();
        let generics = write_node_generics(&variant.generics);
        let path = quote!(#name::<#generics>);
        let (variant, serialise) = if variant.nullary {
            (quote!(Self::#name), quote!(#name.serialise(ctx, db)))
        } else {
            (quote!(Self::#name(val)), quote!(val.serialise(ctx, db)))
        };
        serialise_expr_variants.push(quote! {
            #variant => {
                let mut result = #serialise;
                result.insert(0, SexprNode {
                    contents: SexprNodeContents::Atom(#path::KEYWORD.unwrap().to_string()),
                    span: 0..0
                });
                result
            }
        });
    }

    let expr = quote! {
        /// # Adding variants
        /// When adding a new variant to [`ExprContents`], make sure to update:
        /// - [`ExprContents::sub_expressions`]
        /// - [`ExprContents::sub_expressions_mut`]
        #[derive(Debug, PartialEq, Eq)]
        pub enum ExprContents {
            #node_variants
        }

        /// A realisation of an object which may contain inference variables, and may be simplifiable.
        /// Importantly, it contains no provenance about where it came from in the expression - all we care
        /// about is its value.
        /// It therefore contains no feather nodes, and is cloneable.
        ///
        /// # Adding variants
        /// When adding a new variant to [`PartialValue`], make sure to update:
        /// - [`PartialValue::sub_expressions`]
        /// - [`PartialValue::sub_expressions_mut`]
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub enum PartialValue {
            #value_variants
        }

        #gen_from_impls

        impl ExprContents {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    #node_variant_keywords
                }
            }
        }

        impl PartialValue {
            pub fn variant_keyword(&self) -> &'static str {
                match self {
                    #value_variant_keywords
                }
            }
        }

        impl ListSexpr for ExprContents {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
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

            fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
                // TODO: expr infos
                match self {
                    #serialise_expr_variants
                }
            }
        }

        impl ListSexpr for PartialValue {
            const KEYWORD: Option<&'static str> = None;

            fn parse_list(ctx: &mut SexprParseContext, db: &dyn SexprParser, span: Span, mut args: Vec<SexprNode>) -> Result<Self, ParseError> {
                todo!()
            }

            fn serialise(&self, ctx: &SexprSerialiseContext, db: &dyn SexprParser) -> Vec<SexprNode> {
                todo!()
            }
        }
    };

    // let result = expr.into();
    // eprintln!("{}", result);
    // result

    expr.into()
}
