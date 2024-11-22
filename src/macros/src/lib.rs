use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use std::iter;
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
    token, Data, DeriveInput, Error, Ident, LitInt, Path, Result, Token, TypePath, Visibility,
};

/// Derive macro generating an impl of the trait `Component`.
///
/// # Examples
///
/// ```
/// # use my_ecs_macros::Component;
///
/// #[derive(Component, Default)]
/// struct CompA;
///
/// #[derive(Component, Default)]
/// struct CompB(u8);
///
/// #[derive(Component, Default)]
/// struct CompC {
///     vel: (f32, f32, f32),
///     acc: (f32, f32, f32),
/// }
/// ```
#[proc_macro_derive(Component)]
pub fn derive_component(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let ident = ast.ident.clone();

    TokenStream::from(quote! {
        // Implements `Component` trait.
        impl my_ecs::ecs::ent::component::Component for #ident {}
    })
}

/// # Examples
///
/// ```
/// # use my_ecs_macros::{Component, Entity};
///
/// #[derive(Component)]
/// struct CompA;
///
/// #[derive(Entity)]
/// #[entity_hasher(std::hash::RandomState)]
/// struct EntA {
///     a: CompA,
/// }
/// ```
#[proc_macro_derive(Entity, attributes(entity_hasher))]
pub fn derive_entity(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let ident = input.ident.clone();
    let ident_str = ident.to_string();

    let (field_idents, field_types): (Vec<_>, Vec<_>) = match input.data {
        Data::Struct(data_struct) => data_struct
            .fields
            .iter()
            .map(|field| (field.ident.clone(), field.ty.clone()))
            .unzip(),
        _ => panic!("only struct is allowed for this macro"),
    };

    // Validates that all fields implement `Compoenent` trait.
    let validate_impl_component = quote! {
        const _: () = {
            const fn validate<T: my_ecs::ecs::ent::component::Component>() {}
            #(
                validate::<#field_types>();
            )*
        };
    };

    // Determines hasher for `EntityReg`.
    let hasher = input
        .attrs
        .iter()
        .filter_map(|attr| {
            if attr.path().is_ident("entity_hasher") {
                let ty: Path = attr.parse_args().unwrap();
                Some(quote! { #ty })
            } else {
                None
            }
        })
        .next()
        .unwrap_or(quote! { std::hash::RandomState });

    // Implements `AsEntityReg` trait.
    let impl_as_entity_desc = quote! {
        impl my_ecs::ecs::ent::storage::AsEntityReg for #ident {
            fn as_entity_descriptor() -> my_ecs::ecs::ent::storage::EntityReg {
                let mut desc =
                    my_ecs::ecs::ent::storage::EntityReg::new_with_default_container::<#hasher>(
                    my_ecs::ecs::ent::entity::EntityName::new(#ident_str.into()),
                    Some(my_ecs::ecs::ent::entity::EntityTypeId::of::<#ident>()),
                );
                #(
                    desc.add_component(my_ecs::tinfo!(#field_types));
                )*
                desc
            }
        }
    };

    // Implements `Entity` trait.
    let num_fields = field_types.len();
    let col_idxs = 0..num_fields;
    let impl_as_entity = quote! {
        impl my_ecs::ecs::ent::entity::Entity for #ident {
            fn move_to<T: my_ecs::ecs::ent::entity::AddEntity + ?Sized>(mut self, cont: &mut T) -> usize {
                cont.begin_add_row();

                #(
                    // Safety: Infallible.
                    unsafe {
                        cont.add_value(
                            #col_idxs,
                            std::ptr::NonNull::new_unchecked(
                                (&mut self.#field_idents as *mut _ as *mut u8)
                            )
                        );
                    }
                )*

                #[allow(clippy::forget_non_drop)]
                std::mem::forget(self);

                cont.end_add_row()
            }
        }
    };

    TokenStream::from(quote! {
        #validate_impl_component
        #impl_as_entity_desc
        #impl_as_entity
    })
}

#[proc_macro_derive(Resource)]
pub fn derive_resource(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let ident = ast.ident.clone();

    TokenStream::from(quote! {
        // Implements the trait `Resource`.
        impl my_ecs::ecs::resource::Resource for #ident {}
    })
}

#[proc_macro]
pub fn filter(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as Filter);

    // `Target`, `All`, `Any`, and `None` types must implement `Component`.
    let target = &input.target.ty;
    let empty = Punctuated::<TypePath, Token![,]>::new();
    let all = get_iter(&input.all, &empty);
    let any = get_iter(&input.any, &empty);
    let none = get_iter(&input.none, &empty);
    let all_clone = all.clone();
    let any_clone = any.clone();
    let none_clone = none.clone();
    let validate_impl_component = quote! {
        const _: () = {
            const fn validate<T: my_ecs::ecs::ent::component::Component>() {}
            validate::<#target>();
            #(validate::<#all_clone>();)*
            #(validate::<#any_clone>();)*
            #(validate::<#none_clone>();)*
        };
    };

    // Validates that `Target`, `All` and `Any` doesn't overlap `None`.
    let positive = iter::once(target).chain(all.clone()).chain(any.clone());
    let pairs = positive.flat_map(|p| none.clone().map(move |n| (p, n)));
    let ps = pairs.clone().map(|(p, _)| p);
    let ns = pairs.map(|(_, n)| n);
    let validate_non_overlap = quote! {
        const _: () = {#(
            assert!(
                !my_ecs::ds::types::TypeHelper::<(#ps, #ns)>::IS_EQUAL_TYPE,
                "Types in `Target`, `All`, and `Any` must not be included in `None`",
            );
        )*};
    };

    // The same purpose of code above.
    // This gives more specific position where the error occurs.
    // However, this cannot detect something like as follows
    // Target = Ca, None = crate::Ca
    let positive = iter::once(target).chain(all).chain(any);
    if let Some(conflict) = none.clone().find(|&n| positive.clone().any(|p| p == n)) {
        let err = Error::new(conflict.span(), "conflicts").into_compile_error();
        return TokenStream::from(err);
    }

    // Declares a struct with the given ident.
    let vis = &input.vis;
    let ident = &input.ident;
    let decl_struct = quote! {
        #vis struct #ident;
    };

    // Implements `Filter`.
    let impl_filter = input.token_stream();

    return TokenStream::from(quote! {
        #validate_impl_component
        #validate_non_overlap
        #decl_struct
        #impl_filter
    });

    // === Internal helper functions ===

    fn get_iter<'a>(
        x: &'a Option<(Token![,], Ident, FilterList)>,
        empty: &'a Punctuated<TypePath, Token![,]>,
    ) -> syn::punctuated::Iter<'a, TypePath> {
        if let Some((_, _, list)) = x {
            list.types.iter()
        } else {
            empty.iter()
        }
    }
}

#[derive(Debug)]
struct Filter {
    vis: Visibility,
    ident: Ident,
    _comma: Token![,],
    target: FilterTarget,
    all: Option<(Token![,], Ident, FilterList)>,
    any: Option<(Token![,], Ident, FilterList)>,
    none: Option<(Token![,], Ident, FilterList)>,
}

impl Filter {
    fn token_stream(&self) -> TokenStream2 {
        let ident = &self.ident;
        let target = &self.target.ty;
        let all = from_list(&self.all);
        let any = from_list(&self.any);
        let none = from_list(&self.none);

        return quote! {
            impl my_ecs::ecs::sys::filter::Filter for #ident {
                type Target = #target;
                type All = #all;
                type Any = #any;
                type None = #none;
            }
        };

        // === Internal helper functions ===

        fn from_list(x: &Option<(Token![,], Ident, FilterList)>) -> TokenStream2 {
            if let Some((_, _, list)) = x.as_ref() {
                let types = &list.types;
                quote! {( #types )}
            } else {
                quote! {()}
            }
        }
    }
}

impl Parse for Filter {
    fn parse(input: ParseStream) -> Result<Self> {
        // Parses struct ident.
        let vis: Visibility = input.parse()?;
        let ident: Ident = input.parse()?;

        // Parses `Target`.
        let comma: Token![,] = input.parse()?;
        let target: FilterTarget = input.parse()?;

        // Parses `All`.
        let mut all = None;
        let mut any = None;
        let mut none = None;
        while input.peek(Token![,]) {
            let comma: Token![,] = input.parse()?;
            let ident: Ident = input.parse()?;
            let ident_str = ident.to_string();
            match ident_str.as_str() {
                "All" => {
                    if all.is_some() {
                        return Err(Error::new(ident.span(), "duplicate `All`"));
                    }
                    let list: FilterList = input.parse()?;
                    all = Some((comma, ident, list));
                }
                "Any" => {
                    if any.is_some() {
                        return Err(Error::new(ident.span(), "duplicate `Any`"));
                    }
                    let list: FilterList = input.parse()?;
                    any = Some((comma, ident, list));
                }
                "None" => {
                    if none.is_some() {
                        return Err(Error::new(ident.span(), "duplicate `None`"));
                    }
                    let list: FilterList = input.parse()?;
                    none = Some((comma, ident, list));
                }
                _ => {
                    return Err(Error::new(ident.span(), "expected `All`, `Any` or `None`"));
                }
            }
        }

        Ok(Self {
            vis,
            ident,
            _comma: comma,
            target,
            all,
            any,
            none,
        })
    }
}

#[derive(Debug)]
struct FilterTarget {
    _ident: Ident,
    _eq: Token![=],
    ty: TypePath,
}

impl Parse for FilterTarget {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        if ident.to_string().as_str() != "Target" {
            return Err(Error::new(ident.span(), "expected `Target`"));
        }
        let eq: Token![=] = input.parse()?;
        let ty: syn::TypePath = input.parse()?;

        Ok(Self {
            _ident: ident,
            _eq: eq,
            ty,
        })
    }
}

#[derive(Debug)]
struct FilterList {
    _eq: Token![=],
    _paren: Option<token::Paren>,
    types: Punctuated<TypePath, Token![,]>,
}

impl Parse for FilterList {
    fn parse(input: ParseStream) -> Result<Self> {
        let eq: Token![=] = input.parse()?;

        let (paren, types) = if input.peek(token::Paren) {
            let content;
            let paren = Some(parenthesized!(content in input));
            let types = content.parse_terminated(TypePath::parse, Token![,])?;
            (paren, types)
        } else {
            let paren = None;
            let ty: TypePath = input.parse()?;
            let types: Punctuated<TypePath, Token![,]> = iter::once(ty).collect();
            (paren, types)
        };

        Ok(Self {
            _eq: eq,
            _paren: paren,
            types,
        })
    }
}

#[proc_macro]
pub fn nth(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as Nth);
    let identifiers = input.identifiers.into_iter().collect::<Vec<_>>();
    if input.n < identifiers.len() {
        let ident = &identifiers[input.n];
        TokenStream::from(quote! { #ident })
    } else {
        panic!("Index out of bounds");
    }
}

struct Nth {
    n: usize,
    _comma: Token![,],
    identifiers: Punctuated<Ident, Token![,]>,
}

impl Parse for Nth {
    fn parse(input: ParseStream) -> Result<Self> {
        let n: LitInt = input.parse()?;
        Ok(Nth {
            n: n.base10_parse()?,
            _comma: input.parse()?,
            identifiers: input.parse_terminated(Ident::parse, Token![,])?,
        })
    }
}

#[proc_macro]
pub fn repeat(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as Repeat);
    let job = input.job;
    let jobs = (0..input.n).map(|i| {
        quote! { #job!(#i); }
    });

    TokenStream::from(quote! { #(#jobs)* })
}

struct Repeat {
    n: usize,
    _comma: Token![,],
    job: Ident,
}

impl Parse for Repeat {
    fn parse(input: ParseStream) -> Result<Self> {
        let n: LitInt = input.parse()?;
        Ok(Repeat {
            n: n.base10_parse()?,
            _comma: input.parse()?,
            job: input.parse()?,
        })
    }
}
