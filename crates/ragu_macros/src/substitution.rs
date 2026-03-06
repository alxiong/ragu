use syn::{
    GenericArgument, GenericParam, Ident, Lifetime, Macro, PathArguments, Type, TypeParam,
    TypeParamBound, TypePath,
    parse::{ParseStream, Parser},
    parse_quote,
    punctuated::Punctuated,
};

use crate::proc::kind::Input;

trait Strategy {
    fn ty_path(&self, _: &mut TypePath) -> bool {
        false
    }
    fn ty(&self, _: &mut Type) -> bool {
        false
    }
    fn lt(&self, _: &mut Lifetime) -> bool {
        false
    }
}

trait Substitution {
    fn substitute(&mut self, strategy: &impl Strategy);
}

impl Substitution for Lifetime {
    fn substitute(&mut self, strategy: &impl Strategy) {
        strategy.lt(self);
    }
}

impl Substitution for GenericArgument {
    fn substitute(&mut self, strategy: &impl Strategy) {
        match self {
            GenericArgument::Type(t) => {
                t.substitute(strategy);
            }
            GenericArgument::Lifetime(lt) => {
                lt.substitute(strategy);
            }
            GenericArgument::Constraint(constraint) => {
                constraint.bounds.iter_mut().for_each(|bound| {
                    bound.substitute(strategy);
                });
            }
            GenericArgument::AssocType(assoc_type) => {
                assoc_type.ty.substitute(strategy);
            }
            _ => {}
        }
    }
}

impl Substitution for TypePath {
    fn substitute(&mut self, strategy: &impl Strategy) {
        if strategy.ty_path(self) {
            return;
        }

        for seg in &mut self.path.segments {
            if let PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                for arg in ab.args.iter_mut() {
                    arg.substitute(strategy);
                }
            }
        }
    }
}

impl Substitution for Type {
    fn substitute(&mut self, strategy: &impl Strategy) {
        if strategy.ty(self) {
            return;
        }

        match self {
            Type::Path(type_path) => {
                type_path.substitute(strategy);
            }
            Type::Tuple(tuple) => {
                for elem in &mut tuple.elems {
                    elem.substitute(strategy);
                }
            }
            Type::Macro(type_macro) => {
                type_macro.mac.substitute(strategy);
            }
            _ => {}
        }
    }
}

impl Substitution for Macro {
    fn substitute(&mut self, strategy: &impl Strategy) {
        if let Ok(mut input) = syn::parse2::<Input>(self.tokens.clone()) {
            // Kind![F; [@] path] — substitute in both the field type and the gadget path.
            input.f.substitute(strategy);
            input.path.substitute(strategy);
            let (f, cast, path) = (&input.f, &input.cast, &input.path);
            self.tokens = quote::quote!(#f ; #cast #path);
        } else {
            // Comma-separated generic arguments, e.g. `unified_output_type!(Point, 'dr, D, C)`.
            // If this also fails, the macro form is unsupported and we surface a clear error
            // rather than silently passing through with unsubstituted driver types.
            type GenericArgs = Punctuated<GenericArgument, syn::Token![,]>;
            let parser = |input: ParseStream| GenericArgs::parse_terminated(input);
            let mut args = Parser::parse2(parser, self.tokens.clone())
                .expect("unsupported macro in Write derive: expected Kind![..] or comma-separated generic arguments");
            for arg in &mut args {
                arg.substitute(strategy);
            }
            self.tokens = quote::quote!(#args);
        }
    }
}

impl Substitution for TypeParamBound {
    fn substitute(&mut self, strategy: &impl Strategy) {
        if let TypeParamBound::Trait(trait_bound) = self {
            for seg in &mut trait_bound.path.segments {
                if let syn::PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                    for arg in ab.args.iter_mut() {
                        arg.substitute(strategy);
                    }
                }
            }
        }
    }
}

/// Replaces `D::F` with `driverfield_ident` in type paths.
struct DriverFieldSubstitution<'a> {
    driver_id: &'a Ident,
    driverfield_ident: &'a Ident,
}

impl Strategy for DriverFieldSubstitution<'_> {
    fn ty_path(&self, ty_path: &mut TypePath) -> bool {
        if ty_path.qself.is_none() && ty_path.path.segments.len() == 2 {
            let segs = &ty_path.path.segments;
            if segs[0].ident == *self.driver_id && segs[1].ident == "F" {
                let driverfield_ident = self.driverfield_ident;
                *ty_path = parse_quote!(#driverfield_ident);
                return true;
            }
        }
        false
    }
}

/// Replace '_ with 'static
/// Replace _ with ::core::marker::PhantomData<$F>
pub fn replace_inferences(ty: &mut Type, field_type: &Type) {
    struct PhantomField<'a> {
        field_type: &'a Type,
    }

    impl Strategy for PhantomField<'_> {
        fn ty(&self, t: &mut Type) -> bool {
            match t {
                Type::Infer(_) => {
                    let replace = self.field_type;
                    *t = parse_quote!(::core::marker::PhantomData<#replace>);
                    true
                }
                _ => false,
            }
        }

        fn lt(&self, lt: &mut Lifetime) -> bool {
            if lt.ident == "_" {
                *lt = parse_quote!('static);
                return true;
            }
            false
        }
    }

    ty.substitute(&PhantomField { field_type });
}

/// Replace $D::F with $DriverField
pub fn replace_driver_field_in_generic_param(
    param: &mut syn::GenericParam,
    driver_id: &syn::Ident,
    driverfield_ident: &syn::Ident,
) {
    let strategy = &DriverFieldSubstitution {
        driver_id,
        driverfield_ident,
    };
    if let GenericParam::Type(TypeParam {
        bounds, default, ..
    }) = param
    {
        for bound in bounds.iter_mut() {
            bound.substitute(strategy);
        }
        if let Some(default_ty) = default {
            default_ty.substitute(strategy);
        }
    }
}

/// Normalize driver references to inference placeholders for use in `Kind!` macro invocations.
///
/// - Replaces `D::F` with `driverfield_ident` (keeps the field type as a concrete ident).
/// - Replaces `D` with `_` (Type::Infer).
/// - Replaces `'dr` with `'_`.
///
/// The result can be passed to `Kind![DriverField; <normalized>]` which will then substitute
/// `_` → `PhantomData<DriverField>` and `'_` → `'static`.
pub fn normalize_for_kind_macro(
    ty: &Type,
    driver_ident: &Ident,
    driver_lifetime: &Lifetime,
    driverfield_ident: &Ident,
) -> Type {
    struct DriverToInference<'a> {
        driver_ident: &'a Ident,
        driver_lifetime: &'a Lifetime,
    }

    impl Strategy for DriverToInference<'_> {
        fn ty(&self, t: &mut Type) -> bool {
            let Type::Path(ty_path) = t else { return false };
            if ty_path.qself.is_none()
                && ty_path.path.segments.len() == 1
                && ty_path.path.segments[0].ident == *self.driver_ident
                && matches!(ty_path.path.segments[0].arguments, PathArguments::None)
            {
                *t = parse_quote!(_);
                return true;
            }
            false
        }

        fn lt(&self, lt: &mut Lifetime) -> bool {
            if lt.ident == self.driver_lifetime.ident {
                *lt = parse_quote!('_);
                return true;
            }
            false
        }
    }

    let mut ty = ty.clone();
    ty.substitute(&DriverFieldSubstitution {
        driver_id: driver_ident,
        driverfield_ident,
    });
    ty.substitute(&DriverToInference {
        driver_ident,
        driver_lifetime,
    });
    ty
}
