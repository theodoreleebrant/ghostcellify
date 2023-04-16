use crate::{lazy_static::lazy_static, Atom, Name, analysis::span::{qname, qname_from_hir}};
/// This module contains a simplified representation of Rust's notion of types.
use itertools::Itertools;
use rustc_ast::ast::LitKind;
use rustc_hir::{def_id::DefId, def::*, *};
use rustc_lint::LateContext;
use rustc_middle::ty::{BoundRegionKind, Region, Ty, TyKind, TypeAndMut, subst};
use std::{
    collections::{BTreeSet, HashMap},
    fmt::Debug,
    panic,
    sync::{
        atomic::{AtomicU32, Ordering},
        Mutex,
    },
};

pub type FnName = String;
pub type Lifetime = Atom;

lazy_static! {
    /// Lifetime counter for instantiating syntactic lifetimes obtained from the program
    static ref LIFETIME_COUNTER: AtomicU32 = AtomicU32::new(0);
    /// Current crate, needs to be updated by the lint passes
    pub static ref CRATE_NAME: Mutex<Name> = Mutex::new(Name::from(""));

    pub static ref UNDERSCORE: Lifetime = Name::from("'_");

    pub static ref BOOL : Name = Name::from("bool");
    pub static ref CHAR : Name = Name::from("char");
    pub static ref STR : Name = Name::from("str");
    pub static ref KW_CRATE : Name = Name::from("crate");
}

/// Function type signatures
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FnSig {
    pub unsafety: Unsafety,
    /// Qualified lifetime variables. The signature may use other,
    /// free, lifetime variables depending on its context.
    pub lifetime_quals: Vec<Lifetime>,
    /// Side-constraints of lifetimes. For example, if a function
    /// signature has side-constraint `'a : 'b` (`'a` outlives `'b`),
    /// then this vector contains `('a, 'b)`.
    // pub lifetime_bounds: Vec<(Lifetime, Lifetime)>,
    pub param_types: Vec<Type>,
    pub ret_type: Box<Type>,
    pub c_variadic: bool,
}

/// Rust types that we care about, this is a watered-down version of
/// [`rustc_middle::ty::TyKind`] that does not contain references to [`TyCtxt`].
#[derive(Clone, PartialEq, Eq)]
pub enum Type {
    Bool,
    Char,
    TyAlias(Name),
    TyParam(Name),
    Generic(Box<Type>, Vec<Type>),
    Int(rustc_type_ir::IntTy),
    Uint(rustc_type_ir::UintTy),
    Float(rustc_type_ir::FloatTy),
    Struct(Name),
    Enum(Name),
    Union(Name),
    Str,
    /// An [`Option`], we keep these separate from structs because
    /// we don't support generics in general but there are `Option`s.
    OptionT(Box<Type>),
    Tuple(Vec<Type>),
    /// An array type with an optional known size
    Array(Box<Type>, Option<usize>),
    Slice(Box<Type>),
    /// Function types, here `FnDef` and `FnPtr` from [`TyKind`] are
    /// merged. This does *not* represent closures.
    Fn(FnSig),
    /// Type of `!`, the bottom type.
    Never,
    /// Pointer types
    Ptr(Mutability, Box<Type>),
    /// Reference types
    Ref(Mutability, Lifetime, Box<Type>),
    /// Boxes, we treat boxes specially to represent owned fields
    Boxed(Box<Type>),
    /// The type that is not represented/unknown/not relevant to the analysis at hand
    Opaque,
    /// An unresolved named-type
    Unknown(Vec<Segment>),
    /// A syntactic type that is semantically unknown. This should not
    /// exist after processing struct definitions
    Syntactic(Vec<Segment>),
    /// A type-level application like `T<'a, 'b>`. We consider applying only lifetimes
    App(Box<Type>, Vec<Lifetime>),
    /// An external, unknown type
    Extern(Name),
}

impl Type {
    pub fn get_inner_tys(ctx: &LateContext, outer: &PathSegment) -> Vec<Self> {
        if let Some(args) = &outer.args {
            args.args.iter().map(|arg| {
                match arg {
                    GenericArg::Type(ty) => Type::from_hir_ty(ctx, ty),
                    _ => panic!("generic arg is not a type")
                }
            }).collect()
        } else {
            vec![]
        }
    }

    pub fn opt_brand_struct(ty: &Type, branded_structs: &HashMap<Name, Lifetime>) -> Option<Lifetime> {
        match ty {
            Type::Ref(_, _, ty) | Type::Boxed(ty) | Type::OptionT(ty) => Type::opt_brand_struct(ty, branded_structs),
            Type::Struct(name) => branded_structs.get(name).cloned(),
            Type::Generic(outer, inner_tys) => 
                Type::opt_brand_struct(outer, branded_structs)
                    .or_else(|| inner_tys.iter().find_map(|ty| Type::opt_brand_struct(ty, &branded_structs))),
            _ => None
        }
    }
    
    /// Create a type object from a HIR (syntactic) type. Using these
    /// types may require extra expansion and support, since these
    /// types are not normalized by type checking.
    // pub fn from_hir_ty(ctx: &LateContext<'_>, ty: &rustc_hir::Ty<'_>) -> Self {
    //     use rustc_hir::TyKind;
    //     use Type::Opaque;
    //     match &ty.kind {
    //         /*
    //         TyKind::Bool => Type::Bool,
    //         TyKind::Char => Type::Char,
    //         TyKind::Int(int_ty) => Type::Int(*int_ty),
    //         TyKind::Uint(uint_ty) => Type::Uint(*uint_ty),
    //         TyKind::Float(float_ty) => Type::Float(*float_ty),
    //         TyKind::Adt(_adt_def, _substitutions) => panic!("not implemented"),
    //         TyKind::Foreign(_def_id) => panic!("not implemented"),
    //         TyKind::Str => Type::Str,*/
    //         TyKind::Array(inner, size) => {
    //             let size_expr = &ctx
    //                 .tcx
    //                 .hir()
    //                 .body(BodyId {
    //                     hir_id: size.hir_id(),
    //                 })
    //                 .value;
    //             // let source_map = ctx.sess().source_map();
    //             let size_value = get_constant_value(size_expr).and_then(|l| match l {
    //                 LitKind::Int(n, _) => Some(n as usize),
    //                 _ => None,
    //             });
    //             if size_value.is_none() {
    //                 log::error!("cannot represent array size: {:?}", size_expr);
    //             }
    //             Type::Array(Box::new(Type::from_hir_ty(ctx, inner)), size_value)
    //         }
    //         TyKind::Slice(inner) => Type::Slice(Box::new(Type::from_hir_ty(ctx, inner))),
    //         TyKind::Ptr(MutTy { ty, mutbl }) => {
    //             Type::Ptr(*mutbl, Box::new(Type::from_hir_ty(ctx, ty)))
    //         }
    //         TyKind::Ref(lifetime, MutTy { ty, mutbl }) => Type::Ref(
    //             *mutbl,
    //             extract_lifetime_name(ctx, &lifetime.res)
    //                 .expect(&format!("expected lifetime at {:?}", ty.span)),
    //             Box::new(Type::from_hir_ty(ctx, ty)),
    //         ),
    //         TyKind::BareFn(fn_ty) => {
    //             // verify & extract generics
    //             let lifetime_quals = fn_ty
    //                 .generic_params
    //                 .iter()
    //                 .map(|param| match &param.kind {
    //                     GenericParamKind::Lifetime { .. } => {
    //                         let def_id = param.def_id;
    //                         let hir_id = ctx.tcx.hir().local_def_id_to_hir_id(def_id);
    //                         let ast_generics = ctx.tcx.hir().get_generics(hir_id.owner.def_id);
    //                         let bounds =
    //                             ast_generics.and_then(|g| g.bounds_span_for_suggestions(def_id));

    //                         let param_name = Name::from(&*param.name.ident().name.as_str());

    //                         param_name  
    //                     }
    //                     _ => panic!(
    //                         "found non-lifetime generics parameter in function type {:?}",
    //                         ty.span
    //                     ),
    //                 })
    //                 .collect::<Vec<Lifetime>>();

    //             let param_types = fn_ty
    //                 .decl
    //                 .inputs
    //                 .iter()
    //                 .map(|ty| Type::from_hir_ty(ctx, ty))
    //                 .collect();

    //             let ret_type = Box::new(match fn_ty.decl.output {
    //                 FnRetTy::DefaultReturn(span) => {
    //                     log::info!(
    //                         "Return type in signature is not specified and type checking result is unavailable. Defaulting to `()` : {:?}",
    //                         span
    //                     );
    //                     Type::Tuple(vec![])
    //                 }
    //                 FnRetTy::Return(ty) => Type::from_hir_ty(ctx, ty),
    //             });

    //             Type::Fn(FnSig {
    //                 unsafety: fn_ty.unsafety,
    //                 lifetime_quals: lifetime_quals,
    //                 param_types: param_types,
    //                 ret_type: ret_type,
    //                 c_variadic: fn_ty.decl.c_variadic,
    //             })
    //         }
    //         TyKind::TraitObject(_, _, _) => panic!("trait objects are not supported"),
    //         TyKind::Never => Opaque,
    //         TyKind::Tup(fields) => {
    //             Type::Tuple(fields.iter().map(|ty| Type::from_hir_ty(ctx, ty)).collect())
    //         }
    //         TyKind::Path(qpath) => {
    //             let path = qpath_to_segments(ctx, qpath, ty.hir_id);
    //             match &path[..] {
    //                 [name] if name == &Segment::new(BOOL.clone()) => Type::Bool,
    //                 [name] if name == &Segment::new(CHAR.clone()) => Type::Char,
    //                 [name] if name == &Segment::new(STR.clone()) => Type::Str,
    //                 _ if path.iter().join("::") == "core::option::Option" => {
    //                     if let QPath::Resolved(_, Path { segments, .. }) = qpath {
    //                         // extract the generic argument from the last segment
    //                         if let rustc_hir::GenericArg::Type(inner_ty) =
    //                             &segments.last().unwrap().args.unwrap().args[0]
    //                         {
    //                             Type::OptionT(Box::new(Type::from_hir_ty(ctx, inner_ty)))
    //                         } else {
    //                             panic!(
    //                                 "the Option at {:?} does not have a single generic type argument",
    //                                 ty.span
    //                             );
    //                         }
    //                     } else {
    //                         panic!(
    //                             "could not get the generic argument of Option at {:?}",
    //                             ty.span
    //                         );
    //                     }
    //                 },
    //                 // TODO: specialize int, float, etc. types with
    //                 // best-effort syntactic matching
    //                 _ => { 
    //                     // log::debug!("tried generic path {:#?}", path);
    //                     if let QPath::Resolved(_, Path { segments, .. }) = qpath {
    //                         let outer = segments.first().unwrap();
    //                         match outer.res {
    //                             Res::Def(DefKind::Struct, def_id) => {
    //                                 let name = Name::from(get_def_qname(ctx, def_id));
    //                                 let outer_ty = Box::new(Type::Struct(name));
                                    
    //                                 Type::Generic(outer_ty, Type::get_inner_tys(ctx, outer))
    //                             }, 
    //                             Res::Def(DefKind::TyParam, def_id) => {
    //                                 let name = Name::from(get_def_qname(ctx, def_id));
    //                                 let outer_ty = Box::new(Type::TyParam(name));
    //                                 Type::Generic(outer_ty, Type::get_inner_tys(ctx, outer))
    //                             },
    //                             Res::Def(DefKind::TyAlias, def_id) => {
    //                                 let name = Name::from(get_def_qname(ctx, def_id));
    //                                 let outer_ty = Box::new(Type::TyAlias(name));
    //                                 Type::Generic(outer_ty, Type::get_inner_tys(ctx, outer))
    //                             },
    //                             Res::Def(DefKind::TyAlias, def_id) => {
    //                                 let name = Name::from(get_def_qname(ctx, def_id));
    //                                 let outer_ty = Box::new(Type::TyAlias(name));
    //                                 Type::Generic(outer_ty, Type::get_inner_tys(ctx, outer))
    //                             }  
    //                             _ => panic!("oops {:#?}", outer)
    //                         }
    //                     } else {
    //                         Type::Syntactic(path)
    //                     }
                        
    //                 },
    //             }
    //         }
    //         TyKind::OpaqueDef(_, _, _) => Opaque,
    //         TyKind::Typeof(_) => panic!("typeof is not supported"),
    //         TyKind::Infer => Opaque,
    //         TyKind::Err => panic!("There is a type error in the program"),
    //     }
    // }

    pub fn from_hir_ty(ctx: &LateContext, ty:  &rustc_hir::Ty<'_>) -> Self {
        Type::from_ty(ctx, rustc_hir_analysis::hir_ty_to_ty(ctx.tcx, &ty))
    }

    fn is_ty(ctx: &LateContext, arg: &subst::GenericArg) -> bool {
        matches!(arg.unpack(), subst::GenericArgKind::Type(_)) 
    }

    pub fn from_ty(ctx: &LateContext, ty: Ty<'_>) -> Self {
        use Type::Opaque;
        match ty.kind() {
            TyKind::Bool => Type::Bool,
            TyKind::Char => Type::Char,
            TyKind::Int(int_ty) => Type::Int(*int_ty),
            TyKind::Uint(uint_ty) => Type::Uint(*uint_ty),
            TyKind::Float(float_ty) => Type::Float(*float_ty),
            TyKind::Adt(adt_def, subs) if subs.non_erasable_generics().next().is_some() => {
                // There is at least one non-erasable generic argument
                let name = qname(ctx, adt_def.did());

                if name == "core::option::Option" {
                    // Special handling of option
                    Type::OptionT(Box::new(Type::from_ty(ctx, subs[0].expect_ty())))
                } else {
                    let name = Name::from(name);
                    let outer = if adt_def.is_struct() {
                            Type::Struct(name)
                        } else if adt_def.is_enum() {
                            Type::Enum(name)
                        } else if adt_def.is_union() {
                            Type::Union(name)
                        } else {
                            unimplemented!("ADT definition is not implemented: {:?}", adt_def)
                    };


                    let inner_tys : Vec<Type> = subs
                        .iter()
                        .filter(|arg| Type::is_ty(ctx, arg))
                        .map(|sub| Type::from_ty(ctx, sub.expect_ty()))
                        .collect();

                    log::debug!("ADT name: {:?}", outer);
                    // log::debug!("inner types {:#?} {:#?}", subs, inner_tys);
                    
                    Type::Generic(
                        Box::new(outer),
                        inner_tys)
                }
            }
            TyKind::Adt(adt_def, _subs) => {
                let name = Name::from(qname(ctx, adt_def.did()));
                if adt_def.is_struct() {
                    Type::Struct(name)
                } else if adt_def.is_enum() {
                    Type::Enum(name)
                } else if adt_def.is_union() {
                    Type::Union(name)
                } else {
                    unimplemented!("ADT definition is not implemented: {:?}", adt_def)
                }
            }
            TyKind::Foreign(def_id) => Type::Extern(Name::from(qname(ctx, *def_id))),
            TyKind::Str => Type::Str,
            TyKind::Array(inner, _size) => Type::Array(Box::new(Type::from_ty(ctx, *inner)), None),
            TyKind::Slice(inner) => Type::Slice(Box::new(Type::from_ty(ctx, *inner))),
            TyKind::RawPtr(TypeAndMut { ty, mutbl }) => {
                Type::Ptr(*mutbl, Box::new(Type::from_ty(ctx, *ty)))
            }
            TyKind::Ref(region, pointee_ty, mutbl) => {
                log::debug!("ty: {:#?}", ty);
                log::debug!("region: {:#?}", region);
                log::debug!("pointee_ty: {:#?}", pointee_ty);
                Type::Ref(
                    *mutbl,
                    region_to_lifetime(*region).unwrap(),
                    Box::new(Type::from_ty(ctx, *pointee_ty)),
                )
            },
            TyKind::FnDef(_, _) => panic!("not implemented: {:?}", ty.kind()),
            TyKind::FnPtr(poly_sig) => {
                // note: for now, we assume that there are no
                // qualifiers in the FnPtr types

                // TODO: make sure that we extract and wrap around qualifiers
                let sig = poly_sig.skip_binder();

                let param_types = sig
                    .inputs()
                    .iter()
                    .map(|ty| Type::from_ty(ctx, *ty))
                    .collect();
                let ret_type = Box::new(Type::from_ty(ctx, sig.output()));
                Type::Fn(FnSig {
                    unsafety: sig.unsafety,
                    param_types,
                    ret_type,
                    lifetime_quals: Vec::new(),
                    // lifetime_bounds: Vec::new(),
                    c_variadic: sig.c_variadic,
                })
            }
            TyKind::Dynamic(..) => panic!("dynamic types are not supported"),
            TyKind::Closure(_, _) => Opaque,
            TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => panic!(
                "generators and generator witnesses are not supported: {:?}",
                ty.kind()
            ),
            TyKind::Never => Opaque,
            TyKind::Tuple(_) => Type::Tuple(
                ty.tuple_fields()
                    .iter()
                    .map(|t| Type::from_ty(ctx, t))
                    .collect(),
            ),
            TyKind::Param(p) => Type::TyParam(Name::from(p.name.as_str())),
            TyKind::Bound(_, _) => panic!("generics and traits are not supported"),
            TyKind::Placeholder(_) => Opaque,
            TyKind::Infer(_) => Opaque,
            TyKind::Error(_) => panic!("There is a type error in the program"),
            TyKind::Alias(..) => panic!("alias not covered"),
        }
    }

    /// Collect all structs that occur in this type
    pub fn collect_structs(&self) -> Vec<Name> {
        match self {
            Type::Struct(name) => vec![name.clone()],
            Type::OptionT(inner) => inner.collect_structs(),
            Type::Tuple(inner) => inner.iter().flat_map(|t| t.collect_structs()).collect(),
            Type::Array(inner, _) => inner.collect_structs(),
            Type::Slice(inner) => inner.collect_structs(),
            Type::Fn(sig) => {
                let mut result = Vec::new();
                sig.param_types
                    .iter()
                    .for_each(|t| result.append(&mut t.collect_structs()));
                result.append(&mut sig.ret_type.collect_structs());
                result
            }
            Type::Ptr(_, inner) => inner.collect_structs(),
            Type::Ref(_, _, inner) => inner.collect_structs(),
            Type::Boxed(inner) => inner.collect_structs(),
            Type::App(inner, _) => inner.collect_structs(),
            Type::Generic(outer, inner) =>  {
                let mut vecs = outer.collect_structs();
                let mut inner: Vec<Name> = inner.iter().flat_map(|t| t.collect_structs()).collect();
                vecs.append(&mut inner);
                vecs
            }
            _ => vec![],
        }
    }

    /// Collect all structs that occur in a this type
    pub fn collect_lifetimes_into(&self, s: &mut BTreeSet<Lifetime>) {
        match self {
            Type::OptionT(inner) => inner.collect_lifetimes_into(s),
            Type::Tuple(inner) => inner.iter().for_each(|t| t.collect_lifetimes_into(s)),
            Type::Array(inner, _) => inner.collect_lifetimes_into(s),
            Type::Slice(inner) => inner.collect_lifetimes_into(s),
            Type::App(inner, lifetimes) => {
                s.extend(lifetimes.clone());
                inner.collect_lifetimes_into(s)
            }
            Type::Fn(sig) => s.extend(sig.lifetime_quals.clone()),
            Type::Ptr(_, inner) => inner.collect_lifetimes_into(s),
            Type::Ref(_, lifetime, inner) => inner.collect_lifetimes_into(s),
            Type::Boxed(inner) => inner.collect_lifetimes_into(s),
            _ => {}
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;

        match self {
            Bool => write!(f, "bool"),
            Char => write!(f, "bool"),
            TyAlias(name) => write!(f, "{}", name),
            TyParam(name) => write!(f, "{}", name),
            Generic(outer, inner) => write!(f, "{}<{}>", outer, inner.iter().format(", ")),
            Int(ty) => write!(f, "{}", ty.name_str()),
            Uint(ty) => write!(f, "{}", ty.name_str()),
            Float(ty) => write!(f, "{}", ty.name_str()),
            Struct(name) => write!(f, "{}", (name)),
            Enum(name) => write!(f, "{}", (name)),
            Union(name) => write!(f, "{}", (name)),
            Str => write!(f, "str"),
            OptionT(inner) => write!(f, "Option<{}>", inner),
            Tuple(elems) => write!(f, "({})", elems.iter().format(", ")),
            Array(inner, None) => write!(f, "[{}; ?]", inner),
            Array(inner, Some(size)) => write!(f, "[{}; {}]", inner, size),
            Slice(inner) => write!(f, "[{}]", inner),
            Fn(sig) => {
                if !sig.lifetime_quals.is_empty() {
                    write!(
                        f,
                        "for <{}>",
                        sig.lifetime_quals
                            .iter()
                            .map(|l| {
                                // // upper bounds for this lifetime variable
                                // let upper_bounds = sig
                                //     .lifetime_bounds
                                //     .iter()
                                //     .filter(|(lower, _)| lower == l)
                                //     .map(|(_, u)| u)
                                //     .join(" + ");
                                // if upper_bounds == "" {
                                l.to_string()
                                // } else {
                                //     format!("{}: {}", l, upper_bounds)
                                // }
                            })
                            .join(", ")
                    )?;
                }
                if sig.unsafety == Unsafety::Unsafe {
                    write!(f, "unsafe extern \"C\" ")?;
                }
                write!(f, " fn")?;
                write!(f, "(")?;
                sig.param_types
                    .iter()
                    .for_each(|t| write!(f, "_: {},", t).unwrap());
                if sig.c_variadic {
                    write!(f, "...")?;
                }
                write!(f, ") -> {}", sig.ret_type)
            }
            Never => write!(f, "!"),
            Ptr(mtbl, inner) => write!(
                f,
                "* {} {}",
                if *mtbl == Mutability::Mut {
                    "mut"
                } else {
                    "const"
                },
                inner
            ),
            Ref(mtbl, lifetime, inner) => write!(f, "&{} {}{}", lifetime, mtbl.prefix_str(), inner),
            Boxed(inner) => write!(f, "Box<{}>", inner),
            Opaque => write!(f, "opaque ?"),
            Unknown(path) => write!(f, "{}", (&path).iter().format("::")),
            Syntactic(path) => write!(f, "{}", (&path).iter().format("::")),
            App(inner, args) => write!(f, "{}<{}>", inner, args.iter().format(", ")),
            Extern(name) => write!(f, "extern type {}", name),
        }
    }
}


impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn extract_lifetime_name(ctx: &LateContext, ln: &LifetimeName) -> Option<Name> {
    use LifetimeName::*;

    match ln {
        Error => None,
        // TODO: derive implicit lifetime constraints in function signatures too
        Implicit => Some(Name::from(format!(
            "'implicit_{}",
            LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst)
        ))),
        ImplicitObjectLifetimeDefault => None,
        Static => Some(Name::from("'static")),
        Underscore => panic!("TODO: generate fresh name for underscores"),
        Param(local_def_id) => Some(Name::from(
            ctx.tcx.item_name(local_def_id.to_def_id()).as_str(),
        )),
    }
}

/// An owning version of rustc's resolved [`PathSegment`], lack of
/// references makes carrying values around much easier.
#[derive(Clone, PartialEq, Eq)]
pub struct Segment {
    pub name: Name,
    pub generic_args: Vec<Type>,
    pub lifetime_args: Vec<Lifetime>,
}

impl Segment {
    pub fn new(name: Name) -> Self {
        Segment {
            name: name,
            generic_args: vec![],
            lifetime_args: vec![],
        }
    }

    pub fn from_string(name: String) -> Self {
        Self::new(Name::from(name.as_str()))
    }

    pub fn from_path_segment(ctx: &LateContext<'_>, segment: &PathSegment<'_>) -> Self {
        let name = Name::from(&*segment.ident.name.as_str());
        let mut generic_args = vec![];
        let mut lifetime_args = vec![];

        if let Some(args) = &segment.args {
            assert!(
                args.bindings.is_empty(),
                "Type bindings are not supported. Type binding at: {:?}",
                segment.ident.span
            );

            for arg in args.args {
                match arg {
                    rustc_hir::GenericArg::Lifetime(l) => {
                        lifetime_args.push(extract_lifetime_name(ctx, &l.res).unwrap());
                    }
                    rustc_hir::GenericArg::Type(ty) => {
                        generic_args.push(Type::from_hir_ty(ctx, ty));
                    }
                    rustc_hir::GenericArg::Const(_) => {
                        panic!("constant generic arguments are not supported");
                    }
                    rustc_hir::GenericArg::Infer(_) => {
                        panic!("inferred generic arguments are not supported");
                    }
                }
            }
        }

        Segment {
            name,
            generic_args,
            lifetime_args,
        }
    }

    pub fn to_string(&self) -> String {
        format!("{:?}", self)
    }

    pub fn flatten(&self) -> Name {
        if self.generic_args.is_empty() && self.lifetime_args.is_empty() {
            self.name.clone()
        } else {
            Name::from(self.to_string())
        }
    }
}

impl Debug for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_args<T: Debug>(f: &mut std::fmt::Formatter<'_>, args: &[T]) -> std::fmt::Result {
            write!(
                f,
                "{}",
                args.iter().map(|arg| format!("{:?}", arg)).join(", ")
            )
        };

        write!(f, "{}", self.name)?;
        if self.generic_args.is_empty() && self.lifetime_args.is_empty() {
            return Ok(());
        }

        write!(f, "<")?;
        write_args(f, &self.lifetime_args)?;

        if !self.generic_args.is_empty() && !self.lifetime_args.is_empty() {
            // put a comma between lifetime and generic args
            write!(f, ", ")?;
        }

        write_args(f, &self.generic_args)?;
        write!(f, ">")
    }
}

impl std::fmt::Display for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Representation of a Rust struct
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Struct {
    /// Qualified name of the struct. This uniquely identifies the struct.
    pub name: Name,
    /// Bound lifetimes of the struct. These are variables that occur
    /// in the fields below (there may be free variables if there are
    /// nested structure definitions but they don't appear in Rust
    /// code generated from C).
    pub lifetime_quals: Vec<Lifetime>,
    /// Lifetime bounds/constraints for struct parameters
    pub lifetime_bounds: Vec<(Lifetime, Lifetime)>,
    /// The fields and their types
    pub fields: Vec<(Name, Type)>,
}

/// Information about a Rust enum
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Enum {
    pub name: Name,
    /// We represent each variant as a struct
    pub variants: Vec<Struct>,
}

/// Information about a C-style union. We keep only names, because we
/// don't translate unions.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Union {
    pub name: Name,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum FnFlavor {
    Normal,
    UsedAsFnPtr,
    Extern,
}

/// Checks if given expression has a constant integral value that is cast
/// to different types (like `1 as c_int as usize`), and get its value.
pub fn get_constant_value(expr: &rustc_hir::Expr) -> Option<LitKind> {
    match &expr.kind {
        ExprKind::Lit(lit) => Some(lit.node.clone()),
        ExprKind::Cast(inner, _) => get_constant_value(inner),
        _ => None,
    }
}

pub fn qpath_to_segments<'tcx>(
    ctx: &LateContext<'_>,
    qpath: &QPath<'tcx>,
    hir_id: HirId,
) -> Vec<Segment> {
    use rustc_hir::def::Res::*;
    use QPath::*;

    let resolve_path_directly = || match qpath {
        Resolved(_self_ty, path) => path
            .segments
            .iter()
            .map(|segment| Segment::from_path_segment(ctx, segment))
            .filter(|s| !s.name.is_empty())
            .collect(),
        TypeRelative(self_ty, segment) => {
            // TODO: process self_ty properly, splitting generics
            vec![
                Segment::from_string(format!("{:?}", self_ty)),
                Segment::from_path_segment(ctx, segment),
            ]
        }
        LangItem(item, _, _) => {
            // TODO: process lang item names properly
            vec![Segment::from_string(format!("{}", item.name()))]
        }
    };

    // log::debug!("true path segment {:#?}", resolve_path_directly());

    match ctx.qpath_res(qpath, hir_id) {
        Def(_, def_id) => ctx
            .get_def_path(def_id)
            .iter()
            .map(|s| Segment::new(Name::from(&*s.as_str())))
            .filter(|s| !s.name.is_empty())
            .collect(),
        Local(_) | Err => resolve_path_directly(),
        PrimTy(prim) => vec![Segment::new(Name::from(prim.name_str()))],
        def => todo!("{:?}", def),
    }
}

fn region_to_lifetime(r: Region<'_>) -> Option<Lifetime> {
    use rustc_type_ir::sty::RegionKind::*;

    let bound_region_name = |b| match b {
        BoundRegionKind::BrAnon(_number, _) => panic!("TODO: use the anonymous region number"),
        BoundRegionKind::BrNamed(_, name) => Name::from(&*name.as_str()),
        BrEnv => panic!("TODO: handle anonymous regions passed to closures"),
    };

    // TODO: handle free region names appropriately
    match r.kind() {
        ReEarlyBound(b) => Some(Name::from(b.name.as_str())),
        ReLateBound(_debruijn_index, b) => Some(bound_region_name(b.kind)),
        ReFree(f) => Some(bound_region_name(f.bound_region)),
        ReVar(_) => panic!("region variables should not exist after type check"),
        RePlaceholder(_) => {
            panic!("higher-ranked region placeholders should not exist after type check")
        }
        ReStatic => Some(Name::from("'static")),
        ReErased => Some(Name::from("'_")), // TODO: handle this better
    }
}
