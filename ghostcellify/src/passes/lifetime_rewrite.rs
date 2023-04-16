
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    analysis::{self, span::{qname_from_hir, qname, attr_contains}}, 
    types::*,
    constants::*,
    passes::{struct_info::*, token_analysis::*}, 
    rustc_lint::{LateContext, LintContext, LateLintPass, LintPass},
    rustc_hir::{Expr, TyKind, Path, ExprKind, QPath, def, PatKind, intravisit::FnKind, Impl, ItemKind, Item, FieldDef, Generics},
    rustc_middle::ty::{TyCtxt},
    Name, compiler_interface::{LatePass, EarlyPass}, rustfix_utils::{self, make_suggestion},
};
use itertools::Itertools;
use quote::IdentFragment;

use super::token_analysis::TokenAnalysis;

pub struct LifetimeRewriteAnalysis {
    struct_info: StructInfo,
    token_analysis: TokenAnalysis
}

impl LifetimeRewriteAnalysis {
    pub fn new() -> Self {
        Self {
            struct_info: analysis::result::<StructInfo>().unwrap(),
            token_analysis: analysis::result::<TokenAnalysis>().unwrap(),
        }
    }
}

pub struct LifetimeRewritePass {
    ctx: LifetimeRewriteAnalysis,
    params: HashSet<Name>,
    in_call: bool, // TOOD: replace with proper visitor
    depth: i32,
}

impl LifetimeRewritePass {
    pub fn new<'tcx>(_tcx: TyCtxt<'tcx>) -> std::boxed::Box<(dyn LateLintPass<'tcx> + 'tcx)> {
        Box::new(LifetimeRewritePass {
            ctx: LifetimeRewriteAnalysis::new(),
            params: HashSet::default(),
            in_call: false,
            depth: 1,
        })
    }

    fn process_def<'tcx>(
        &mut self,
        ctx: &LateContext<'tcx>,
        name: Name,
        generics: &'tcx rustc_hir::Generics<'tcx>,
        is_params: bool,
    ) {
        if is_params && self.params.contains(&name) {
            return;
        }

        // is this a branded struct or alias?
        let brands = self.ctx.struct_info.brands(&name);

        let mut param_strs = generics.params.iter().map(|param| {
            ctx.sess().source_map().span_to_snippet(param.span).unwrap()
        }).collect::<Vec<_>>();

        let mut new_params = brands
            .iter()
            .map(|b| format!("'{}", b))
            .collect::<Vec<_>>();
        new_params.append(&mut param_strs);

        if is_params {
            self.params.insert(name);
        } 

        // emit lint
        rustfix_utils::make_suggestion(
            ctx, 
            generics.span, 
            "add brand to def".into(), 
            format!("<{}>", new_params.join(", ")), 
            self.depth
        );
    }

    pub fn rewrite_segment<'tcx>(&mut self, ctx: &LateContext<'tcx>, path: &rustc_hir::Path<'tcx>, seg: &rustc_hir::PathSegment<'tcx>) {
        match seg.res {
            def::Res::Def(def::DefKind::Struct | def::DefKind::TyAlias, def_id) => {
                let name = Name::from(qname(ctx, def_id));
                let brands = self.ctx.struct_info.brands(&name);

                if brands.is_empty() {
                    return;
                };

                let mut new_params = brands
                    .iter()
                    .map(|b| format!("'{}", b))
                    .collect::<Vec<_>>();

                if let Some(args) = seg.args && !args.args.is_empty() {
                    let arg = args.args.first().unwrap();
                    let span = arg.span();
                    let arg_str = ctx.sess().source_map().span_to_snippet(span).unwrap();

                    rustfix_utils::make_suggestion(
                        ctx, 
                        span, 
                        "adding lifetime for arg".into(), 
                        format!("{}, {}", new_params.iter().join(", "), arg_str), 
                        self.depth)
                } else {
                    rustfix_utils::make_suggestion(
                        ctx, 
                        path.span.shrink_to_hi(), 
                        "adding lifetime for arg".into(), 
                        format!("<{}>", new_params.iter().join(", ")), 
                        self.depth)
                }
            },
            _ => ()
        }
    }

    pub fn rewrite_path<'tcx>(&mut self, ctx: &LateContext<'tcx>, path: &rustc_hir::Path<'tcx>) {
        path.segments.iter().for_each(|seg| {
            self.rewrite_segment(ctx, path, seg);
        });
    }
}

impl LintPass for LifetimeRewritePass {
    fn name(&self) -> &'static str {
        "LifetimeRewritePass" 
    }
}

impl<'tcx> LateLintPass<'tcx> for LifetimeRewritePass {
    fn check_item(&mut self, ctx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        // Get the name only when necessary.
        let name = || Name::from(qname_from_hir(ctx, item.hir_id()));

        match &item.kind {
            ItemKind::Struct(data, generics) => {
                self.process_def(ctx, name(), generics, true);
            }
            ItemKind::TyAlias(ty, generics) => {
                self.process_def(ctx, name(), generics, true);
            }
            ItemKind::Impl(Impl { generics, self_ty, ..} ) => {
                match &self_ty.kind {
                    TyKind::Path(QPath::Resolved(_, Path { res: def::Res::Def(def::DefKind::Struct, def_id), .. })) => {
                        let name = Name::from(qname(ctx, *def_id));
                        self.process_def(ctx, name, generics, false);
                    },
                    _ => ()
                }
                // self.process_def(ctx, name, generics);
            }
            _ => {} // ignore other item kinds
        }
    }

    fn check_expr(&mut self, ctx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        // check if expr is a method call
        if let ExprKind::Path(..) = expr.kind {
            self.in_call = true;
            // log::warn!("in call: {}", self.in_call);
        } else {
            self.in_call = false;
        } 
    }

    fn check_expr_post(&mut self, ctx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::Path(QPath::TypeRelative(ty, ..)) => {
                match ty { 
                    rustc_hir::Ty { kind: TyKind::Path(QPath::Resolved(_, path)), ..} => {
                    let path_str = ctx.sess().source_map().span_to_snippet(path.span).unwrap();
                    let has_refcell = path_str == "RefCell";

                    if has_refcell {
                        make_suggestion(
                            ctx, 
                            path.span, 
                            "replace RefCell with GhostCell in expr".into(),
                            "GhostCell".into(),
                            self.depth)
                    }
                    },
                    _ => ()
                }
            },
            ExprKind::Call(fn_expr, args) => {
                if let ExprKind::Path(QPath::TypeRelative(_, seg)) = fn_expr.kind {
                    // TODO: fix and resolve qpah
                    let ident = seg.ident.as_str();

                    // check if any key in map matches ident, and return value
                    // TODO: check for exact match
                    let token = self.ctx.token_analysis.fn_token.iter().find(|(k, _)| k.contains(&ident)).map(|(_, v)| v);

                    if matches!(token, Some(TokenKind::Mut(_)) | Some(TokenKind::Immut(_))) {
                        let arg = args.last().expect("expected at least one fn arg");
                        let arg_str = ctx.sess().source_map().span_to_snippet(arg.span).unwrap();
                        make_suggestion(
                            ctx, 
                            arg.span, 
                            "add token to fn call".into(), // TODO: check if fn requires token
                            format!("{}, token", arg_str),
                            self.depth)
                    }
                }
            }
            _ => {}
        }
    }

    fn check_ty(&mut self, ctx: &LateContext<'tcx>, ty: &'tcx rustc_hir::Ty<'tcx>) {
        self.in_call = false;

        match &ty.kind {
            TyKind::Path(QPath::Resolved(_, path)) => {
                let seg = path.segments.last().unwrap();
                let seg_str = ctx.sess().source_map().span_to_snippet(seg.ident.span).unwrap();

                match seg.args {
                        Some(args @ rustc_hir::GenericArgs { args: [rustc_hir::GenericArg::Type(ty)], ..})  => {
                            match Type::from_hir_ty(ctx, ty) {
                                Type::Generic(box Type::Struct(name), _) => {
                                    let brands = self.ctx.struct_info.brands(&name);

                                    let arg = args.args.first().unwrap();
                                    let span = arg.span().shrink_to_lo();
                            
                                    let new_params = brands
                                        .iter()
                                        .map(|b| format!("'{}", b))
                                        .collect::<Vec<_>>();

                                    let has_refcell = seg_str == ("RefCell"); // TODO use absolute path

                                    if has_refcell {
                                        rustfix_utils::make_suggestion(
                                            ctx, 
                                            span, 
                                            "add brand to type".into(), 
                                            format!("{}, ", new_params.join(", ")), 
                                            self.depth
                                        );
    
    
                                        rustfix_utils::make_suggestion(
                                            ctx, 
                                            seg.ident.span, 
                                            "replace RefCell in type".into(), 
                                            format!("GhostCell"), 
                                            self.depth
                                        );
                                    } else {
                                        // log::warn!("non-refcell path_str: {}", path_str);
                                        self.rewrite_path(ctx, path);
                                    }

                                },
                                _ => {
                                    // log::warn!("non-struct path_str: {}", path_str);
                                    self.rewrite_path(ctx, path);
                                }
                            }
                        },
                        _ => ()
                }
            },
            _ => {}
        }
    }
}