use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    analysis::{self, span::{qname_from_hir}}, 
    types::*,
    constants::*,
    passes::struct_info::*, 
    rustc_lint::{LateContext, LateLintPass, LintPass},
    rustc_hir::{Expr, ExprKind, QPath, def, PatKind, intravisit::FnKind},
    rustc_middle::ty::{TyCtxt},
    Name, compiler_interface::LatePass,
};

use super::callgraph::CallGraph;

// PartialOrd will ensure that TokenKind::NoToken is always the smallest
#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub enum TokenKind {
    NoToken,
    Immut(Lifetime), // lifetime name
    Mut(Lifetime), // lifetime name
}

pub fn method_resolved_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> Option<Name> {
    if let ExprKind::MethodCall(path, _, _, _) = &expr.kind {
        let def_id = cx.typeck_results().type_dependent_def_id(expr.hir_id).unwrap();
        let path = cx.tcx.def_path_str(def_id);
        Some(Name::from(path))
    } else {
        None
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenAnalysis {
    struct_info: StructInfo,
    callgraph: CallGraph,
    pub fn_token: HashMap<Name, TokenKind>,
}

impl TokenAnalysis {
    pub fn new() -> Self {
        Self {
            struct_info: analysis::result::<StructInfo>().unwrap(),
            callgraph: analysis::result::<CallGraph>().unwrap(),
            fn_token: HashMap::new(),
        }
    }

    pub fn has_token(&self, name: &Name) -> bool {
        self.fn_token.contains_key(name)
    }

    pub fn get_token(&self, name: &Name) -> TokenKind {
        self.fn_token.get(name).unwrap_or(&TokenKind::NoToken).clone()
    }

    pub fn set_token(&mut self, name: Name, token: TokenKind) {
        let curr_token = self.get_token(&name);
        if token > curr_token {
            self.fn_token.insert(name, token);
        }
    }
}

impl analysis::AnalysisResult for TokenAnalysis {
    fn name() -> String {
        "TokenAnalysis".to_owned()
    }
}


pub struct TokenAnalysisPass {
    ctx: TokenAnalysis,
    curr: Option<Name>,
}

impl TokenAnalysisPass {
    pub fn new<'tcx>(_tcx: TyCtxt<'tcx>) -> std::boxed::Box<(dyn LateLintPass<'tcx> + 'tcx)> {
        Box::new(TokenAnalysisPass {
            ctx: TokenAnalysis::new(),
            curr: None,
        })
    }
}

impl LintPass for TokenAnalysisPass {
    fn name(&self) -> &'static str {
        "TokenAnalysisPass" 
    }
}

impl<'tcx> LateLintPass<'tcx> for TokenAnalysisPass {
    fn check_fn(
        &mut self,
        cx: &rustc_lint::LateContext<'tcx>,
        kind: FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        _: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        hir_id: rustc_hir::HirId,
    ) {
        // skip closures
        if let FnKind::Closure = kind {
            return;
        }

        let name = Name::from(qname_from_hir(cx, hir_id));
        self.curr = Some(name.clone());
        self.ctx.set_token(name, TokenKind::NoToken);
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if let Some(name) = &self.curr {
            // check if the expr is a method call
            if let ExprKind::MethodCall(path, recv, _, _) = &expr.kind {
                let path = method_resolved_path(cx, expr).unwrap_or_default();

                let recv_ty = Type::from_ty(cx, cx.typeck_results().expr_ty(&recv));

                let brand = Type::opt_brand_struct(&recv_ty, &self.ctx.struct_info.branded_structs);

                if brand.is_none() { // none of the types are branded
                    log::debug!("fn {}: {} {:#?}", name, recv_ty, &self.ctx.struct_info.branded_structs);
                    return;
                }

                log::debug!("fn {}: {} -> {:?}", name, path, brand.clone().unwrap());

                // check if the method is a borrow
                if path == String::from("std::cell::RefCell::<T>::borrow") {
                    // if so, set the token to Immut
                    self.ctx.set_token(name.clone(), TokenKind::Immut(brand.unwrap()));
                } else if path == String::from("std::cell::RefCell::<T>::borrow_mut") {
                    // if so, set the token to Mut
                    self.ctx.set_token(name.clone(), TokenKind::Mut(brand.unwrap()));
                } 
            }
        }
    }

    fn check_crate_post(&mut self, _: &LateContext<'tcx>) {
        // for each callee fn in callgraph closure, add token to caller
        let closure = self.ctx.callgraph.closure.clone();
        for (caller, callees) in closure.iter() {
            for callee in callees {
                let token = self.ctx.get_token(callee);
                self.ctx.set_token(caller.clone(), token);
            }
        }

        analysis::replace::<TokenAnalysis>(Box::new(self.ctx.clone()));
    }
}


