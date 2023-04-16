use std::collections::HashMap;

use crate::utils::parse_item;
use crate::utils::{self, add_brands};
use rustc_ast::ast::*;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast::ptr::P;
use rustc_ast::visit::Visitor;
use rustc_ast_pretty::pprust::crate_to_string_for_macros;
use rustc_middle::ty::TyCtxt;
use rustc_parse::parser::{ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::source_map::FilePathMapping;
use rustc_span::symbol::Ident;
use rustc_span::FileName;
use syn::parse::Parse;

struct AddImport {
    sess: ParseSess,
}

impl MutVisitor for AddImport {
    fn visit_crate(&mut self, c: &mut Crate) {
        // Parse a quoted string into a tree, don't use syn
        let use_ghostcell = parse_item("use ghostcell::{GhostCell, GhostToken};", &self.sess);
        // Push item into the crate
        c.items.insert(0, use_ghostcell);
    }
}

struct GetGhostCellifyStructs {
    ghostcellified_structs: Vec<(NodeId, Ident)>,
    all_structs: Vec<(NodeId, Ident)>,
    struct_generics: HashMap<Ident, Vec<GenericParam>>,
}

impl<'ast> Visitor<'ast> for GetGhostCellifyStructs {
    fn visit_item(&mut self, i: &'ast Item) {
        if let ItemKind::Struct(_, generics) = &i.kind {
            self.all_structs.push((i.id, i.ident));
            self.struct_generics.insert(i.ident, Vec::new());
            if utils::item_contains_ghostcellify(i) {
                self.ghostcellified_structs.push((i.id, i.ident));
            }
        }
    }
}

struct MakeStructGraph {
    graph: HashMap<Ident, Vec<Ident>>,
    all_structs: Vec<Ident>,
    curr: Option<(NodeId, Ident)>,
}

impl<'ast> Visitor<'ast> for MakeStructGraph {
    fn visit_item(&mut self, i: &'ast Item) {
        self.curr = Some((i.id, i.ident));
        match &i.kind {
            ItemKind::Struct(ref variant_data, _generics) => {
                self.graph.insert(i.ident, vec![]);
                self.visit_variant_data(variant_data);
            }
            _ => {}
        }
        self.curr = None;
    }

    fn visit_variant_data(&mut self, v: &'ast VariantData) {
        match v {
            VariantData::Struct(fields, _) => {
                for field in fields {
                    self.visit_ty(&field.ty);
                }
            }
            _ => {}
        }
    }

    fn visit_path_segment(&mut self, ps: &'ast PathSegment) {
        if self.all_structs.contains(&ps.ident) {
            // extract current (parent) id and ident
            let (_curr_id, curr_ident) = self.curr.unwrap();
            let mut children_vec = self.graph.get_mut(&curr_ident).unwrap();
            children_vec.push(ps.ident);
        }
        rustc_ast::visit::walk_path_segment(self, ps);
    }
}

struct AddGenericParams {
    target: HashMap<Ident, Vec<GenericParam>>,
}
impl MutVisitor for AddGenericParams {
    fn visit_crate(&mut self, c: &mut Crate) {
        for item in &mut c.items {
            let contains_key = self.target.contains_key(&item.ident);
            let ident = item.ident.clone();
            if let ItemKind::Struct(_, ref mut struct_generics) = &mut item.kind {
                if contains_key {
                    let mut generics = self.target.get(&ident).unwrap().clone();
                    generics.append(&mut struct_generics.params.clone());
                    struct_generics.params = generics;
                }
            }

            if let ItemKind::Impl(box Impl {
                ref mut generics,
                ref mut self_ty,
                ..
            }) = &mut item.kind
            {
                if let Some(ident) = utils::brand_in_ty(&self.target, self_ty) {
                    let mut generic_params = self.target.get(&ident).unwrap().clone();
                    generic_params.append(&mut generics.params.clone());
                    generics.params = generic_params;
                }
            }
        }
    }
}

struct AddGenericArgs {
    target: HashMap<Ident, Vec<GenericArg>>,
}
impl MutVisitor for AddGenericArgs {
    fn visit_ty(&mut self, ty: &mut P<Ty>) {
        if let TyKind::Path(_, ref mut path) = &mut ty.kind {
            for ps in &mut path.segments {
                let id = ps.ident;
                if self.target.contains_key(&id) {
                    let args = self.target.get(&id).unwrap();
                    let mut g_args: Vec<AngleBracketedArg> = args
                        .iter()
                        .map(|x| AngleBracketedArg::Arg(x.clone()))
                        .collect();
                    match &mut ps.args {
                        Some(gargs) => {
                            match gargs.clone().into_inner() {
                                GenericArgs::AngleBracketed(ref mut ab_args) => {
                                    g_args.append(&mut ab_args.args.clone());
                                    ps.args =
                                        Some(P(GenericArgs::AngleBracketed(AngleBracketedArgs {
                                            args: g_args,
                                            span: path.span,
                                        })));
                                }
                                // TODO: what to do if it is a parenthesized arg?
                                _ => (),
                            }
                        }
                        None => {
                            eprint!("None case");
                            ps.args = Some(P(GenericArgs::AngleBracketed(AngleBracketedArgs {
                                args: g_args,
                                span: path.span,
                            })));
                        }
                    }
                } else {
                    // recurse into generic args
                    if let Some(ref mut args) = &mut ps.args {
                        self.visit_generic_args(args);
                    }
                }
            }
        }
    }
}

struct GetMutInfo<'tcx> {
    methods: Vec<(NodeId, bool)>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'ast> Visitor<'a> for GetMutInfo<'ast> {
    fn visit_expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) => {
                // check type
                log::debug!("ty: {:#?}", utils::type_of_node_id(self.tcx, receiver.id));
            }
            _ => (),
        }
    }
}

pub fn transform<'tcx>(mut c: Crate, tcx: TyCtxt<'tcx>) -> String {
    AddImport {
        sess: ParseSess::new(FilePathMapping::empty()),
    }
    .visit_crate(&mut c);

    let mut gs = GetGhostCellifyStructs {
        ghostcellified_structs: Vec::new(),
        all_structs: Vec::new(),
        struct_generics: HashMap::new(),
    };

    gs.visit_crate(&mut c);

    let mut msg = MakeStructGraph {
        graph: HashMap::new(),
        all_structs: gs.all_structs.iter().map(|(_, i)| i.clone()).collect(),
        curr: None,
    };

    msg.visit_crate(&mut c);

    log::debug!("All structs: {:?}", msg.all_structs);
    log::debug!("graph: {:?}", msg.graph);

    // elog::debug!("struct_generics: {:#?}", gs.struct_generics);

    add_brands(
        &gs.ghostcellified_structs,
        &mut gs.struct_generics,
        &ParseSess::new(FilePathMapping::empty()),
    );

    // elog::debug!("struct_generics: {:#?}", gs.struct_generics);

    let target: HashMap<Ident, Vec<GenericParam>> = utils::propagate_params(
        msg.graph,
        gs.struct_generics,
        msg.all_structs,
        &gs.ghostcellified_structs,
    );

    let mut agp = AddGenericParams {
        target: target.clone(),
    };
    agp.visit_crate(&mut c);

    // elog::debug!("target: {:#?}", target);

    let args_target = utils::convert_param_map_to_args(&target);

    let mut aga = AddGenericArgs {
        target: args_target,
    };
    aga.visit_crate(&mut c);

    crate_to_string_for_macros(&c)
}
