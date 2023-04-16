use std::cell::Ref;
use std::collections::{HashMap, HashSet};

use rustc_ast::ast::*;
use rustc_ast::ptr::P;
use rustc_parse::parser::{ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::symbol::Ident;
use rustc_span::FileName;
use rustc_span::Symbol;
use std::ops::Add;
extern crate thin_vec;
use rustc_ast::visit::Visitor;
use rustc_middle::ty::TyCtxt;
use std::cmp::Ordering::{self, *};

fn gen_parser<'a, 'b>(str: &'b str, sess: &'a ParseSess) -> Parser<'a> {
    // let sess = ParseSess::new(FilePathMapping::empty());
    let tokens =
        rustc_parse::parse_stream_from_source_str(FileName::Anon(0), str.to_string(), &sess, None);
    let mut parser = Parser::new(sess, tokens, false, None);
    parser
}

pub fn parse_item(str: &str, sess: &ParseSess) -> P<Item> {
    let mut parser = gen_parser(str, sess);
    match parser.parse_item(ForceCollect::Yes).unwrap() {
        Some(item) => item,
        None => panic!("parse_item: Expected item when parsing {str}, got None"),
    }
}

fn make_generic_param(uid: usize, parent_id: NodeId) -> GenericParam {
    GenericParam {
        id: parent_id.clone(),
        ident: Ident::from_str(&format!("'id{}", uid)),
        attrs: thin_vec::ThinVec::new(),
        bounds: Vec::new(),
        is_placeholder: false,
        kind: GenericParamKind::Lifetime,
        colon_span: None,
    }
}

pub fn eq_str_ident(s: &str, i: &Ident) -> bool {
    let dummy_ident = Ident::from_str(s);
    i.name == dummy_ident.name
}

// TODO: ghostcellify or ghostcellify#0 ?
pub fn path_contains_ghostcellify(path: &Path) -> bool {
    for segment in &path.segments {
        if eq_str_ident("ghostcellify", &segment.ident) {
            return true;
        }
    }
    false
}

pub fn attribute_contains_ghostcellify(attr: Attribute) -> bool {
    match attr.kind {
        AttrKind::Normal(inner) => path_contains_ghostcellify(&inner.into_inner().item.path),
        _ => false,
    }
}

pub fn item_contains_ghostcellify(item: &Item) -> bool {
    for attr in &item.attrs {
        if attribute_contains_ghostcellify(attr.clone()) {
            return true;
        }
    }
    false
}

pub fn add_brands(
    ghostcellified_structs: &Vec<(NodeId, Ident)>,
    struct_generics: &mut HashMap<Ident, Vec<GenericParam>>,
    parse_sess: &ParseSess,
) {
    for (i, (id, ident)) in ghostcellified_structs.iter().enumerate() {
        let params = struct_generics.get_mut(ident).unwrap();
        let brand = make_generic_param(i, *id);
        params.insert(0, brand);
    }
}

pub fn propagate_params(
    graph: HashMap<Ident, Vec<Ident>>,
    struct_params: HashMap<Ident, Vec<GenericParam>>,
    structs: Vec<Ident>,
    branded_structs: &Vec<(NodeId, Ident)>,
) -> HashMap<Ident, Vec<GenericParam>> {
    pub fn sort_generic_hashmap(
        map: &mut HashMap<Ident, Vec<GenericParam>>,
        branded_structs: &Vec<(NodeId, Ident)>,
    ) {
        for (ident, params) in map {
            let uid = branded_structs.iter().position(|&(_, sid)| sid == *ident);
            params.sort_by(|a, b| compare_generics(a, b, uid));
        }
    }

    fn eq_generic_param(gp1: &GenericParam, gp2: &GenericParam) -> bool {
        gp1.ident.name == gp2.ident.name
    }

    fn contains_gp(gp_vec: &Vec<GenericParam>, gp: &GenericParam) -> bool {
        gp_vec.iter().any(|gp2| eq_generic_param(gp2, gp))
    }

    fn propagate(
        graph: &HashMap<Ident, Vec<Ident>>,
        struct_params: HashMap<Ident, Vec<GenericParam>>,
        structs: Vec<Ident>,
        branded_structs: &Vec<(NodeId, Ident)>,
    ) -> HashMap<Ident, Vec<GenericParam>> {
        fn traverse_update(
            parent_graph: &mut HashMap<Ident, Vec<Ident>>,
            start_node: Ident,
            res: &mut HashMap<Ident, Vec<GenericParam>>,
        ) {
            let mut visited = HashSet::new();
            visited.insert(start_node.clone());
            let mut stack = vec![start_node];

            while !stack.is_empty() {
                let curr = stack.pop().unwrap(); // Will not panic: guarantee in line above
                for parent in parent_graph.get(&curr).unwrap_or(&mut Vec::new()) {
                    if visited.contains(parent) {
                        continue;
                    } else {
                        let [par_params, curr_params] = res
                            .get_many_mut([parent, &curr])
                            .expect("cannot get both parent and curr");
                        for curr_param in curr_params {
                            if !contains_gp(par_params, curr_param) {
                                par_params.push(curr_param.clone());
                            }
                        }
                    }
                    visited.insert(parent.clone());
                    stack.push(parent.clone());
                }
            }
        }

        fn gen_par_graph(
            nodes: Vec<Ident>,
            graph: &HashMap<Ident, Vec<Ident>>,
        ) -> HashMap<Ident, Vec<Ident>> {
            let mut res = HashMap::new();
            for node in nodes {
                res.insert(node, Vec::new());
            }
            for (node, neighbors) in graph {
                for neighbor in neighbors {
                    res.get_mut(neighbor).unwrap().push(node.clone());
                }
            }
            res
        }

        let mut parent_graph = gen_par_graph(structs.clone(), graph);
        // let leaves = get_leaves(graph);
        let mut res = struct_params.clone();

        for node in structs {
            traverse_update(&mut parent_graph, node, &mut res);
        }

        sort_generic_hashmap(&mut res, branded_structs);
        res
    }

    propagate(&graph, struct_params, structs, branded_structs)
}

pub fn compare_generics(a: &GenericParam, b: &GenericParam, uid: Option<usize>) -> Ordering {
    fn is_brand(gp: &GenericParam) -> bool {
        match gp.kind {
            GenericParamKind::Lifetime => gp.ident.name.as_str().starts_with("'id"),
            _ => false,
        }
    }

    fn inner_compare(a: &GenericParam, b: &GenericParam) -> Ordering {
        match (is_brand(a), is_brand(b)) {
            (true, true) => {
                return Symbol::cmp(&a.ident.name, &b.ident.name);
            }
            (true, false) => return Less,
            (false, true) => return Greater,
            (false, false) => return Equal,
        }
    }

    match (&a.kind, &b.kind) {
        (GenericParamKind::Lifetime, GenericParamKind::Lifetime) => match uid {
            Some(inner) => {
                let curr_brand = make_generic_param(inner, NodeId::from_usize(inner));
                if a.ident == curr_brand.ident {
                    return Less;
                } else if b.ident == curr_brand.ident {
                    return Greater;
                } else {
                    return inner_compare(a, b);
                }
            }
            None => {
                return inner_compare(a, b);
            }
        },
        (GenericParamKind::Lifetime, _) => Less,
        (_, GenericParamKind::Lifetime) => Greater,
        (_, _) => Equal,
    }
}

pub fn convert_param_to_arg(param: &GenericParam) -> Option<GenericArg> {
    match &param.kind {
        GenericParamKind::Lifetime => Some(GenericArg::Lifetime(Lifetime {
            id: param.id,
            ident: param.ident,
        })),
        GenericParamKind::Type { default } => match default {
            Some(ty) => Some(GenericArg::Type(ty.clone())),
            None => None,
        },
        _ => None,
    }
}

pub fn convert_param_map_to_args(
    params: &HashMap<Ident, Vec<GenericParam>>,
) -> HashMap<Ident, Vec<GenericArg>> {
    let mut res: HashMap<Ident, Vec<GenericArg>> = HashMap::new();
    for (ident, params) in params {
        let mut args = Vec::new();
        for param in params {
            if let Some(arg) = convert_param_to_arg(&param) {
                args.push(arg);
            }
        }
        res.insert(ident.clone(), args);
    }
    res
}

pub fn brand_in_ty<'ast>(map: &'ast HashMap<Ident, Vec<GenericParam>>, ty: &Ty) -> Option<Ident> {
    struct TyVisitor<'ast> {
        map: &'ast HashMap<Ident, Vec<GenericParam>>,
        found: Option<Ident>,
    }
    impl<'ast> Visitor<'ast> for TyVisitor<'ast> {
        fn visit_path_segment(&mut self, seg: &'ast PathSegment) {
            if self.map.contains_key(&seg.ident) {
                self.found = Some(seg.ident.clone());
            }
        }
    }

    let mut visitor = TyVisitor { map, found: None };
    visitor.visit_ty(ty);
    visitor.found
}

pub fn type_of_node_id<'ast>(tcx: TyCtxt<'ast>, node_id: NodeId) -> rustc_middle::ty::Ty<'ast> {
    let resolver = tcx.resolver_for_lowering(()).borrow();
    let resolver = Ref::leak(resolver);
    let node_id_to_def_id = &resolver.node_id_to_def_id;
    let local_def_id = node_id_to_def_id.get(&node_id).unwrap();
    let def_id = local_def_id.to_def_id();
    let ty = tcx.type_of(def_id);
    ty
}
