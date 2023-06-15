use crate::{
    analysis::{*, span::*},
    compiler_interface::LatePass,
    rustc_ast::ast::{Attribute},
    rustc_driver,
    rustc_errors::emitter::{ColorConfig, HumanReadableErrorType},
    rustc_hir::{
        def_id::{DefId, LOCAL_CRATE},
        intravisit::FnKind,
        Generics, *,
    },
    rustc_interface,
    rustc_lint::{LateContext, LateLintPass, LintContext, LintPass},
    rustc_middle,
    rustc_middle::ty::{
        adjustment::{Adjust, AutoBorrow, PointerCast},
        TyCtxt, TypeAndMut,
    },
    rustc_session::config::ErrorOutputType,
    rustc_span::{
        sym,
        symbol::{Ident, Symbol},
        BytePos, FileName, FileNameDisplayPreference, Span,
    },
    rustc_target::spec::abi::Abi,
    types::{FnSig, Lifetime, *},
    Name,
};
use itertools::Itertools;
use std::iter::FromIterator;
use std::{collections::{HashMap, HashSet}, hash::Hash};

/// Points-to graph with strongly-connected components (SCCs)
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PointsToGraph {
    /// normal adjacency map of the points-to graph
    pub graph: HashMap<Name, HashMap<Name, Name>>,
    /// scc look-up table from struct name to SCC ID
    pub sccs: HashMap<Name, u32>,
    /// reverse scc look-up table from SCC ID to the structs it contains
    pub scc_contents: HashMap<u32, HashSet<Name>>,
    /// the points-to graph of SCCs, each edge is labeled with struct &
    /// field name (e.g. Foo::bar) to uniquely identify field names
    /// shared by multiple structs
    pub scc_graph: HashMap<u32, HashMap<(Name, Name), u32>>,
}

impl PointsToGraph {
    pub fn new() -> Self {
        PointsToGraph {
            graph: HashMap::default(),
            sccs: HashMap::default(),
            scc_contents: HashMap::default(),
            scc_graph: HashMap::default(),
        }
    }

    /// Compute an SCC that the argument belongs to using Tarjan's
    /// algorithm, this is to be called from `compute_sccs`
    fn compute_scc(
        sccs: &mut HashMap<Name, u32>,
        scc_contents: &mut HashMap<u32, HashSet<Name>>,
        graph: &HashMap<Name, HashMap<Name, Name>>,
        v: Name,
        stack: &mut Vec<Name>,
        on_stack: &mut HashSet<Name>,
        last_scc: &mut u32,
        lowlink: &mut HashMap<Name, u32>,
    ) {
        let scc = *last_scc;
        *last_scc += 1;
        sccs.insert(v.clone(), scc);
        lowlink.insert(v.clone(), scc);
        stack.push(v.clone());
        on_stack.insert(v.clone());

        // visit successors of v and compute their SCCs
        for w in graph[&v].values() {
            if !sccs.contains_key(w) {
                // recursively compute the scc for w
                Self::compute_scc(
                    sccs,
                    scc_contents,
                    graph,
                    w.clone(),
                    stack,
                    on_stack,
                    last_scc,
                    lowlink,
                );
                // update the lowlink of v, in case we ended up on a cycle through w
                *lowlink.get_mut(&v).unwrap() = lowlink[&v].min(lowlink[w]);
            } else if on_stack.contains(w) {
                // w is on the stack so it is in the current SCC (we visited it earlier!)
                *lowlink.get_mut(&v).unwrap() = lowlink[&v].min(sccs[w]);
            }
        }

        // if v is a root node (the lowlink didn't get lowered), then
        // generate an SCC
        if lowlink[&v] == scc {
            let mut nodes_in_scc = HashSet::default();
            while let Some(w) = stack.pop() {
                on_stack.remove(&w);
                *sccs.get_mut(&w).unwrap() = scc;
                if w == v {
                    break;
                }
                nodes_in_scc.insert(w);
            }
            nodes_in_scc.insert(v);
            scc_contents.insert(scc, nodes_in_scc);
        }
    }

    pub fn compute_sccs(&mut self) {
        self.sccs = HashMap::default();
        self.scc_graph = HashMap::default();

        let mut stack = Vec::new();
        let mut on_stack = HashSet::default();
        let mut last_scc = 0;
        // the lowest SCC ID that a node can point to
        let mut lowlink = HashMap::default();

        // use Tarjan's algorithm on each element to compute sccs
        for v in self.graph.keys() {
            if !self.sccs.contains_key(v) {
                Self::compute_scc(
                    &mut self.sccs,
                    &mut self.scc_contents,
                    &self.graph,
                    v.clone(),
                    &mut stack,
                    &mut on_stack,
                    &mut last_scc,
                    &mut lowlink,
                );
            }
        }

        // traverse the graph to build the SCC graph
        for (source, targets) in &self.graph {
            let target_sccs = self
                .scc_graph
                .entry(self.sccs[source])
                .or_insert(HashMap::default());
            for (field, target) in targets {
                target_sccs.insert((source.clone(), field.clone()), self.sccs[target]);
            }
        }
    }

    pub fn process_struct_def(&mut self, name: &Name, strukt: &Struct) {
        for (field, ty) in &strukt.fields {
            // TODO(maemre): also handle options, boxes, references and other references here
            let targets = self.graph.entry(name.clone()).or_insert(HashMap::default());
            if let Type::Ptr(_, box Type::Struct(target)) = ty {
                targets.insert(field.clone(), target.clone());
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StructInfo {
    /// A graph of which struct contains or points to which structs,
    /// and over which fields. For example, if we have a program
    /// fragment like,
    ///
    /// ```
    /// struct Foo {
    ///     bar: i32,
    /// }
    /// struct Baz {
    ///     quux: Foo,
    ///     jazz: * const Baz,
    /// }
    /// ```
    ///
    /// Then the contains graph will contain `[Foo -> [], Baz ->
    /// [Foo, Baz]]`.
    pub contains_graph: HashMap<Name, HashSet<Name>>,
    
    pub closure: HashMap<Name, HashSet<Name>>,
    /// A graph of HashMap<struct, parents> where `parents` are structs that contain `struct` transitively
    pub inverse_closure: HashMap<Name, HashSet<Name>>,

    pub branded_structs: HashMap<Name, Lifetime>, // (struct name, brand)

    /// The structs that occur in external API signatures
    pub occurs_in_external_apis: HashSet<Name>,

    /// A graph that tracks pointer fields, and records which field
    /// point to which other struct. The SCCs derived from this graph
    /// are used for generating lifetimes for reference fields
    pub points_to_graph: PointsToGraph,

    pub struct_defs: HashMap<Name, Struct>,
    pub enum_defs: HashMap<Name, Enum>,
    pub union_defs: HashMap<Name, Union>,
    pub type_defs: HashMap<Name, Type>,
    /// Function signatures, used for tainting structs based on
    /// whether they are involved in external APIs. The Boolean part
    /// denotes whether the function belongs to an external API or
    /// used as a function pointer.
    pub fn_sigs: HashMap<Name, (FnSig, FnFlavor)>,
    /// Internally-used mapping of named types to the types they represent to resolve syntactic types.
    type_mapping: HashMap<Name, Type>,
}

impl StructInfo {
    pub fn new() -> Self {
        StructInfo {
            contains_graph: HashMap::default(),
            closure: HashMap::default(),
            inverse_closure: HashMap::default(),
            branded_structs: HashMap::default(),
            occurs_in_external_apis: HashSet::default(),
            points_to_graph: PointsToGraph::new(),
            struct_defs: HashMap::default(),
            enum_defs: HashMap::default(),
            union_defs: HashMap::default(),
            type_defs: HashMap::default(),
            fn_sigs: HashMap::default(),
            type_mapping: HashMap::default(),
        }
    }

    /// Looks up the type with given name in all the definitions. This
    /// function clones the types defined in typedefs. Avoiding that
    /// cloning (or having a shallow clone) requires [`Type`] using an
    /// arena and references, but we are deliberately avoiding it for
    /// the sake of simplicity.
    pub fn find_type(&self, name: &Name) -> Option<Type> {
        if self.struct_defs.contains_key(name) {
            Some(Type::Struct(name.clone()))
        } else if self.enum_defs.contains_key(name) {
            Some(Type::Enum(name.clone()))
        } else if self.union_defs.contains_key(name) {
            Some(Type::Union(name.clone()))
        } else {
            self.type_defs.get(&name).map(|ty| ty.clone())
        }
    }

    /// Whether the given type name is or contains (not points to!) a union
    pub fn can_generate_default(&self, ty: &Type) -> bool {
        use Type::*;
        match ty {
            Struct(name) => self.struct_defs[name]
                .fields
                .iter()
                .all(|(_, t)| self.can_generate_default(t)),
            Union(_) => false,
            OptionT(_) => true,
            Ptr(..) => true,
            Tuple(tys) => tys.iter().all(|ty| self.can_generate_default(ty)),
            Array(inner, Some(_)) => self.can_generate_default(&**inner),
            Array(_, _) => false, // cannot generate default values for arrays with unknown size
            App(inner, _) => self.can_generate_default(&**inner),
            Unknown(path) => false,
            Unknown(_) => {
                // log::warn!("cannot generate default values for {}", ty);
                false
            }
            Bool | Char | Int(_) | Uint(_) | Float(_) => true,
            Never => false,
            _ => false,
        }
    }

    /// Walk the type and resolve syntactic types based on the type resolutions built so far
    pub fn resolve_type(&self, ty: &Type) -> Type {
        Self::resolve_syntactic_type(&self.type_mapping, ty)
    }

    /// Walk the type and resolve syntactic types that occur in it
    fn resolve_syntactic_type(type_mapping: &HashMap<Name, Type>, ty: &Type) -> Type {
        let f = |ty| Self::resolve_syntactic_type(type_mapping, ty);

        match ty {
            Type::OptionT(inner) => Type::OptionT(Box::new(f(inner))),
            Type::Tuple(fields) => Type::Tuple(fields.iter().map(f).collect()),
            Type::Array(inner, size) => Type::Array(Box::new(f(inner)), size.clone()),
            Type::Slice(inner) => Type::Slice(Box::new(f(inner))),
            Type::Fn(fn_sig) => Type::Fn(FnSig {
                param_types: fn_sig.param_types.iter().map(f).collect(),
                ret_type: Box::new(f(&*fn_sig.ret_type)),
                unsafety: fn_sig.unsafety,
                lifetime_quals: fn_sig.lifetime_quals.clone(),
                // lifetime_bounds: fn_sig.lifetime_bounds.clone(),
                c_variadic: fn_sig.c_variadic,
            }),
            Type::Ptr(mutbl, inner) => Type::Ptr(*mutbl, Box::new(f(inner))),
            Type::Ref(mutbl, lifetime, inner) => {
                Type::Ref(*mutbl, lifetime.clone(), Box::new(f(inner)))
            }
            Type::Boxed(inner) => Type::Boxed(Box::new(f(inner))),
            Type::Syntactic(v) => {
                if v.len() == 1 && type_mapping.contains_key(&v[0].name) {
                    assert!(
                        v[0].generic_args.is_empty(),
                        "Cannot apply generic arguments in {:?}. Substitutions not implemented",
                        v.iter().format("::")
                    );
                    // TODO: apply lifetime args to create struct,
                    // enum, union with appropriate lifetime info
                    type_mapping[&v[0].name].clone()
                } else {
                    if v.iter().all(|segment| {
                        segment.generic_args.is_empty() && segment.lifetime_args.is_empty()
                    }) {
                        if let Some(ty) = type_mapping
                            .get(&Name::from(v.iter().map(|s| s.to_string()).join("::")))
                        {
                            ty.clone()
                        } else {
                            Type::Unknown(v.clone())
                        }
                    } else {
                        Type::Unknown(v.clone())
                    }
                }
            }
            _ => ty.clone(),
        }
    }

    /// Match syntactic types with type or struct defs. This assumes
    /// there are no (mutually) recursive types defined with typedef
    /// (e.g. `type Foo = Option<Foo>` is illegal). After this pass
    /// there should not be any instances of [`Type::Syntactic`] in
    /// any definition.
    pub fn resolve_syntactic_types(&mut self) {
        let mut type_mapping = HashMap::default();
        for name in self.struct_defs.keys() {
            type_mapping.insert(name.clone(), Type::Struct(name.clone()));
        }
        for name in self.union_defs.keys() {
            type_mapping.insert(name.clone(), Type::Union(name.clone()));
        }
        for name in self.enum_defs.keys() {
            type_mapping.insert(name.clone(), Type::Enum(name.clone()));
        }
        for (name, ty) in &self.type_defs {
            type_mapping.insert(name.clone(), ty.clone());
        }

        // Expand RHS of type definitions until reaching a
        // fixpoint. We traverse all type defs in each iteration
        // because we don't have a reverse mapping telling us which
        // type defs are affected.
        loop {
            let mut changed = false;
            for (name, ty) in &mut self.type_defs {
                let new_ty = Self::resolve_syntactic_type(&type_mapping, ty);
                if new_ty != *ty {
                    changed = true;
                    *ty = new_ty;
                    type_mapping.insert(name.clone(), ty.clone());
                }
            }
            if !changed {
                break;
            }
        }

        for struct_ in self.struct_defs.values_mut() {
            for (_, field_ty) in struct_.fields.iter_mut() {
                *field_ty = Self::resolve_syntactic_type(&type_mapping, field_ty);
            }
        }

        for struct_ in self
            .enum_defs
            .values_mut()
            .flat_map(|e| e.variants.iter_mut())
        {
            for (_, field_ty) in struct_.fields.iter_mut() {
                *field_ty = Self::resolve_syntactic_type(&type_mapping, field_ty);
            }
        }

        self.fn_sigs.values_mut().for_each(|(fn_sig, _)| {
            if let Type::Fn(new_sig) =
                Self::resolve_syntactic_type(&type_mapping, &Type::Fn(fn_sig.clone()))
            {
                *fn_sig = new_sig;
            } else {
                unimplemented!("resolving a function type should yield a function type");
            }
        });

        // save the type mapping
        self.type_mapping = type_mapping;
    }

    /// Build the dependency graph between structs and enums. This is
    /// used for finding recursive types for lifetime annotation.
    pub fn compute_struct_dependencies(&mut self) {
        fn collect_mentioned_types(names: &mut HashSet<Name>, ty: &Type) {
            use Type::*;

            let mut f = |ty| collect_mentioned_types(names, ty);

            match ty {
                Struct(name) => {
                    names.insert(name.clone());
                }
                Enum(name) => {
                    names.insert(name.clone());
                }
                Union(name) => {
                    names.insert(name.clone());
                }
                OptionT(inner) => f(inner),
                Tuple(fields) => fields.iter().for_each(f),
                Array(inner, _) => f(inner),
                Slice(inner) => f(inner),
                Fn(FnSig {
                    param_types,
                    ret_type,
                    ..
                }) => {
                    param_types.iter().for_each(&mut f);
                    f(ret_type)
                }
                Ptr(_, inner) => f(inner),
                Ref(_, _, inner) => f(inner),
                Boxed(inner) => f(inner),
                Generic(outer, inner_tys) => {
                    f(outer);
                    inner_tys.iter().for_each(f);
                }
                Syntactic(_v) => panic!("There should not be any syntactic types at this stage"),
                _ => {}
            };
        }

        for (name, struct_) in &self.struct_defs {
            let mut names = HashSet::default();
            struct_
                .fields
                .iter()
                .for_each(|(_, ty)| collect_mentioned_types(&mut names, ty));
            self.contains_graph.insert(name.clone(), names);
            self.points_to_graph.process_struct_def(name, struct_);
        }

        // Compute the transitive closure of contains_graph
        for container in self
            .contains_graph
            .keys()
            .map(|l| l.clone())
            .collect::<Vec<Name>>()
        {
            let mut worklist = self.contains_graph[&container]
                .iter()
                .map(|l| l.clone())
                .collect::<Vec<Name>>();
            let mut visited: HashSet<Name> = HashSet::default();

            while let Some(contained) = worklist.pop() {
                if self.contains_graph.contains_key(&contained) {
                    for child in &self.contains_graph[&contained] {
                        if !visited.contains(child) {
                            worklist.push(child.clone());
                        }
                    }
                }
                visited.insert(contained);
            }
            self.contains_graph
                .get_mut(&container)
                .unwrap()
                .extend(visited);
        }

        self.points_to_graph.compute_sccs();
    }

    pub fn compute_occurs_in_external_apis(&mut self, fn_ptr_types: &Vec<Type>) {
        let resolved_fn_ptr_types = fn_ptr_types
            .iter()
            .map(|ty| self.resolve_type(ty))
            .collect::<Vec<Type>>();
        let occur_set = &mut self.occurs_in_external_apis;
        let contains_graph = &self.contains_graph;
        let mut poison_occurring_structs = |ty: &Type| {
            for struct_name in ty.collect_structs() {
                // TODO: also poison structs transitively pointed to by this struct
                contains_graph[&struct_name].iter().for_each(|name| {
                    occur_set.insert(name.clone());
                });
                occur_set.insert(struct_name);
            }
        };

        for (sig, flavor) in self.fn_sigs.values() {
            if *flavor != FnFlavor::Normal {
                sig.param_types
                    .iter()
                    .for_each(&mut poison_occurring_structs);
                poison_occurring_structs(&sig.ret_type);
            }
        }

        for ty in resolved_fn_ptr_types {
            if let Type::Fn(sig) = ty {
                sig.param_types
                    .iter()
                    .for_each(&mut poison_occurring_structs);
                poison_occurring_structs(&sig.ret_type);
            } else {
                unreachable!();
            }
        }
    }

    pub fn brands(&self, name: &Name) -> HashSet<Lifetime> {
        let default =  HashSet::default();
        let children = self.closure.get(name).unwrap_or(&default);

        // get children which are in branded structs
        let children: HashSet<Name> = children
            .iter()
            .filter_map(|child| self.branded_structs.get(child))
            .map(|c| c.clone())
            .collect::<HashSet<_>>();

        children
    }

}

impl AnalysisResult for StructInfo {
    fn name() -> String {
        "StructInfo".to_owned()
    }
}

/// A pass to discover points-to relations between structs and use of
/// structs and fields in different contexts.
pub struct StructInfoPass {
    info: StructInfo,
    /// Call graph built by pointer provenance
    /// *Syntactic* function pointer types seen in the program, used
    /// for marking the types inside them as used in external APIs.
    fn_ptr_types: Vec<Type>,
}

impl StructInfoPass {
    pub fn new<'tcx>(_: TyCtxt<'tcx>) -> Box<LatePass> {
        Box::new(StructInfoPass {
            info: StructInfo::new(),
            fn_ptr_types: Vec::new(),
        })
    }

    fn process_union(&mut self, name: Name) {
        self.info
            .union_defs
            .insert(name.clone(), Union { name: name });
    }

    fn process_struct<'tcx>(
        &mut self,
        ctx: &LateContext<'tcx>,
        name: Name,
        fields: &'tcx [FieldDef<'tcx>],
        generics: &'tcx Generics<'tcx>,
        should_brand: bool,
    ) {
        // add struct to branded_structs
        if should_brand {
            self.info.branded_structs.insert(name.clone(), Lifetime::from(format!("id{}", 0)));
        }

        let mut lifetime_bounds = Vec::new();

        // verify & extract generics
        let lifetime_quals = generics
            .params
            .iter()
            .filter_map(|param| match &param.kind {
                GenericParamKind::Lifetime { .. } => {
                    let param_name = Name::from(&*param.name.ident().name.as_str());
                    process_bounds(
                        ctx,
                        &mut lifetime_bounds,
                        &name,
                        &param_name,
                        generics.bounds_for_param(param.def_id),
                    );
                    Some(param_name)
                }
                _ => None,
            })
            .collect::<Vec<Lifetime>>();

        // extract bounds from side constraints
        for predicate in generics.predicates {
            use WherePredicate::*;
            match predicate {
                RegionPredicate(pred) => {
                    if let Some(lhs) = extract_lifetime_name(ctx, &pred.lifetime.res) {
                        process_bound(pred.bounds, ctx, &mut lifetime_bounds, &name, &lhs);
                    }
                }
                BoundPredicate(..) => {}
                _ => panic!(
                    "found unsupported where predicate in struct {} at {:?}",
                    name,
                    predicate.span()
                ),
            }
        }

        // process fields
        let fields = fields
            .iter()
            .map(|field| {
                let field_name = Name::from(&*field.ident.name.as_str());

                // Because typeck results are not available outside
                // bodies, we are using syntactic types to construct the
                // type of this field.
                let field_ty = Type::from_hir_ty(ctx, field.ty);

                (field_name, field_ty)
            })
            .collect();

        self.info.struct_defs.insert(
            name.clone(),
            Struct {
                name: name,
                lifetime_quals: lifetime_quals,
                lifetime_bounds: lifetime_bounds,
                fields: fields,
            },
        );
    }

    fn process_enum(&mut self, _name: Name, _enum_def: &EnumDef<'_>, _generics: &Generics<'_>) {
        todo!();
    }

    fn process_typedef(
        &mut self,
        ctx: &LateContext<'_>,
        name: Name,
        ty: &rustc_hir::Ty<'_>,
        generics: &Generics<'_>,
    ) {
        // assert!(
        //     generics.params.is_empty(),
        //     "typedef has generics at {:?}",
        //     ty.span
        // );
        self.info.type_defs.insert(name, Type::from_hir_ty(ctx, ty));
    }

    fn process_fn(
        &mut self,
        ctx: &LateContext<'_>,
        name: Name,
        fn_decl: &FnDecl<'_>,
        generics: &Generics<'_>,
        unsafety: Unsafety,
        is_foreign: bool,
    ) {
        let mut lifetime_bounds = Vec::new();

        // Extract existing lifetime bounds of a given lifetime from
        // the program
        let mut process_bounds = |lhs: &Name, generic_bounds: GenericBounds| {
            for bound in generic_bounds {
                match bound {
                    GenericBound::Outlives(rhs) => {
                        if let Some(rhs) = extract_lifetime_name(ctx, &rhs.res) {
                            lifetime_bounds.push((lhs.clone(), rhs))
                        }
                    }
                    _ => panic!("Unsupported generic bound in function {}", name),
                }
            }
        };

        // verify & extract generics
        let lifetime_quals = generics
            .params
            .iter()
            .filter_map(|param| match &param.kind {
                GenericParamKind::Lifetime { .. } => {
                    let param_name = Name::from(&*param.name.ident().name.as_str());

                    // process_bounds(&param_name, &param.bounds);
                    Some(param_name)
                }
                _ => {
                    log::debug!("found non-lifetime generics parameter in function {}", name);
                    None
                }
            })
            .collect::<Vec<Lifetime>>();

        // extract bounds from side constraints
        for predicate in generics.predicates {
            use WherePredicate::*;
            match predicate {
                RegionPredicate(pred) => {
                    if let Some(lhs) = extract_lifetime_name(ctx, &pred.lifetime.res) {
                        process_bounds(&lhs, &pred.bounds);
                    }
                }
                BoundPredicate(..) => {}
                _ => panic!(
                    "found unsupported where predicate in function {} at {:?}",
                    name,
                    predicate.span()
                ),
            }
        }

        let ret_type = match &fn_decl.output {
            FnRetTy::Return(ty) => Box::new(Type::from_hir_ty(ctx, ty)),
            FnRetTy::DefaultReturn(_) => {
                // since this function is not a closure, the default
                // return type is ()
                Box::new(Type::Tuple(vec![]))
            }
        };

        let param_types = fn_decl
            .inputs
            .iter()
            .map(|ty| Type::from_hir_ty(ctx, ty))
            .collect();

        self.info.fn_sigs.insert(
            name,
            (
                FnSig {
                    unsafety: unsafety,
                    lifetime_quals: lifetime_quals,
                    // lifetime_bounds: lifetime_bounds,
                    param_types: param_types,
                    ret_type: ret_type,
                    c_variadic: fn_decl.c_variadic,
                },
                FnFlavor::Normal,
            ),
        );
    }

    pub fn compute_closure(&mut self)  {
        let mut cg = &mut self.info.contains_graph;

        // iter over type defs, collect structs and map to a hashset
        let mut type_defs : HashMap<Name, HashSet<Name>> = HashMap::default();
        for (name, ty) in &self.info.type_defs {
            let v = ty.collect_structs();
            let vset = v.iter().cloned().collect();
            type_defs.insert(name.clone(), vset);
        }

        // log::warn!("type_defs: {:#?}", type_defs);

        for (name, ty) in &type_defs {
            if let Some(targets) = type_defs.get(&name) {
                    cg.insert(name.clone(), targets.clone());
            }
        }
        

        let mut closure: HashMap<Name, HashSet<Name>> = HashMap::default();
        for (source, targets) in &self.info.contains_graph {
            let mut visited = HashSet::default();
            let mut stack = vec![source.clone()];
            while let Some(v) = stack.pop() {
                if !visited.contains(&v) {
                    visited.insert(v.clone());
                    if let Some(targets) = self.info.contains_graph.get(&v) {
                        stack.extend(targets.clone());
                    }
                }
            }
            closure.insert(source.clone(), visited);
        }
        
        for (source, targets) in &type_defs {
            let mut visited = HashSet::default();
            let mut stack = vec![source.clone()];
            while let Some(v) = stack.pop() {
                if !visited.contains(&v) {
                    visited.insert(v.clone());
                    if let Some(targets) = self.info.contains_graph.get(&v) {
                        stack.extend(targets.clone());
                    }
                }
            }
            closure.insert(source.clone(), visited);
        }

        // compute the inverse closure
        let mut inverse_closure: HashMap<Name, HashSet<Name>> = HashMap::default();
        for (source, targets) in &closure {
            for target in targets {
                let inverse_targets = inverse_closure.entry(target.clone()).or_insert(HashSet::default());
                inverse_targets.insert(source.clone());
            }
        }

        self.info.closure = closure;
        self.info.inverse_closure = inverse_closure;
    }
}

impl LintPass for StructInfoPass {
    fn name(&self) -> &'static str {
        "StructInfoPass"
    }
}

impl<'tcx> LateLintPass<'tcx> for StructInfoPass {
    fn check_item_post(&mut self, ctx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        // Get the name only when necessary.
        let name = || Name::from(qname_from_hir(ctx, item.hir_id()));

        match &item.kind {
            ItemKind::Enum(enum_def, generics) => {
                self.process_enum(name(), enum_def, generics);
            }
            ItemKind::Struct(data, generics) => {
                let attrs = ctx.tcx.hir().attrs(item.hir_id());
                let should_brand = attrs.iter().any(|attr| { attr_contains(ctx, attr, "ghostcellify") });
                self.process_struct(ctx, name(), data.fields(), generics, should_brand);
            }
            ItemKind::Union(_fields, _generics) => {
                self.process_union(name());
            }
            ItemKind::TyAlias(ty, generics) => {
                self.process_typedef(ctx, name(), ty, generics);
            }
            _ => {} // ignore other item kinds
        }
    }

    fn check_foreign_item(&mut self, ctx: &LateContext<'tcx>, item: &'tcx ForeignItem<'tcx>) {
        use ForeignItemKind::*;
        let name = || Name::from(qname_from_hir(ctx, item.hir_id()));

        match &item.kind {
            Fn(fn_decl, _param_names, generics) => {
                // process foreign function declarations
                self.process_fn(ctx, name(), fn_decl, generics, Unsafety::Unsafe, true);
            }
            Static(..) => {} // skip static variables
            Type => {}       // skip foreign types, they will be marked unknown by the analysis
        }
    }

    fn check_fn(
        &mut self,
        ctx: &LateContext<'tcx>,
        kind: FnKind<'tcx>,
        decl: &'tcx FnDecl<'tcx>,
        body: &'tcx Body<'tcx>,
        span: Span,
        hir_id: HirId,
    ) {
        // A function has a type, it also has parameters as part of
        // its body. For now, we do not touch parameters, but we may
        // need to modify them in later passes & we need to build a
        // local context out of variables that appear in parameter
        // patterns.

        // Get the name only when necessary.

        let name = || Name::from(qname_from_hir(ctx, hir_id));

        match kind {
            FnKind::ItemFn(_, generics, header) => {
                let name = name();
                // skip the bitfield helpers we added
                if !name.contains("::bitfields") {
                    self.process_fn(ctx, name, decl, generics, header.unsafety, false);
                }
            }
            FnKind::Method(..) => {
                let name = name();
                // skip the bitfield helpers we added
                if !name.contains("::bitfields") && !name.contains("::xmlschemastypes") {
                    // todo!("methods are not processed yet: {:?}", decl);
                }
            }
            FnKind::Closure => {
                // todo!("closures are not processed yet: {:?}", decl);
            }
        }
    }

    fn check_ty(&mut self, ctx: &LateContext<'tcx>, ty: &'tcx rustc_hir::Ty<'tcx>) {
        if matches!(ty.kind, TyKind::BareFn(..)) {
            // This is a function pointer, remember it.
            self.fn_ptr_types.push(Type::from_hir_ty(ctx, ty))
        }
    }

    fn check_crate(&mut self, ctx: &LateContext<'tcx>) {
        *CRATE_NAME.lock().unwrap() = Name::from(ctx.tcx.crate_name(LOCAL_CRATE).to_string());

        log::debug!("crate {:#?}", ctx.tcx.hir().krate());
    }

    fn check_crate_post(&mut self, _: &LateContext<'tcx>) {
        self.info.resolve_syntactic_types();
        self.info.compute_struct_dependencies();
        self.compute_closure();
        self.info
            .compute_occurs_in_external_apis(&self.fn_ptr_types);

        // Update analysis results
        replace::<StructInfo>(Box::new(self.info.clone()));
    }
}

pub fn process_bounds<'tcx>(
    ctx: &LateContext<'tcx>,
    lifetime_bounds: &mut Vec<(Lifetime, Lifetime)>,
    name: &Name,
    lhs: &Name,
    preds: impl Iterator<Item = &'tcx WhereBoundPredicate<'tcx>>,
) {
    for pred in preds {
        process_bound(pred.bounds, ctx, lifetime_bounds, lhs, name);
    }
}

pub fn process_bound<'tcx>(
    bounds: GenericBounds<'tcx>,
    ctx: &LateContext<'tcx>,
    lifetime_bounds: &mut Vec<(Lifetime, Lifetime)>,
    lhs: &Name,
    name: &Name,
) {
    for bound in bounds.into_iter() {
        match bound {
            GenericBound::Outlives(rhs) => {
                if let Some(rhs) = extract_lifetime_name(ctx, &rhs.res) {
                    lifetime_bounds.push((lhs.clone(), rhs))
                }
            }
            _ => panic!("Unsupported generic bound in struct {}", name),
        }
    }
}