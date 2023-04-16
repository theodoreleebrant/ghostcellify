use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    analysis::{self, span::{qname_from_hir, qname}}, 
    types::*,
    Name, 
    rustc_lint::{LateContext, LateLintPass, LintPass},
    rustc_ast::ast::LitKind,
    rustc_hir::{
        def::{DefKind, Res},
        intravisit::FnKind,
        *,
    },
    rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind, TypeAndMut},
    rustc_span::{symbol::Ident, Span, def_id::{DefId, LOCAL_CRATE}},
    compiler_interface::LatePass, 
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
/// Different kinds of unsafe behavior we can extract syntactically
pub enum UnsafeBehavior {
    /// Reading a fields from untagged unions
    ReadFromUnion,
    /// Accessing a mutable global/static variable
    MutGlobalAccess,
    /// Inline assembly
    InlineAsm,
    /// Calling external functions, or unsafe fn pointers
    ExternCall,
    /// Raw pointer dereference
    RawPtrDeref,
    /// Unsafe casting by calling `mem::transmute`
    UnsafeCast,
    /// Memory allocation/deallocation by calling `malloc` and `free` directly
    Alloc,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Call graph, does not handle trait methods yet.
pub struct CallGraph {
    /// Holds the callees of each function. This is the ground truth
    /// for the call graph, all the other parts of the graph are
    /// computed from this.
    callees: HashMap<Name, HashSet<Name>>,
    /// Holds the callers of each function
    callers: HashMap<Name, HashSet<Name>>,
    /// Holds the transitive closure of the call graph
    pub closure: HashMap<Name, HashSet<Name>>,
    /// Holds the transitive closure of callers, for inverse lookup
    inverse_closure: HashMap<Name, HashSet<Name>>,
    /// Whether the closure is no longer valid
    dirty: bool,
    /// Whether a function has certain types of code we don't handle
    unsafe_behavior: HashMap<Name, BTreeSet<UnsafeBehavior>>,
    /// Count of static occurrences of different unsafe behavior
    ub_count: BTreeMap<UnsafeBehavior, usize>,
    pub defined_fns: HashSet<Name>,
    /// Extern functions declared in the program
    pub extern_fns: HashSet<Name>,
    /// Calls to functions whose extern status are not resolved yet
    /// (excluding calls to function pointers). We use this during the
    /// online building of initial call graph.
    unresolved_calls: Vec<(Name, Name)>,
    /// Functions that are used as function pointers
    pub used_as_fn_pointer: HashSet<Name>,
}

impl CallGraph {
    pub fn new() -> Self {
        CallGraph {
            callees: HashMap::default(),
            callers: HashMap::default(),
            closure: HashMap::default(),
            inverse_closure: HashMap::default(),
            dirty: false,
            unsafe_behavior: HashMap::default(),
            ub_count: BTreeMap::new(),
            defined_fns: HashSet::default(),
            extern_fns: HashSet::default(),
            unresolved_calls: Vec::new(),
            used_as_fn_pointer: HashSet::default(),
        }
    }

    /// Add this function declaration to relevant maps
    pub fn add_fn_decl(&mut self, fn_name: Name) {
        self.unsafe_behavior.insert(fn_name, BTreeSet::new());
    }

    pub fn add_unsafe_behavior(&mut self, fn_name: &Name, ub: UnsafeBehavior) {
        // also increment the counter
        *self.ub_count.entry(ub).or_insert(0) += 1;

        if !self.unsafe_behavior.contains_key(fn_name) {
            self.unsafe_behavior
                .insert(fn_name.clone(), BTreeSet::new());
        }

        self.unsafe_behavior.get_mut(fn_name).unwrap().insert(ub);
    }

    pub fn unsafe_behavior(&self) -> &HashMap<Name, BTreeSet<UnsafeBehavior>> {
        &self.unsafe_behavior
    }

    pub fn ub_count(&self) -> &BTreeMap<UnsafeBehavior, usize> {
        &self.ub_count
    }

    pub fn transitive_callers(&self) -> Option<&HashMap<Name, HashSet<Name>>> {
        if self.dirty {
            None
        } else {
            Some(&self.inverse_closure)
        }
    }

    pub fn callees(&self) -> &HashMap<Name, HashSet<Name>> {
        &self.callees
    }

    pub fn callers(&self) -> &HashMap<Name, HashSet<Name>> {
        &self.callers
    }

    pub fn closure(&self) -> Option<&HashMap<Name, HashSet<Name>>> {
        if self.dirty {
            None
        } else {
            Some(&self.closure)
        }
    }

    pub fn inverse_closure(&self) -> Option<&HashMap<Name, HashSet<Name>>> {
        if self.dirty {
            None
        } else {
            Some(&self.inverse_closure)
        }
    }

    /// Add given call edge. The parameter `is_special` should be set
    /// if the callee is a special extern function we handle (e.g. `malloc`).
    pub fn add_call(&mut self, caller: Name, callee: Name, is_special: bool) {
        // TODO: take a reference and avoid copying unless necessary

        self.dirty = self
            .callees
            .entry(caller)
            .or_insert_with(HashSet::default)
            .insert(callee)
            || self.dirty;
    }

    pub fn compute_closure(&mut self) {
        if !self.dirty {
            return;
        }

        // at this point, all callees should be resolved, go through unresolved calls and resolve them
        for (caller, callee) in std::mem::take(&mut self.unresolved_calls) {
            let unqual_callee = Name::from(callee.rsplit_once("::").unwrap().1);
            if self.extern_fns.contains(&unqual_callee) {
                self.add_unsafe_behavior(&caller, UnsafeBehavior::ExternCall);
            }

            // insert the missing call edge
            let real_callee = self
                .defined_fns
                .get(&unqual_callee)
                .cloned()
                .unwrap_or(callee);
            self.dirty = self
                .callees
                .entry(caller)
                .or_insert_with(HashSet::default)
                .insert(real_callee)
                || self.dirty;
        }

        let fns: HashSet<&Name> = {
            let mut fns = HashSet::default();

            for (f, gs) in self.callees.iter() {
                fns.insert(f);
                fns.extend(gs);
            }

            fns
        };

        for f in fns.into_iter() {
            if let Some(callees) = self.callees.get(f) {
                let mut worklist = callees.iter().map(|n| n.clone()).collect::<Vec<Name>>();
                let mut seen = HashSet::default();

                while let Some(g) = worklist.pop() {
                    seen.insert(g.clone());

                    for h in self.callees.get(&g).into_iter().flatten() {
                        if !seen.contains(h) {
                            worklist.push(h.clone());
                        }
                    }
                }

                // Put the computed result in the closure map
                self.closure.insert(f.clone(), seen);
            } else {
                self.closure.insert(f.clone(), HashSet::default());
            }
        }

        // build the caller graph
        for (caller, callees) in &self.callees {
            for callee in callees {
                self.callers
                    .entry(callee.clone())
                    .or_insert(HashSet::default())
                    .insert(caller.clone());
            }
        }
        for caller in self.closure.keys() {
            // create empty entries for the callers too
            self.callers
                .entry(caller.clone())
                .or_insert(HashSet::default());
        }

        // build inverse closure
        for (caller, callees) in &self.closure {
            for callee in callees {
                self.inverse_closure
                    .entry(callee.clone())
                    .or_insert(HashSet::default())
                    .insert(caller.clone());
            }
        }

        // propagate unsafe behavior to the closure
        for (callee, callers) in &self.inverse_closure {
            if let Some(ubs) = self.unsafe_behavior.get(callee).cloned() {
                if ubs.is_empty() {
                    continue;
                }
                for caller in callers {
                    self.unsafe_behavior
                        .entry(caller.clone())
                        .or_insert(BTreeSet::new())
                        .extend(ubs.clone().into_iter());
                }
            }
        }

        self.dirty = false;
    }
}

impl analysis::AnalysisResult for CallGraph {
    fn name() -> String {
        "CallGraph".to_owned()
    }
}

pub struct CallGraphPass {
    callgraph: CallGraph,
    fn_name: Name,
}

impl CallGraphPass {
    pub fn new<'tcx>(_tcx: TyCtxt<'tcx>) -> std::boxed::Box<(dyn LateLintPass<'tcx> + 'tcx)> {
        Box::new(CallGraphPass {
            callgraph: CallGraph::new(),
            fn_name: Name::from(""),
        })
    }

    // fn analyze_expr<'a, 'tcx>(
    //     &mut self,
    //     ctx: &LateContext<'tcx>,
    //     expr: &'tcx Expr<'tcx>,
    // ) {
    //     match &expr.kind {
    //         E
    //     }
    // }

    // fn analyze_body<'tcx>(
    //     &mut self,
    //     fn_name: Name,
    //     Body { params, value, .. }: &'tcx Body<'tcx>,
    //     ctx: &LateContext<'tcx>,
    //     is_main: bool,
    // ) {
    //     self.fn_name = fn_name;
    //     self.analyze_expr(&ctx, &value);
    // }
}

impl LintPass for CallGraphPass {
    fn name(&self) -> &'static str {
        "CallGraphPass"
    }
}

impl<'tcx> LateLintPass<'tcx> for CallGraphPass {
    fn check_expr_post(&mut self, ctx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = &expr.kind {
            if let ExprKind::Path(qpath) = &callee.kind {
                if let Some(def_id) = ctx.qpath_res(qpath, callee.hir_id).opt_def_id() {
                    let callee_name = Name::from(qname(ctx, def_id));
                    self.callgraph.add_call(self.fn_name.clone(), callee_name, false);
                }
            }
        }

        // method calls
        if let ExprKind::MethodCall(path, span, args, _) = &expr.kind {
            if let Some(def_id) = ctx.typeck_results().type_dependent_def_id(expr.hir_id) {
                let callee_name = Name::from(qname(ctx, def_id));
                self.callgraph.add_call(self.fn_name.clone(), callee_name, false);
            }
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
        if matches!(kind, FnKind::Closure) {
            return;
        }

        let def_qname = qname_from_hir(ctx, hir_id);

        self.callgraph
            .defined_fns
            .insert(Name::from(&*def_qname));

        if span.in_derive_expansion() {
            return;
        }

        let fn_name: Name = def_qname.into();

        // add this function to the relevant parts of call graph
        self.callgraph.add_fn_decl(fn_name.clone());

        self.fn_name = fn_name.clone();

        // self.analyze_body(def_qname.into(), body, ctx, is_main);
    }

    fn check_crate_post(&mut self, _: &LateContext<'tcx>) {
        self.callgraph.compute_closure();
        analysis::replace::<CallGraph>(Box::new(self.callgraph.clone()));
    }
}
