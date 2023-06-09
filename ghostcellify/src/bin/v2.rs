#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(str_split_once)]

extern crate env_logger;

use crate::def_id::{DefId, LOCAL_CRATE};
use ghostcelltf::{
    analysis,
    analysis::span::*,
    rustfix_utils,
    colored::*,
    constants::*,
    compiler_interface::*,
    io::{FileIO, OutputMode},
    lazy_static::lazy_static,
    passes::{callgraph::*, struct_info::*, token_analysis::*, lifetime_rewrite::LifetimeRewritePass},
    rustc_driver,
    rustc_hir::{intravisit::FnKind, *},
    rustc_lint::{LateContext, LateLintPass, LintContext, LintPass},
    rustc_middle::ty::TyCtxt,
    rustc_span::{sym, BytePos, FileName, FileNameDisplayPreference, Span},
    types::*,
    Atom,
};
use itertools::Itertools;
use log::*;
use rustfix::{Replacement, Snippet, Solution, Suggestion};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    panic,
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
};

static SINGLE_MOD: AtomicBool = AtomicBool::new(false);

/// Checks if the given function is generated by the compiler
fn is_synthetic_fn(_fn_decl: &FnDecl<'_>, body: &Body<'_>) -> bool {
    body.value.span.in_derive_expansion()
}

/// Get the field names of a struct or union (or field indices as
/// strings if it is a tuple struct)
fn get_fields(variant_data: &VariantData) -> Vec<String> {
    variant_data
        .fields()
        .iter()
        .map(|f| f.ident.as_str().to_string())
        .collect()
}

/// Information about which parts of the source code are relevant to
/// an external type
#[derive(Default, Eq, PartialEq)]
struct ItemInfo {
    /// Unqualified name
    unqual_name: String,
    /// The span for this definition
    span: Span,
    /*
    /// The spans for commenting out (e.g. `#[derive(..)]` spans) when
    /// removing this item
    to_comment_out: Vec<Span>,
    /// The spans to remove when removing this item, e.g. the annotations
    to_remove: Vec<Span>,
    */
    /// End of the parent `extern { .. }` statement, so that we can add this item if need be
    end_of_extern: Span,
    /// The parent module, so that we can look up imported names
    parent_mod: String,
}

/// A type signature to match up ADTs with the same shape and unqualified names
#[derive(Debug, PartialEq, Eq, Hash)]
enum TypeSig {
    /// An unknown type (coming from type definitions)
    Unknown,
    /// A struct with field names.
    ///
    /// TODO: field sizes/shapes as well for better matching. That
    /// would require some constraint solving
    Struct(Vec<String>),
    /// A C union with field names
    Union(Vec<String>),
}

/// A pass for the rewriting part of this tool
struct TokenRewritePass {
    /// Call graph built by pointer provenance
    call_graph: CallGraph,
    /// A mapping of structs and unions to their definitions in the crate
    type_defs: HashMap<String, HashMap<TypeSig, String>>,
    /// Contains a mapping from fn name to its type
    token_analysis: TokenAnalysis,
    /// Current function being recursed on
    fn_name: Option<Name>,
    /// Information about unresolved names, we post-process them to
    /// resolve them
    ///
    /// QualifiedName -> (UnqualifiedName, Spans)
    unresolved_types: HashMap<String, ItemInfo>,
    /// Whether to remove `#[repr(..)]`
    remove_repr: bool,
    /// Whether to remove `#[derive(..)]`
    remove_derive: bool,
    /// Whether to remove `#[no_mangle]`
    remove_no_mangle: bool,
    /// Keep track of a unique ID for removed extern functions so we can remove their `no_mangle` attribute
    removed_fns: HashSet<Span>,
    /// Names imported in each module
    imported_names: HashMap<String, HashSet<String>>,
    /// Name of the current module being processed
    current_mod: String,
    /// recursion depth for rewriting expressions
    depth: i32,
}

impl TokenRewritePass {
    pub fn new<'tcx>(_: TyCtxt<'tcx>) -> Box<LatePass> {
        Box::new(TokenRewritePass {
            call_graph: CallGraph::new(),
            type_defs: HashMap::default(),
            token_analysis: analysis::result::<TokenAnalysis>().unwrap(),
            fn_name: None,
            remove_repr: false,
            remove_derive: false,
            remove_no_mangle: false,
            removed_fns: HashSet::default(),
            imported_names: HashMap::default(),
            current_mod: "".to_owned(),
            unresolved_types: HashMap::default(),
            depth: 1,
        })
    }
}

impl LintPass for TokenRewritePass {
    fn name(&self) -> &'static str {
        "RewritePass"
    }
}

impl<'tcx> LateLintPass<'tcx> for TokenRewritePass {
    fn check_mod(&mut self, ctx: &LateContext<'tcx>, m: &'tcx Mod<'tcx>, hir_id: HirId) {
        let def_id = ctx.tcx.hir().local_def_id(hir_id).to_def_id();
        let span = ctx.tcx.def_span(def_id);
        // Here, we skip annotating modules that are defined in the
        // same file as the crate. A better approach would find if the
        // module spans the whole file and insert the helper
        // functions/imports in the correct place right before the
        // `}` that closes the module.

        let mod_name = qname_from_hir(ctx, hir_id);

        let helper_span = m.spans.inner_span.shrink_to_lo();

        if mod_name.as_str() == (*CRATE_NAME.lock().unwrap()).as_ref() {
            if !SINGLE_MOD.load(Ordering::Relaxed) {
                // remember the source file corresponding to the crate
                *CRATE_FILE_POS.lock().unwrap() = Some(
                    ctx.sess()
                        .source_map()
                        .lookup_source_file(span.lo())
                        .start_pos,
                );
            }
        } else {
            let beginning_of_source_file = ctx
                .sess()
                .source_map()
                .lookup_source_file(m.spans.inner_span.lo())
                .start_pos;
            if Some(beginning_of_source_file) == *CRATE_FILE_POS.lock().unwrap() {
                // skip annotating a module if it is not on its own separate file
                log::debug!(
                    "{} {} with helpers. the source file pos: {:?} -- crate pos: {:?}",
                    "skipping annotating".green().bold(),
                    mod_name,
                    beginning_of_source_file,
                    *CRATE_FILE_POS.lock().unwrap()
                );
                return;
            }
        };

        // let source_str = ctx.sess().source_map().span_to_snippet(m.spans.inner_span).unwrap();

        rustfix_utils::make_suggestion(
            ctx,
            helper_span.shrink_to_lo(),
            format!(
                "add imports to the beginning of the module `{}`",
                mod_name.as_str()
            ),
            format!(
                "{}\n", 
                "use ghost_cell::{GhostCell, GhostToken};".to_string(),
            ), 
            self.depth
        );
    }

    fn check_attribute(
        &mut self,
        ctx: &LateContext<'tcx>,
        attr: &'tcx ghostcelltf::rustc_ast::ast::Attribute,
    ) {
        // remove the attributes related to the structs that are removed
        if !attr.is_doc_comment() {
            if self.remove_derive && attr.has_name(sym::automatically_derived) {
                let begin_span = ctx
                    .sess()
                    .source_map()
                    .span_extend_to_prev_char(attr.span, '\n', true)
                    .shrink_to_lo();
                rustfix_utils::make_suggestion(
                    ctx,
                    begin_span,
                    "comment out derive".to_owned(),
                    "// ".to_owned(),
                    self.depth,
                );
                self.remove_derive = false;
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
        match kind {
           FnKind::ItemFn(..) | FnKind::Method(..) => {
                let fn_name = Name::from(qname_from_hir(ctx, hir_id).as_str());
                self.fn_name = Some(fn_name.clone());
                
                if fn_name.contains("main") {
                    let body_span = body.value.span;

                    // find first curly brace in body_span
                    let open_brace = ctx.sess().source_map().span_through_char(body_span, '{');
                    // add closure to beginning of body_span
                    rustfix_utils::make_suggestion(
                        ctx,
                        open_brace.shrink_to_hi(),
                        format!("add closure beginning to `{}`", fn_name),
                        format!(
                            "\n{}",
                            "GhostToken::new(|mut token| {\nlet token = &mut token;".to_string(),
                        ), 
                        self.depth
                    );

                    // add closing brace to end of body_span
                    let close_brace = ctx.sess().source_map().end_point(body_span);
                    rustfix_utils::make_suggestion(
                        ctx,
                        close_brace.shrink_to_lo(),
                        format!("add closure ending to `{}`", fn_name),
                        format!(
                            "{}\n", 
                            "});".to_string(),
                        ), 
                        self.depth
                    );

                    return;
                }

                let method_span = ctx
                .sess()
                .source_map()
                .span_until_char(span, ')').shrink_to_hi();

                let last_param = body.params.iter().last();


                match self.token_analysis.get_token(&fn_name) {
                    TokenKind::Immut(b) => {
                        rustfix_utils::make_suggestion(
                            ctx,
                            last_param.unwrap().span.shrink_to_hi(),
                            format!("add &token in `{}`", fn_name),
                            format!(", token: &GhostToken<'{}>", b),
                            self.depth,
                        );
                    }, 
                    TokenKind::Mut(b) => {
                        rustfix_utils::make_suggestion(
                            ctx,
                            last_param.unwrap().span.shrink_to_hi(),
                            format!("add &mut token in `{}`", fn_name),
                            format!(", token: &mut GhostToken<'{}>", b),
                            self.depth,
                        );
                    },
                    TokenKind::NoToken => (),
                }
            },
            FnKind::Closure => (),
        } 
    }

    fn check_expr_post(&mut self, ctx: &LateContext<'tcx>, e: &'tcx Expr<'tcx>) {
        if self.fn_name.is_none() {
            return;
        }

        if let ExprKind::MethodCall(path, _, args, _) = &e.kind {
            let qname = method_resolved_path(ctx, e).unwrap_or_default();

            // span of length 0 at the end of the span (in this case, method call)
            let ident_span = path.ident.span.shrink_to_hi();

            let end_of_method = ctx
                .sess()
                .source_map()
                .span_extend_to_next_char(ident_span, ')', true);

            let fname = self.fn_name.clone().unwrap();

            match self.token_analysis.get_token(&fname) {
                TokenKind::Immut(_) | TokenKind::Mut(_) => 
                if qname.contains("borrow") || qname.contains("borrow_mut") {
                    rustfix_utils::make_suggestion(
                        ctx,
                        end_of_method,
                        "replace with `borrow`".to_owned(),
                        "(token".to_owned(),
                        self.depth,
                    );
                },
                _ => ()
            };
        }
    }

    fn check_crate(&mut self, ctx: &LateContext<'tcx>) {
        // Reset all edit offsets and suggestions
        // *EDIT_OFFSETS.lock().unwrap() = EditOffsets::default();
        // RUSTFIX_SUGGESTIONS.lock().unwrap().clear();
    }

    fn check_crate_post(&mut self, _: &LateContext<'tcx>) {
        // Compute the data pertaining to edits
        // EDIT_OFFSETS.lock().unwrap().compute_cumulative_offsets();
    }
}

pub fn main() {
    // This is our logger
    env_logger::init();
    // Initialize rustc's logger as well
    rustc_driver::init_rustc_env_logger();

    run_compiler(&vec![], vec![StructInfoPass::new, CallGraphPass::new]);
    let info = analysis::result::<StructInfo>().unwrap();
    log::debug!("info: {:#?}", info);

    let callgraph = analysis::result::<CallGraph>().unwrap();
    log::debug!("callgraph: {:#?}", callgraph);

    run_compiler(&vec![], vec![TokenAnalysisPass::new]);
    let token = analysis::result::<TokenAnalysis>().unwrap();
    log::debug!("token: {:#?}", token);

    run_compiler(&vec![], vec![LifetimeRewritePass::new]);
    run_compiler(&vec![], vec![TokenRewritePass::new]);

    log::debug!("{}", "Suggestions:".bold().green());

    for (file, suggestions) in RUSTFIX_SUGGESTIONS.lock().unwrap().iter() {
        log::debug!("For file {}:", file.to_str().unwrap());

        for suggestion in suggestions.values().flatten() {
            let solution = &suggestion.solutions[0];
            log::debug!("{}", solution.message);
            for replacement in &solution.replacements {
                log::debug!(" - replace {:?}", replacement.snippet.text);
                log::debug!("   with   `{}`", replacement.replacement);
                log::debug!(
                    "   at {} {}:{}-{}:{}",
                    replacement.snippet.file_name,
                    replacement.snippet.line_range.start.line,
                    replacement.snippet.line_range.start.column,
                    replacement.snippet.line_range.end.line,
                    replacement.snippet.line_range.end.column,
                );
            }
        }
    }

    let cfg = ghostcelltf::Config {
        output_path: None,
        output_mode: OutputMode::NewFile,
    };

    let file_io = FileIO::new(&cfg);

    log::debug!("{}", "Applying fixes".bold().green());

    let mut orig_files: HashMap<PathBuf, String> = HashMap::default();

    for (file, suggestions) in RUSTFIX_SUGGESTIONS.lock().unwrap().drain() {
        log::info!("Rewriting file {}:", file.to_str().unwrap());

        // suggestions, ordered by depth
        let ordered_suggestions = suggestions
            .into_values()
            .flatten()
            .collect::<Vec<Suggestion>>();

        // remember and load the original source code
        let orig_source = orig_files
            .entry(file.clone())
            .or_insert_with_key(|f| file_io.read_file(f).unwrap());

        let fixed_source_code =
            rustfix::apply_suggestions(&orig_source, &ordered_suggestions).unwrap();
        
        log::debug!("{}", fixed_source_code);
        file_io.write_file(&file, &fixed_source_code).unwrap();
    }

    let orig_args: Vec<String> = std::env::args().collect();
    let args = ghostcelltf::cli::read_env(orig_args);
    let exit_code = run_compiler_with_setup(args.clone(), &vec![], vec![], |callbacks| {
        // rustc_driver::init_rustc_env_logger();
    })
    .0;

    if exit_code == 0 {
        log::debug!(
            "DONE: {}",
            "The compiler successfully compiles the code".green()
        );
    } else {
        log::debug!(
            "DONE: {}",
            "Compilation failed, please unroll the unsafe changes".red()
        );
    }
}
