#![feature(box_patterns)]
#![feature(rustc_private)]
#![feature(str_split_once)]
#![feature(get_many_mut)]
#![feature(map_many_mut)]
#![feature(cell_leak)]
#![feature(let_chains)]

pub extern crate ahash;
pub extern crate colored;
pub extern crate lazy_static;
extern crate log;
extern crate regex;

pub extern crate rustc_ast;
pub extern crate rustc_ast_pretty;
pub extern crate rustc_attr;
pub extern crate rustc_const_eval;
pub extern crate rustc_data_structures;
pub extern crate rustc_driver;
pub extern crate rustc_errors;
pub extern crate rustc_hir;
pub extern crate rustc_hir_analysis;
pub extern crate rustc_hir_pretty;
pub extern crate rustc_infer;
pub extern crate rustc_interface;
pub extern crate rustc_lint;
pub extern crate rustc_middle;
pub extern crate rustc_parse;
pub extern crate rustc_session;
pub extern crate rustc_span;
pub extern crate rustc_target;
pub extern crate rustc_tools_util;
pub extern crate rustc_type_ir;

extern crate serde_json;
extern crate string_cache;
pub use log::*;
pub use string_cache::DefaultAtom as Atom;

use std::path::PathBuf;

// common
pub mod io;
pub mod constants;

// initial pass
pub mod compiler;
pub mod transform;
pub mod utils;

// second pass
pub mod analysis;
pub mod cli;
pub mod compiler_interface;
pub mod passes;
pub mod types;
pub mod rustfix_utils;

/// Common configuration for all the tools
pub struct Config {
    /// Output file path, if any given
    pub output_path: Option<PathBuf>,
    pub output_mode: io::OutputMode,
}

/// Use interned strings for names, we use `Name` instead of `Symbol`
/// to prevent clashes with [`Symbol`] used and defined by rustc.
pub type Name = Atom;
