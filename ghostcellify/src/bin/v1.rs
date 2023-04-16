#![feature(get_many_mut)]
#![feature(map_many_mut)]
#![feature(box_patterns)]
#![feature(rustc_private)]
#![feature(cell_leak)]

pub extern crate rustc_ast;
pub extern crate rustc_ast_pretty;
pub extern crate rustc_attr;
pub extern crate rustc_const_eval;
pub extern crate rustc_data_structures;
pub extern crate rustc_driver;
pub extern crate rustc_errors;
pub extern crate rustc_hir;
pub extern crate rustc_hir_pretty;
pub extern crate rustc_infer;
pub extern crate rustc_interface;
pub extern crate rustc_middle;
pub extern crate rustc_parse;
pub extern crate rustc_session;
pub extern crate rustc_span;
pub extern crate rustc_target;
pub extern crate rustc_type_ir;

use ghostcelltf::compiler;

fn main() {
    // let filenames = vec!["circle", "toy"];
    // for filename in filenames {
    //     let filepath = format!("in/{filename}.rs");
    //     // log::debug!("{filepath
    //     let file = syn_impl::io::open_file(&filepath).expect("Error in reading file");
    //     let res = syn_impl::transform(file);
    //     syn_impl::io::write_output(res, &filename).expect("Error in writing file");
    // }

    // let filenames = vec!["circle", "toy"];
    // for filename in filenames {
    //     let filepath = format!("in/{filename}.rs");

    //     // log::debug!("{filepath
    //     let file = syn_impl::io::open_file(&filepath).expect("Error in reading file");
    //     let res = syn_impl::transform(file);
    //     syn_impl::io::write_output(res, &filename).expect("Error in writing file");
    // }

    // read args with flags for input and output files
    let args: Vec<String> = std::env::args().collect();
    let input_file = &args[1];
    let output_file = &args[2];

    compiler::run_on_file(&input_file, &output_file);
}
