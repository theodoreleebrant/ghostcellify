use crate::io;
use crate::transform;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_ast::Crate;

fn sys_root() -> Vec<String> {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    let sysroot = format!("{}/toolchains/{}", home.unwrap(), toolchain.unwrap());
    vec!["--sysroot".into(), sysroot]
}

struct CompilerCallbacks {
    ast: Option<String>,
}

impl Callbacks for CompilerCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        let mut krate = queries.parse().unwrap().take();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            self.ast = Some(transform::transform(krate, tcx));
        });

        Compilation::Continue
    }
}

pub fn run_on_file(input_file: &str, output_file: &str) -> () {
    // format string to concatenate dir and filename
    let mut args = vec!["rustc".into(), input_file.into()];
    let current_dir = std::env::current_exe().unwrap();
    let current_dir = current_dir.parent().unwrap();
    // Back out once more if running CI
    let current_dir = if current_dir.ends_with("deps") {
        current_dir.parent().unwrap()
    } else {
        current_dir
    };

    args.extend(["-A".into(), "dead_code".into()]);
    args.extend(["-A".into(), "unused_variables".into()]);
    args.extend(sys_root());
    std::env::set_var(
        "LD_LIBRARY_PATH",
        std::env::current_exe().unwrap().as_os_str(),
    );
    std::env::set_var(
        "DYLD_LIBRARY_PATH",
        std::env::current_exe().unwrap().as_os_str(),
    );
    let libghostcell_macros = current_dir.join("libghostcell_macros.rlib");
    args.extend([
        "--extern".into(),
        format!(
            "ghostcell_macros={}",
            libghostcell_macros.as_os_str().to_str().unwrap()
        ),
    ]);

    let mut cc = CompilerCallbacks { ast: None };
    RunCompiler::new(&args, &mut cc).run().unwrap();

    if let Some(ast) = cc.ast {
        log::debug!("AST: {}", ast);
        io::write_output(&ast, output_file);
    }
}
