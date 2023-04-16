use rustc_lint::{LateContext, LintContext};
use crate::{
    analysis::span::*,
    constants::*,
    colored::Colorize,
};
use rustc_span::{FileName, FileNameDisplayPreference, Span};
use rustfix::{Replacement, Snippet, Solution, Suggestion};

// suggestions for right-hand side of expressions. this is so that
// we order the suggestions for rustfix to process correctly when
// two expressions' beginning/end coincide
pub fn make_suggestion_after(
    ctx: &LateContext<'_>,
    span: Span,
    message: String,
    replacement: String,
    depth: i32,
) {
    make_suggestion_impl(ctx, span, message, replacement, depth)
}
    // suggestions for left-hand side of expressions
pub fn make_suggestion(
    ctx: &LateContext<'_>,
    span: Span,
    message: String,
    replacement: String,
    depth: i32,
) {
    make_suggestion_impl(ctx, span, message, replacement, depth)
}

fn make_suggestion_impl(
    ctx: &LateContext<'_>,
    span: Span,
    message: String,
    replacement: String,
    depth: i32,
) {
    use rustfix::{LinePosition, LineRange};

    let source_map = ctx.sess().source_map();
    let fname = source_map.span_to_filename(span);

    let fname_real = match fname {
        FileName::Real(ref n) => n,
        _ => {
            log::debug!(
                "{}",
                format!("WARNING: Attempted to fix generated code at {:?}", span)
                    .bold()
                    .red()
            );
            return;
        }
    };

    let file = source_map.get_source_file(&fname).unwrap();
    // get the char offsets within the file
    let lo_offset = file.original_relative_byte_pos(span.lo()).0;
    let hi_offset = file.original_relative_byte_pos(span.hi()).0;
    // get the line and the column numbers
    let lo = file.lookup_file_pos_with_col_display(span.lo());
    let hi = file.lookup_file_pos_with_col_display(span.hi());
    let line_range = LineRange {
        start: LinePosition {
            line: lo.0,
            column: lo.2,
        },
        end: LinePosition {
            line: hi.0,
            column: hi.2,
        },
    };
    let snippet = Snippet {
        file_name: fname
            .display(FileNameDisplayPreference::Remapped)
            .to_string(),
        line_range,
        range: (lo_offset as usize)..(hi_offset as usize),
        text: (
            "".into(),
            source_map.span_to_snippet(span).unwrap(),
            "".into(),
        ),
    };

    EDIT_OFFSETS.lock().unwrap().add_edit(
        Name::from(
            fname_real
                .local_path()
                .expect("local path")
                .to_str()
                .unwrap(),
        ),
        lo_offset,
        hi_offset - lo_offset,
        replacement.len() as u32,
    );

    let mut suggestions = RUSTFIX_SUGGESTIONS.lock().unwrap();

    suggestions
        .entry(fname_real.local_path().expect("local path").into())
        .or_default()
        .entry(depth)
        .or_insert(vec![])
        .push(Suggestion {
            message: "".to_owned(),
            snippets: vec![snippet.clone()],
            solutions: vec![Solution {
                message,
                replacements: vec![Replacement {
                    snippet,
                    replacement,
                }],
            }],
        });
}