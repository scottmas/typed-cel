//! The fold's tests: compile a program with known roots bound from JSON, and render the residual —
//! the same `CelEnvironment::compile` with `CompileOpts::known` a caller runs.

use typed_cel::{CelEnvironment, CompileOpts};

/// `src` compiled against `env` with each `(name, json)` pair bound as KNOWN, rendered as the
/// residual's `source()`: the folded tree, then one `// $kN = …` line per constant slot.
pub fn fold_text(env: &CelEnvironment, known: &[(&str, serde_json::Value)], src: &str) -> String {
    let mut act = env.activation();
    for (name, v) in known {
        act.bind(name, v)
            .unwrap_or_else(|e| panic!("binding {name}={v}: {e}"));
    }
    env.compile(
        src,
        &CompileOpts {
            known: Some(&act),
            ..Default::default()
        },
    )
    .unwrap_or_else(|e| panic!("compiling `{src}` with known values: {e}"))
    .source()
    .to_string()
}
