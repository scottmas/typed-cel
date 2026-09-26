//! The fold's tests: specialize a checked program against known roots bound from JSON, and render
//! the residual — the same `CelEnvironment::specialize` a caller runs.

use typed_cel::CelEnvironment;

/// `src` compiled against `env`, specialized with each `(name, json)` pair bound, rendered as the
/// residual's `source()`: the folded tree, then one `// $kN = …` line per constant slot.
pub fn fold_text(env: &CelEnvironment, known: &[(&str, serde_json::Value)], src: &str) -> String {
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let mut act = env.activation();
    for (name, v) in known {
        act.bind(name, v)
            .unwrap_or_else(|e| panic!("binding {name}={v}: {e}"));
    }
    env.specialize(&program, &act)
        .unwrap_or_else(|e| panic!("specializing `{src}`: {e}"))
        .source()
        .to_string()
}
