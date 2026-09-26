//! `cel.expr.conformance.test.SimpleTestFile`, read out of the generic textproto tree.
//!
//! This is the only place that knows the corpus's schema. It is deliberately TOTAL over the
//! fields that decide an outcome: a field it does not understand becomes an explicit
//! `Unsupported` rather than a default, because a default here reads as "the case ran and agreed"
//! when what happened is "the harness did not look".

use std::path::Path;

use super::textproto::{self, Msg, Value as Tp};

/// The whole vendored corpus, parsed once.
#[derive(Debug)]
pub struct Corpus {
    pub files: Vec<CaseFile>,
}

#[derive(Debug)]
pub struct CaseFile {
    pub name: String,
    pub cases: Vec<Case>,
}

/// One `SimpleTest`. `(file, section, name)` is its identity, and the three together are what
/// EXCLUSIONS.toml and the generated tests key on.
#[derive(Clone, Debug)]
pub struct Case {
    pub file: String,
    pub section: String,
    pub name: String,
    pub expr: String,
    pub container: Option<String>,
    pub disable_macros: bool,
    pub disable_check: bool,
    pub check_only: bool,
    /// The case declares a type environment, which only a CHECKER can honour.
    pub has_type_env: bool,
    pub bindings: Vec<(String, Binding)>,
    pub expect: Expect,
    /// 0 for the first case with this `(file, section, name)`, 1 for the second, and so on.
    /// `(file, section, name)` is NOT unique upstream — `string_ext/index_of` carries three
    /// different tests all called `char_index`.
    pub ordinal: usize,
}

impl Case {
    /// `file/section/name` — what an exclusion rule cites. Deliberately NOT unique: a rule naming
    /// a duplicated case name excludes every case with that name, which is the behaviour you want
    /// when the reason is a construct rather than an individual expression.
    pub fn id(&self) -> String {
        format!("{}/{}/{}", self.file, self.section, self.name)
    }

    /// The identity that is unique across the corpus — `id`, plus `#N` for a repeat. Test names
    /// and report rows use this, so two upstream cases sharing a name stay two cases.
    pub fn unique_id(&self) -> String {
        match self.ordinal {
            0 => self.id(),
            n => format!("{}#{}", self.id(), n + 1),
        }
    }
}

/// A bound variable. The corpus binds a `cel.expr.ExprValue`, which is a value OR an error OR an
/// unknown; only the first is something we can put in a `Context`.
#[derive(Clone, Debug)]
pub enum Binding {
    Value(CelValue),
    /// An error or unknown binding — legal in the corpus, not expressible in our runtime.
    Unsupported(String),
}

/// What the case says should happen.
#[derive(Clone, Debug)]
pub enum Expect {
    /// No `result_matcher` at all. cel-spec's default: the expression must evaluate to `true`.
    True,
    Value(CelValue),
    /// `eval_error` — the messages are advisory. cel-spec's own runners do not compare error TEXT
    /// across implementations, and neither do we: matching Google's wording would test our
    /// phrasing rather than our behaviour. What is asserted is that evaluation FAILED.
    EvalError,
    /// A matcher this harness cannot decide (`unknown`, `any_unknowns`, `typed_result`, …). Never
    /// silently treated as a pass.
    Unsupported(String),
}

/// `cel.expr.Value`, the corpus's expected-value language.
#[derive(Clone, Debug, PartialEq)]
pub enum CelValue {
    Null,
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
    List(Vec<CelValue>),
    Map(Vec<(CelValue, CelValue)>),
    /// A protobuf message value — `object_value`, an `Any` with a type URL.
    Object {
        type_url: String,
    },
    /// `enum_value`.
    Enum {
        ty: String,
        value: i64,
    },
    /// `type_value` — the name of a type, as produced by `type(x)`.
    Type(String),
    /// A value kind this harness does not model.
    Unsupported(String),
}

impl Corpus {
    /// Parse every `*.textproto` under `dir`, in sorted order so the generated output is stable.
    pub fn load(dir: &Path) -> Result<Corpus, String> {
        let mut paths: Vec<_> = std::fs::read_dir(dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "textproto"))
            .collect();
        paths.sort();

        let mut files = Vec::new();
        for path in paths {
            let src = std::fs::read_to_string(&path).map_err(|e| format!("{path:?}: {e}"))?;
            let msg = textproto::parse(&src).map_err(|e| format!("{}: {e}", path.display()))?;
            let stem = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or_default()
                .to_string();
            files.push(CaseFile::read(&stem, &msg));
        }
        Ok(Corpus { files })
    }

    pub fn cases(&self) -> impl Iterator<Item = &Case> {
        self.files.iter().flat_map(|f| f.cases.iter())
    }

    pub fn len(&self) -> usize {
        self.files.iter().map(|f| f.cases.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl CaseFile {
    /// `stem` is the identity, NOT the file's own `name:` field. They disagree upstream —
    /// `type_deduction.textproto` declares `name: "type_deductions"` — and the stem is what a
    /// reader sees on disk and what an exclusion rule cites, so the stem wins everywhere.
    fn read(stem: &str, msg: &Msg) -> CaseFile {
        let name = stem.to_string();
        let mut cases: Vec<Case> = Vec::new();
        let mut seen: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for section in msg.all("section") {
            let Tp::Msg(section) = section else { continue };
            let section_name = section.get_str("name").unwrap_or_default();
            for test in section.all("test") {
                let Tp::Msg(test) = test else { continue };
                let mut case = Case::read(stem, &section_name, test);
                let slot = seen.entry(case.id()).or_default();
                case.ordinal = *slot;
                *slot += 1;
                cases.push(case);
            }
        }
        CaseFile { name, cases }
    }
}

impl Case {
    fn read(file: &str, section: &str, msg: &Msg) -> Case {
        let bindings = msg
            .all("bindings")
            .filter_map(|b| match b {
                Tp::Msg(m) => Some(m),
                _ => None,
            })
            .map(|m| {
                let key = m.get_str("key").unwrap_or_default();
                let binding = match m.get_msg("value") {
                    // ExprValue { value | error | unknown }
                    Some(ev) => match ev.get_msg("value") {
                        Some(v) => Binding::Value(CelValue::read(v)),
                        None => Binding::Unsupported(format!(
                            "binding `{key}` is not a plain value: {:?}",
                            ev.fields.iter().map(|(k, _)| k).collect::<Vec<_>>()
                        )),
                    },
                    None => Binding::Unsupported(format!("binding `{key}` has no value")),
                };
                (key, binding)
            })
            .collect();

        // The oneof, in the proto's declaration order. Exactly one is set, or none.
        let expect = if let Some(v) = msg.get_msg("value") {
            Expect::Value(CelValue::read(v))
        } else if msg.get("eval_error").is_some() {
            Expect::EvalError
        } else if let Some((field, _)) = msg.fields.iter().find(|(k, _)| {
            matches!(
                k.as_str(),
                "typed_result" | "any_eval_errors" | "unknown" | "any_unknowns"
            )
        }) {
            Expect::Unsupported(format!("result matcher `{field}`"))
        } else {
            Expect::True
        };

        Case {
            file: file.to_string(),
            section: section.to_string(),
            name: msg.get_str("name").unwrap_or_default(),
            expr: msg.get_str("expr").unwrap_or_default(),
            container: msg.get_str("container").filter(|c| !c.is_empty()),
            disable_macros: msg.get_bool("disable_macros").unwrap_or(false),
            disable_check: msg.get_bool("disable_check").unwrap_or(false),
            check_only: msg.get_bool("check_only").unwrap_or(false),
            has_type_env: msg.get("type_env").is_some(),
            bindings,
            expect,
            ordinal: 0,
        }
    }
}

impl CelValue {
    fn read(msg: &Msg) -> CelValue {
        let Some((field, value)) = msg.fields.first() else {
            // An EMPTY `value {}` is a legal encoding of the default, which for `cel.expr.Value`
            // is `null_value`. Reading it as "unsupported" would turn ~a dozen real cases into
            // noise.
            return CelValue::Null;
        };
        match (field.as_str(), value) {
            ("null_value", _) => CelValue::Null,
            ("bool_value", Tp::Ident(i)) => CelValue::Bool(i == "true"),
            ("int64_value", Tp::Num(n)) => n
                .parse::<i64>()
                .map(CelValue::Int)
                .unwrap_or_else(|_| CelValue::Unsupported(format!("int64_value {n}"))),
            ("uint64_value", Tp::Num(n)) => n
                .parse::<u64>()
                .map(CelValue::Uint)
                .unwrap_or_else(|_| CelValue::Unsupported(format!("uint64_value {n}"))),
            // The corpus spells the non-finite doubles four ways — `inf`, `-inf`, `Infinity`,
            // `NaN` — and only the signed ones lex as numbers. Rust's `f64::from_str` accepts all
            // of them case-insensitively, so both token kinds go through it rather than through a
            // hand-written table that would silently miss the fifth spelling.
            ("double_value", Tp::Num(n) | Tp::Ident(n)) => n
                .parse::<f64>()
                .map(CelValue::Double)
                .unwrap_or_else(|_| CelValue::Unsupported(format!("double_value {n}"))),
            ("string_value", Tp::Str(b)) => {
                CelValue::String(String::from_utf8_lossy(b).into_owned())
            }
            ("bytes_value", Tp::Str(b)) => CelValue::Bytes(b.clone()),
            ("type_value", Tp::Str(b)) => CelValue::Type(String::from_utf8_lossy(b).into_owned()),
            ("list_value", Tp::Msg(m)) => CelValue::List(
                m.all("values")
                    .filter_map(|v| match v {
                        Tp::Msg(v) => Some(CelValue::read(v)),
                        _ => None,
                    })
                    .collect(),
            ),
            ("map_value", Tp::Msg(m)) => CelValue::Map(
                m.all("entries")
                    .filter_map(|e| match e {
                        Tp::Msg(e) => Some((
                            e.get_msg("key")
                                .map(CelValue::read)
                                .unwrap_or(CelValue::Null),
                            e.get_msg("value")
                                .map(CelValue::read)
                                .unwrap_or(CelValue::Null),
                        )),
                        _ => None,
                    })
                    .collect(),
            ),
            ("object_value", Tp::Msg(m)) => CelValue::Object {
                // The Any's payload is spelled as one `[type.url] { … }` field.
                type_url: m
                    .fields
                    .first()
                    .map(|(k, _)| k.clone())
                    .unwrap_or_else(|| "<empty>".into()),
            },
            ("enum_value", Tp::Msg(m)) => CelValue::Enum {
                ty: m.get_str("type").unwrap_or_default(),
                value: match m.get("value") {
                    Some(Tp::Num(n)) => n.parse().unwrap_or(0),
                    _ => 0,
                },
            },
            (other, v) => CelValue::Unsupported(format!("{other} = {v:?}")),
        }
    }
}
