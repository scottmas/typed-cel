//! Every bound `typed-cel` enforces.
//!
//! The fork arrived with NONE. A grep of the absorbed source for
//! `recursion|max_depth|iteration_limit|budget|limit` finds the parser's own ANTLR recursion guard
//! and a set of timestamp range constants, and the timestamp deletion took those — so an
//! expression over attacker-controlled data is bounded here or not at all.
//!
//! The two environments have opposite cost profiles, and both are covered by the same struct. An
//! HTTP assertion runs ONCE per request against a bounded body; a system expression runs on EVERY
//! TICK, forever, against a state that grows with the sandbox's own activity. So depth and cost
//! are refused at BUILD time, when a human is present to read the error, and input caps are a
//! precondition of constructing the activation — `execute` cannot be interrupted once it has
//! started.

use crate::common::ast::{Expr, IdedExpr};

/// The limits, with the defaults `README.md` documents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CelLimits {
    /// Expression source length in bytes. Checked on the DESUGARED form, before the parser.
    pub max_source_len: usize,
    /// Syntactic nesting depth, scanned from the DESUGARED SOURCE, before the parser. Measuring
    /// it by walking the parsed AST measures AFTER the hazard — the parser is what recurses first.
    pub max_depth: u32,
    /// Static cost estimate. Comprehension bodies multiply by [`ASSUMED_ELEMENTS`], so the
    /// default admits two nested comprehensions over declared lists and refuses three — the point
    /// at which the runtime becomes a product of more attacker-controlled lengths than a reviewer
    /// can hold in their head.
    pub max_cost: u64,
    /// Elements in any one bound list. HTTP environment only — the system environment binds no
    /// attacker-controlled list.
    ///
    /// A correctness knob as well as a cost one: a legitimately large response that exceeds it is
    /// DENIED, so the default carries headroom.
    pub max_list_len: usize,
    /// Elements across the whole activation. A per-list cap alone is bypassed by breadth.
    pub max_total_elements: usize,
    /// Elements a specialization may unroll a comprehension over a KNOWN range into. Above it the
    /// loop is kept, over a literal copy of the range.
    pub max_unroll: usize,
}

impl Default for CelLimits {
    fn default() -> CelLimits {
        CelLimits {
            max_source_len: 8 * 1024,
            // Comfortably under the parser's own ANTLR guard (96), so the refusal an author sees
            // is ours and names a limit they can look up.
            max_depth: 32,
            max_cost: 1_000_000,
            // A policy root list is one bound list: a million roots compile and decide
            // (measured). The total is never below one list's cap, or
            // the per-list cap would be unreachable.
            max_list_len: 1_000_000,
            max_total_elements: 1_000_000,
            max_unroll: 256,
        }
    }
}

/// What a comprehension body is assumed to run over when estimating cost.
///
/// Deliberately crude and deliberately an OVER-estimate: a refusal at build time is a sentence in
/// an error message; a missed one is an unbounded loop serving a request — or, in the system
/// environment, an unbounded loop inside every poll tick forever.
const ASSUMED_ELEMENTS: u64 = 100;

/// Why an expression is outside the bounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundError {
    SourceTooLong { len: usize, limit: usize },
    TooDeep { depth: u32, limit: u32 },
    TooCostly { estimate: u64, limit: u64 },
}

impl std::fmt::Display for BoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundError::SourceTooLong { len, limit } => {
                write!(f, "expression is {len} bytes, over the limit of {limit}")
            }
            BoundError::TooDeep { depth, limit } => {
                write!(
                    f,
                    "expression nests {depth} deep, over the limit of {limit}"
                )
            }
            BoundError::TooCostly { estimate, limit } => write!(
                f,
                "expression has an estimated cost of {estimate}, over the limit of {limit}"
            ),
        }
    }
}

/// The checks that run BEFORE the parser, on the desugared source.
pub(crate) fn check_source(src: &str, limits: &CelLimits) -> Result<(), BoundError> {
    if src.len() > limits.max_source_len {
        return Err(BoundError::SourceTooLong {
            len: src.len(),
            limit: limits.max_source_len,
        });
    }
    let depth = source_depth(src);
    if depth > limits.max_depth {
        return Err(BoundError::TooDeep {
            depth,
            limit: limits.max_depth,
        });
    }
    Ok(())
}

/// Maximum bracket nesting, ignoring string literals.
///
/// A syntactic proxy for how deep the generated parser will recurse. It does not have to be exact;
/// it has to be an upper bound reached BEFORE `CELParser::start` is called.
fn source_depth(src: &str) -> u32 {
    let b = src.as_bytes();
    let mut depth = 0u32;
    let mut max = 0u32;
    let mut i = 0usize;
    while i < b.len() {
        match b[i] {
            q @ (b'\'' | b'"') => {
                let triple = b.get(i + 1) == Some(&q) && b.get(i + 2) == Some(&q);
                let delim = if triple { 3 } else { 1 };
                i += delim;
                while i < b.len() {
                    if b[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if b[i] == q
                        && (!triple || (b.get(i + 1) == Some(&q) && b.get(i + 2) == Some(&q)))
                    {
                        i += delim;
                        break;
                    }
                    i += 1;
                }
                continue;
            }
            b'(' | b'[' | b'{' => {
                depth += 1;
                max = max.max(depth);
            }
            b')' | b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
        i += 1;
    }
    max
}

/// The static cost estimate, refused at build time.
pub(crate) fn check_cost(expr: &IdedExpr, limits: &CelLimits) -> Result<u64, BoundError> {
    let estimate = estimate_cost(expr, 1);
    if estimate > limits.max_cost {
        return Err(BoundError::TooCostly {
            estimate,
            limit: limits.max_cost,
        });
    }
    Ok(estimate)
}

/// Cost of `expr`, each enclosing comprehension multiplying by [`ASSUMED_ELEMENTS`].
///
/// This is what refuses a shape whose runtime is a product of two attacker-controlled lengths —
/// `a.all(x, b.all(y, c.all(z, …)))` — at build time rather than at request time.
fn estimate_cost(expr: &IdedExpr, multiplier: u64) -> u64 {
    let own = multiplier;
    let children: u64 = match &expr.expr {
        Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => 0,
        Expr::Select(s) => estimate_cost(&s.operand, multiplier),
        Expr::Call(c) => {
            let target = c
                .target
                .as_ref()
                .map(|t| estimate_cost(t, multiplier))
                .unwrap_or(0);
            target
                + c.args
                    .iter()
                    .map(|a| estimate_cost(a, multiplier))
                    .sum::<u64>()
        }
        Expr::List(l) => l
            .elements
            .iter()
            .map(|e| estimate_cost(e, multiplier))
            .sum(),
        Expr::Map(m) => m
            .entries
            .iter()
            .map(|e| match &e.expr {
                crate::common::ast::EntryExpr::MapEntry(entry) => {
                    estimate_cost(&entry.key, multiplier) + estimate_cost(&entry.value, multiplier)
                }
            })
            .sum(),
        Expr::Comprehension(c) => {
            let inner = multiplier.saturating_mul(ASSUMED_ELEMENTS);
            estimate_cost(&c.iter_range, multiplier)
                + estimate_cost(&c.accu_init, multiplier)
                + estimate_cost(&c.loop_cond, inner)
                + estimate_cost(&c.loop_step, inner)
                + estimate_cost(&c.result, multiplier)
        }
    };
    own.saturating_add(children)
}

/// Why an activation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputError {
    ListTooLong {
        path: String,
        len: usize,
        limit: usize,
    },
    TooManyElements {
        total: usize,
        limit: usize,
    },
}

impl std::fmt::Display for InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputError::ListTooLong { path, len, limit } => write!(
                f,
                "`{path}` has {len} elements, over the per-collection limit of {limit}"
            ),
            InputError::TooManyElements { total, limit } => write!(
                f,
                "the activation has {total} elements, over the total limit of {limit}"
            ),
        }
    }
}

/// Count the elements of a bound value, refusing anything over the caps.
///
/// A precondition of constructing the activation, never a check during evaluation: `execute`
/// cannot be interrupted once it has started, so capping at evaluation time is too late.
pub(crate) fn check_input(
    value: &serde_json::Value,
    path: &str,
    limits: &CelLimits,
    total: &mut usize,
) -> Result<(), InputError> {
    match value {
        serde_json::Value::Array(items) => {
            if items.len() > limits.max_list_len {
                return Err(InputError::ListTooLong {
                    path: path.to_string(),
                    len: items.len(),
                    limit: limits.max_list_len,
                });
            }
            bump(total, items.len(), limits)?;
            for (i, item) in items.iter().enumerate() {
                check_input(item, &format!("{path}[{i}]"), limits, total)?;
            }
            Ok(())
        }
        serde_json::Value::Object(entries) => {
            if entries.len() > limits.max_list_len {
                return Err(InputError::ListTooLong {
                    path: path.to_string(),
                    len: entries.len(),
                    limit: limits.max_list_len,
                });
            }
            bump(total, entries.len(), limits)?;
            for (k, v) in entries {
                check_input(v, &format!("{path}.{k}"), limits, total)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn bump(total: &mut usize, by: usize, limits: &CelLimits) -> Result<(), InputError> {
    *total += by;
    if *total > limits.max_total_elements {
        return Err(InputError::TooManyElements {
            total: *total,
            limit: limits.max_total_elements,
        });
    }
    Ok(())
}
