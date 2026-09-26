//! A structural query: the top-level conjuncts of a compiled expression.
//!
//! A caller that lints an expression's SHAPE — "is there a guard conjunct for each window this
//! reads?" — otherwise has to re-parse the authored source, which means a second parser that
//! disagrees with the first the day either changes.
//!
//! Deliberately shallow. Enough to write a lint, not enough to reimplement the checker. A caller
//! that needs more than this wants a different query, and the answer is to add a second narrow one
//! rather than to expose the AST.

use crate::common::ast::{operators, Expr, IdedExpr, LiteralValue};
use crate::demand::Segment;

/// One top-level `&&` conjunct of a compiled expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Conjunct {
    /// The path on the LEFT, in the same `Segment` vocabulary [`DemandSet`](crate::DemandSet)
    /// uses, so a caller matches against one thing and not two. Empty when the conjunct is opaque.
    pub path: Vec<Segment>,
    /// `>`, `==`, `in`, … `None` when the conjunct is not a comparison.
    pub operator: Option<String>,
    /// The constant on the RIGHT. `None` when there is not one — the row is still reported, so a
    /// lint cannot silently skip what it could not read.
    pub literal: Option<Literal>,
}

/// A constant a conjunct compares against.
#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Bool(bool),
    Num(f64),
    Str(String),
    /// The duration SPELLING, as the author wrote it — `40s`, not `duration('40s')`.
    Duration(String),
}

impl crate::CelProgram {
    /// The top-level `&&` conjuncts, in source order.
    ///
    /// A `||`, a comprehension or a call is ONE opaque conjunct — reported, with no operator and
    /// no literal. `&&` is the only connective a guard can be proven through: flattening `_||_`
    /// as well would produce a list that reads like a conjunction and is not one, and a lint built
    /// on it would approve exactly the expression it exists to reject.
    pub fn conjuncts(&self) -> Vec<Conjunct> {
        let mut out = Vec::new();
        split_and(self.program().expression(), &mut out);
        out
    }
}

/// Fold over `_&&_` ONLY, left to right, so the result is in source order.
fn split_and(e: &IdedExpr, out: &mut Vec<Conjunct>) {
    if let Expr::Call(c) = &e.expr {
        if c.func_name == operators::LOGICAL_AND && c.target.is_none() && c.args.len() == 2 {
            split_and(&c.args[0], out);
            split_and(&c.args[1], out);
            return;
        }
    }
    out.push(conjunct(e));
}

/// One leaf of the `&&` fold, read as far as it reads and no further.
fn conjunct(e: &IdedExpr) -> Conjunct {
    if let Expr::Call(c) = &e.expr {
        if c.target.is_none() && c.args.len() == 2 {
            if let Some(op) = comparison(&c.func_name) {
                return Conjunct {
                    path: path(&c.args[0]).unwrap_or_default(),
                    operator: Some(op.to_string()),
                    literal: literal(&c.args[1]),
                };
            }
        }
    }
    // A bare predicate — `flag` — still carries a path; anything else is opaque.
    Conjunct {
        path: path(e).unwrap_or_default(),
        operator: None,
        literal: None,
    }
}

/// The comparison operators, unwrapped from the parser's `_op_` spelling.
///
/// An allowlist rather than a strip-the-underscores rule: `_&&_`, `_?_:_` and `_[_]` wear the same
/// shape, and reporting one of those as a comparison would hand a lint a row it would read as a
/// guard.
fn comparison(func: &str) -> Option<&'static str> {
    Some(match func {
        operators::EQUALS => "==",
        operators::NOT_EQUALS => "!=",
        operators::LESS => "<",
        operators::LESS_EQUALS => "<=",
        operators::GREATER => ">",
        operators::GREATER_EQUALS => ">=",
        operators::IN => "in",
        _ => return None,
    })
}

/// `root ▸ "a" ▸ "b"`, for the shapes a path can take. `None` for anything computed.
fn path(e: &IdedExpr) -> Option<Vec<Segment>> {
    match &e.expr {
        Expr::Ident(name) => Some(vec![Segment::Root(name.clone())]),
        Expr::Select(s) => {
            let mut p = path(&s.operand)?;
            p.push(Segment::Key(s.field.clone()));
            Some(p)
        }
        Expr::Call(c) if c.func_name == operators::INDEX && c.args.len() == 2 => {
            let mut p = path(&c.args[0])?;
            match &c.args[1].expr {
                Expr::Literal(LiteralValue::String(k)) => {
                    p.push(Segment::Key(k.inner().to_string()));
                    Some(p)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The constant on the right, when there is one.
fn literal(e: &IdedExpr) -> Option<Literal> {
    match &e.expr {
        Expr::Literal(LiteralValue::Boolean(b)) => Some(Literal::Bool(*b.inner())),
        Expr::Literal(LiteralValue::Double(d)) => Some(Literal::Num(*d.inner())),
        Expr::Literal(LiteralValue::Int(i)) => Some(Literal::Num(*i as f64)),
        Expr::Literal(LiteralValue::String(s)) => Some(Literal::Str(s.inner().to_string())),
        // `40s` reaches the parser as `duration('40s')`, because the alias expands BEFORE parsing.
        // Report the spelling the AUTHOR wrote: a lint matching window keys against guard
        // thresholds compares `40s` to `40s`, and would compare nothing at all if this reported a
        // call it did not expect.
        Expr::Call(c) if c.func_name == "duration" && c.target.is_none() && c.args.len() == 1 => {
            match &c.args[0].expr {
                Expr::Literal(LiteralValue::String(s)) => {
                    Some(Literal::Duration(s.inner().to_string()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
