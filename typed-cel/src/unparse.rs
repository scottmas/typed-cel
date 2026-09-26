//! Render a desugared expression as CEL text that parses back to the same tree.
//!
//! Used for a residual's `source()` and by its round-trip test. Never on an evaluation path: a
//! residual is evaluated and emitted from its tree, so this text is for a reader and a re-parse.
//!
//! The rendering is deliberately paren-generous, and the rule is total without a precedence table
//! (a precedence table would be a second copy of the grammar, and a copy drifts):
//!
//! - A node is PRIMARY when it is an `Ident`, a non-negative numeric literal, any other literal, a
//!   `Select`, a `has(..)`, an index, a call to a NON-operator function, a list or map literal, or a
//!   comprehension (rendered as the member-call macro it came from).
//! - Every operand of an operator that is not primary is wrapped in `( … )`.
//! - A unary operand (`!_`, `-_`) is wrapped unless it is an `Ident`, a `Select` or a non-operator
//!   call, so `-_` over the literal `3` renders `-(3)` — which re-parses as a call, not as `-3`.
//! - The operand of a `Select`, the target of a member call and the target of an index are wrapped
//!   unless primary; so is a map key, whose `:` would otherwise meet a conditional's.
//!
//! Parentheses create no node, so wrapping is always safe; the one thing that is NOT safe is
//! flattening a balanced `&&`/`||` run into one run, which changes the tree. It is not done.

use crate::check::{build_parts, classify, first_arg, second_arg, Fold};
use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedExpr, LiteralValue,
};

/// Why a tree has no source form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnparseError(pub String);

impl std::fmt::Display for UnparseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for UnparseError {}

/// The CEL text for `e`, or why there is none.
pub fn unparse(e: &IdedExpr) -> Result<String, UnparseError> {
    let mut out = String::new();
    write_expr(&mut out, e)?;
    Ok(out)
}

fn err<T>(msg: impl Into<String>) -> Result<T, UnparseError> {
    Err(UnparseError(msg.into()))
}

/// The source spelling of a binary infix operator, or `None` if `name` is not one.
fn infix(name: &str) -> Option<&'static str> {
    Some(match name {
        operators::LOGICAL_AND => "&&",
        operators::LOGICAL_OR => "||",
        operators::EQUALS => "==",
        operators::NOT_EQUALS => "!=",
        operators::LESS => "<",
        operators::LESS_EQUALS => "<=",
        operators::GREATER => ">",
        operators::GREATER_EQUALS => ">=",
        operators::ADD => "+",
        operators::SUBSTRACT => "-",
        operators::MULTIPLY => "*",
        operators::DIVIDE => "/",
        operators::MODULO => "%",
        operators::IN => "in",
        _ => return None,
    })
}

/// An operator call, as opposed to a call of a named function. An index is neither: it renders
/// as a postfix `[..]` and is primary.
fn is_operator(name: &str) -> bool {
    infix(name).is_some()
        || matches!(
            name,
            operators::CONDITIONAL
                | operators::LOGICAL_NOT
                | operators::NEGATE
                | operators::NOT_STRICTLY_FALSE
        )
}

fn is_primary(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::Literal(LiteralValue::Int(i)) => *i >= 0,
        Expr::Literal(LiteralValue::Double(d)) => !d.inner().is_sign_negative(),
        Expr::Literal(_) => true,
        Expr::Ident(_) | Expr::Select(_) | Expr::List(_) | Expr::Map(_) => true,
        Expr::Comprehension(_) => true,
        Expr::Call(c) => c.func_name == operators::INDEX || !is_operator(&c.func_name),
        Expr::Unspecified => false,
    }
}

/// A name the grammar reads back as the same identifier: `[_a-zA-Z][_a-zA-Z0-9]*`.
fn is_ident(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c == '_' || c.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn write_name(out: &mut String, name: &str, what: &str) -> Result<(), UnparseError> {
    if !is_ident(name) {
        return err(format!("`{name}` is not a {what} the grammar can spell"));
    }
    out.push_str(name);
    Ok(())
}

fn write_expr(out: &mut String, e: &IdedExpr) -> Result<(), UnparseError> {
    match &e.expr {
        Expr::Literal(v) => write_literal(out, v),
        // A residual's constant slot is rendered as its name. No CEL identifier can be one, so
        // this text does not parse back: the residual is run from its tree, never re-parsed.
        Expr::Ident(n) if crate::specialize::is_slot_name(n) => {
            out.push_str(n);
            Ok(())
        }
        Expr::Ident(n) => write_name(out, n, "identifier"),
        Expr::Select(s) if s.test => {
            out.push_str("has(");
            write_operand(out, &s.operand)?;
            out.push('.');
            write_name(out, &s.field, "field name")?;
            out.push(')');
            Ok(())
        }
        Expr::Select(s) => {
            write_operand(out, &s.operand)?;
            out.push('.');
            write_name(out, &s.field, "field name")
        }
        Expr::Call(c) => write_call(out, c),
        Expr::List(l) => {
            out.push('[');
            for (i, el) in l.elements.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_expr(out, el)?;
            }
            out.push(']');
            Ok(())
        }
        Expr::Map(m) => {
            out.push('{');
            for (i, entry) in m.entries.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let EntryExpr::MapEntry(me) = &entry.expr;
                write_operand(out, &me.key)?;
                out.push_str(": ");
                write_expr(out, &me.value)?;
            }
            out.push('}');
            Ok(())
        }
        Expr::Comprehension(c) => write_comprehension(out, c),
        Expr::Unspecified => err("an unspecified expression has no source form"),
    }
}

/// An operand: itself when primary, parenthesized otherwise.
fn write_operand(out: &mut String, e: &IdedExpr) -> Result<(), UnparseError> {
    if is_primary(e) {
        write_expr(out, e)
    } else {
        out.push('(');
        write_expr(out, e)?;
        out.push(')');
        Ok(())
    }
}

/// The operand of `!_`/`-_`: bare only when it is an `Ident`, a `Select` or a named call.
fn write_unary_operand(out: &mut String, e: &IdedExpr) -> Result<(), UnparseError> {
    let bare = match &e.expr {
        Expr::Ident(_) | Expr::Select(_) => true,
        Expr::Call(c) => c.func_name != operators::INDEX && !is_operator(&c.func_name),
        _ => false,
    };
    if bare {
        write_expr(out, e)
    } else {
        out.push('(');
        write_expr(out, e)?;
        out.push(')');
        Ok(())
    }
}

fn write_args(out: &mut String, args: &[IdedExpr]) -> Result<(), UnparseError> {
    out.push('(');
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        write_expr(out, a)?;
    }
    out.push(')');
    Ok(())
}

fn write_call(out: &mut String, c: &CallExpr) -> Result<(), UnparseError> {
    let name = c.func_name.as_str();
    match (name, c.target.as_deref(), c.args.as_slice()) {
        (operators::NOT_STRICTLY_FALSE, _, _) => {
            err("`@not_strictly_false` is comprehension plumbing and has no standalone source form")
        }
        (_, None, [l, r]) if infix(name).is_some() => {
            write_operand(out, l)?;
            out.push(' ');
            out.push_str(infix(name).unwrap_or_default());
            out.push(' ');
            write_operand(out, r)
        }
        (operators::CONDITIONAL, None, [cond, a, b]) => {
            write_operand(out, cond)?;
            out.push_str(" ? ");
            write_operand(out, a)?;
            out.push_str(" : ");
            write_operand(out, b)
        }
        (operators::INDEX, None, [t, k]) => {
            write_operand(out, t)?;
            out.push('[');
            write_expr(out, k)?;
            out.push(']');
            Ok(())
        }
        (operators::LOGICAL_NOT, None, [x]) => {
            out.push('!');
            write_unary_operand(out, x)
        }
        (operators::NEGATE, None, [x]) => {
            out.push('-');
            write_unary_operand(out, x)
        }
        _ if is_operator(name) || name == operators::INDEX => err(format!(
            "operator `{name}` with {} argument(s){} has no source form",
            c.args.len(),
            if c.target.is_some() {
                " and a target"
            } else {
                ""
            }
        )),
        (_, Some(t), args) => {
            write_operand(out, t)?;
            out.push('.');
            write_name(out, name, "function name")?;
            write_args(out, args)
        }
        (_, None, args) => {
            write_name(out, name, "function name")?;
            write_args(out, args)
        }
    }
}

/// A comprehension re-macroized by the SAME classification the checker uses (`check.rs`), so the
/// shape rules exist once.
fn write_comprehension(out: &mut String, c: &ComprehensionExpr) -> Result<(), UnparseError> {
    if let Some(v2) = &c.iter_var2 {
        return err(format!(
            "two-variable comprehensions have no source form here (`{v2}`)"
        ));
    }
    let shape = || UnparseError("unrecognised comprehension shape: no macro produces it".into());
    let (macro_name, parts): (&str, Vec<&IdedExpr>) = match classify(c) {
        Some(Fold::Predicate) => {
            let pred = second_arg(&c.loop_step).ok_or_else(shape)?;
            // exists: init false; all: init true (parser/macros.rs).
            let name = match &c.accu_init.expr {
                Expr::Literal(LiteralValue::Boolean(b)) if !*b.inner() => operators::EXISTS,
                _ => operators::ALL,
            };
            (name, vec![pred])
        }
        Some(Fold::CountingPredicate) => (
            operators::EXISTS_ONE,
            vec![first_arg(&c.loop_step).ok_or_else(shape)?],
        ),
        Some(Fold::Build) => match build_parts(&c.loop_step).ok_or_else(shape)? {
            (None, appended) => (operators::MAP, vec![appended]),
            // filter appends the iteration variable itself.
            (Some(p), appended) if matches!(&appended.expr, Expr::Ident(n) if *n == c.iter_var) => {
                (operators::FILTER, vec![p])
            }
            (Some(p), appended) => (operators::MAP, vec![p, appended]),
        },
        None => return Err(shape()),
    };
    write_operand(out, &c.iter_range)?;
    out.push('.');
    out.push_str(macro_name);
    out.push('(');
    write_name(out, &c.iter_var, "iteration variable")?;
    for p in parts {
        out.push_str(", ");
        write_expr(out, p)?;
    }
    out.push(')');
    Ok(())
}

fn write_literal(out: &mut String, v: &LiteralValue) -> Result<(), UnparseError> {
    match v {
        LiteralValue::Boolean(b) => out.push_str(if *b.inner() { "true" } else { "false" }),
        LiteralValue::Null => out.push_str("null"),
        LiteralValue::Int(i) => out.push_str(&i.to_string()),
        LiteralValue::Double(d) => {
            let f = *d.inner();
            if !f.is_finite() {
                return err("a non-finite double has no literal form");
            }
            // `{:?}` is the shortest spelling that round-trips, and it always carries a `.` or an
            // exponent (`7.0`, `1e21`, `1e-7`, `-0.0`) — `{}` would print `7`, which re-parses as
            // an Int, and the runtime keeps Int and Double apart.
            out.push_str(&format!("{f:?}"));
        }
        LiteralValue::String(s) => write_string(out, s.inner()),
        LiteralValue::Bytes(b) => write_bytes(out, b.inner()),
    }
    Ok(())
}

fn write_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

fn write_bytes(out: &mut String, b: &[u8]) {
    out.push_str("b\"");
    for &byte in b {
        match byte {
            b'\\' => out.push_str("\\\\"),
            b'"' => out.push_str("\\\""),
            0x20..=0x7e => out.push(byte as char),
            _ => out.push_str(&format!("\\x{byte:02x}")),
        }
    }
    out.push('"');
}
