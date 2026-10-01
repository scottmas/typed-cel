use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, Expr, IdedExpr, ListExpr, LiteralValue,
    OptionalRewrite, SelectExpr,
};
use crate::parser::{MacroExprHelper, ParseError};

pub type MacroExpander = fn(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError>;

pub fn find_expander(
    func_name: &str,
    target: Option<&IdedExpr>,
    args: &[IdedExpr],
) -> Option<MacroExpander> {
    match func_name {
        operators::HAS if args.len() == 1 && target.is_none() => Some(has_macro_expander),
        operators::EXISTS if args.len() == 2 && target.is_some() => Some(exists_macro_expander),
        operators::ALL if args.len() == 2 && target.is_some() => Some(all_macro_expander),
        operators::EXISTS_ONE | "existsOne" if args.len() == 2 && target.is_some() => {
            Some(exists_one_macro_expander)
        }
        operators::MAP if (args.len() == 2 || args.len() == 3) && target.is_some() => {
            Some(map_macro_expander)
        }
        operators::FILTER if args.len() == 2 && target.is_some() => Some(filter_macro_expander),
        // An optional read ends here (`added: optional reads`). Only on a target that IS an
        // optional chain: `x.orValue(d)` on a plain read reaches the checker's refusal.
        "orValue" if args.len() == 1 && target.is_some_and(is_optional_chain) => {
            Some(or_value_expander)
        }
        "hasValue" if args.is_empty() && target.is_some_and(is_optional_chain) => {
            Some(has_value_expander)
        }
        _ => None,
    }
}

fn has_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_some() {
        unreachable!("Got a target when expecting `None`!")
    }
    if args.len() != 1 {
        unreachable!("Expected a single arg!")
    }

    let ided_expr = args.remove(0);
    // `has(chain.f)`: presence through the chain, then of `f`.
    if let Expr::Select(select) = &ided_expr.expr {
        if let Some((root, segs, k0)) = flatten(&select.operand) {
            let (conj, last) = guards(helper, &root, &segs, k0);
            let has = helper.expr_for(
                ided_expr.id,
                Expr::Select(SelectExpr {
                    operand: Box::new(last),
                    field: select.field.clone(),
                    test: true,
                }),
            );
            return Ok(and(helper, conj, has));
        }
    }
    match ided_expr.expr {
        Expr::Select(mut select) => {
            select.test = true;
            Ok(helper.next_expr(Expr::Select(select)))
        }
        _ => Err(ParseError {
            source: None,
            pos: helper.pos_for(ided_expr.id).unwrap_or_default(),
            msg: "invalid argument to has() macro".to_string(),
            expr_id: 0,
            source_info: None,
        }),
    }
}

fn exists_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_none() {
        unreachable!("Expected a target, but got `None`!")
    }
    if args.len() != 2 {
        unreachable!("Expected two args!")
    }

    let mut arguments = vec![args.remove(1)];
    let v = extract_ident(args.remove(0), helper)?;

    let init = helper.next_expr(Expr::Literal(LiteralValue::Boolean(false.into())));
    let result_binding = "@result".to_string();
    let accu_ident = helper.next_expr(Expr::Ident(result_binding.clone()));
    let arg = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::LOGICAL_NOT.to_string(),
        target: None,
        args: vec![accu_ident],
    }));
    let condition = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::NOT_STRICTLY_FALSE.to_string(),
        target: None,
        args: vec![arg],
    }));

    arguments.insert(0, helper.next_expr(Expr::Ident(result_binding.clone())));
    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::LOGICAL_OR.to_string(),
        target: None,
        args: arguments,
    }));

    let result = helper.next_expr(Expr::Ident(result_binding.clone()));

    Ok(
        helper.next_expr(Expr::Comprehension(Box::new(ComprehensionExpr {
            iter_range: target.unwrap(),
            iter_var: v,
            iter_var2: None,
            accu_var: result_binding,
            accu_init: init,
            loop_cond: condition,
            loop_step: step,
            result,
        }))),
    )
}
fn all_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_none() {
        unreachable!("Expected a target, but got `None`!")
    }
    if args.len() != 2 {
        unreachable!("Expected two args!")
    }

    let mut arguments = vec![args.remove(1)];
    let v = extract_ident(args.remove(0), helper)?;

    let init = helper.next_expr(Expr::Literal(LiteralValue::Boolean(true.into())));
    let result_binding = "@result".to_string();
    let accu_ident = helper.next_expr(Expr::Ident(result_binding.clone()));
    let condition = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::NOT_STRICTLY_FALSE.to_string(),
        target: None,
        args: vec![accu_ident],
    }));

    arguments.insert(0, helper.next_expr(Expr::Ident(result_binding.clone())));
    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::LOGICAL_AND.to_string(),
        target: None,
        args: arguments,
    }));

    let result = helper.next_expr(Expr::Ident(result_binding.clone()));

    Ok(
        helper.next_expr(Expr::Comprehension(Box::new(ComprehensionExpr {
            iter_range: target.unwrap(),
            iter_var: v,
            iter_var2: None,
            accu_var: result_binding,
            accu_init: init,
            loop_cond: condition,
            loop_step: step,
            result,
        }))),
    )
}

fn exists_one_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_none() {
        unreachable!("Expected a target, but got `None`!")
    }
    if args.len() != 2 {
        unreachable!("Expected two args!")
    }

    let mut arguments = vec![args.remove(1)];
    let v = extract_ident(args.remove(0), helper)?;

    let init = helper.next_expr(Expr::Literal(LiteralValue::Int(0)));
    let result_binding = "@result".to_string();
    let condition = helper.next_expr(Expr::Literal(LiteralValue::Boolean(true.into())));

    let args = vec![
        helper.next_expr(Expr::Ident(result_binding.clone())),
        helper.next_expr(Expr::Literal(LiteralValue::Int(1))),
    ];
    arguments.push(helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::ADD.to_string(),
        target: None,
        args,
    })));
    arguments.push(helper.next_expr(Expr::Ident(result_binding.clone())));

    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::CONDITIONAL.to_string(),
        target: None,
        args: arguments,
    }));

    let accu = helper.next_expr(Expr::Ident(result_binding.clone()));
    let one = helper.next_expr(Expr::Literal(LiteralValue::Int(1)));
    let result = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::EQUALS.to_string(),
        target: None,
        args: vec![accu, one],
    }));

    Ok(
        helper.next_expr(Expr::Comprehension(Box::new(ComprehensionExpr {
            iter_range: target.unwrap(),
            iter_var: v,
            iter_var2: None,
            accu_var: result_binding,
            accu_init: init,
            loop_cond: condition,
            loop_step: step,
            result,
        }))),
    )
}

fn map_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_none() {
        unreachable!("Expected a target, but got `None`!")
    }
    if args.len() != 2 && args.len() != 3 {
        unreachable!("Expected two or three args!")
    }

    let func = args.pop().unwrap();
    let v = extract_ident(args.remove(0), helper)?;

    let init = helper.next_expr(Expr::List(ListExpr::new(Vec::default())));
    let result_binding = "@result".to_string();
    let condition = helper.next_expr(Expr::Literal(LiteralValue::Boolean(true.into())));

    let filter = args.pop();

    let args = vec![
        helper.next_expr(Expr::Ident(result_binding.clone())),
        helper.next_expr(Expr::List(ListExpr::new(vec![func]))),
    ];
    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::ADD.to_string(),
        target: None,
        args,
    }));

    let step = match filter {
        Some(filter) => {
            let accu = helper.next_expr(Expr::Ident(result_binding.clone()));
            helper.next_expr(Expr::Call(CallExpr {
                func_name: operators::CONDITIONAL.to_string(),
                target: None,
                args: vec![filter, step, accu],
            }))
        }
        None => step,
    };

    let result = helper.next_expr(Expr::Ident(result_binding.clone()));

    Ok(
        helper.next_expr(Expr::Comprehension(Box::new(ComprehensionExpr {
            iter_range: target.unwrap(),
            iter_var: v,
            iter_var2: None,
            accu_var: result_binding,
            accu_init: init,
            loop_cond: condition,
            loop_step: step,
            result,
        }))),
    )
}

fn filter_macro_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    if target.is_none() {
        unreachable!("Expected a target, but got `None`!")
    }
    if args.len() != 2 {
        unreachable!("Expected two args!")
    }

    let var = args.remove(0);
    let v = extract_ident(var.clone(), helper)?;
    let filter = args.pop().unwrap();

    let init = helper.next_expr(Expr::List(ListExpr::new(Vec::default())));
    let result_binding = "@result".to_string();
    let condition = helper.next_expr(Expr::Literal(LiteralValue::Boolean(true.into())));

    let args = vec![
        helper.next_expr(Expr::Ident(result_binding.clone())),
        helper.next_expr(Expr::List(ListExpr::new(vec![var]))),
    ];
    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::ADD.to_string(),
        target: None,
        args,
    }));

    let accu = helper.next_expr(Expr::Ident(result_binding.clone()));
    let step = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::CONDITIONAL.to_string(),
        target: None,
        args: vec![filter, step, accu],
    }));

    let result = helper.next_expr(Expr::Ident(result_binding.clone()));

    Ok(
        helper.next_expr(Expr::Comprehension(Box::new(ComprehensionExpr {
            iter_range: target.unwrap(),
            iter_var: v,
            iter_var2: None,
            accu_var: result_binding,
            accu_init: init,
            loop_cond: condition,
            loop_step: step,
            result,
        }))),
    )
}

fn extract_ident(expr: IdedExpr, helper: &mut MacroExprHelper) -> Result<String, ParseError> {
    match expr.expr {
        Expr::Ident(ident) => Ok(ident),
        _ => Err(ParseError {
            source: None,
            pos: helper.pos_for(expr.id).unwrap_or_default(),
            msg: "argument must be a simple name".to_string(),
            expr_id: 0,
            source_info: None,
        }),
    }
}

/// One read in an optional chain.
enum Seg {
    Field(String),
    Index(IdedExpr),
}

/// `(root, segments, index of the first optional segment)` — `None` when `e` has no optional
/// segment. A segment is a non-`test` `Select`, an `_[_]` call, `_?._` (a field) or `_[?_]` (an
/// index), each with the id of the authored node it came from; the root is the first node that is
/// none of these. Once a chain is optional every later segment is: a plain `.c` after `.?b` is
/// optional too, as spec CEL has it.
fn flatten(e: &IdedExpr) -> Option<(IdedExpr, Vec<(Seg, u64)>, usize)> {
    let mut segs = Vec::new();
    let mut optional = Vec::new();
    let mut cur = e;
    loop {
        match &cur.expr {
            Expr::Select(s) if !s.test => {
                segs.push((Seg::Field(s.field.clone()), cur.id));
                optional.push(false);
                cur = &s.operand;
            }
            Expr::Call(c) if c.target.is_none() && c.args.len() == 2 => {
                let seg = match (c.func_name.as_str(), &c.args[1].expr) {
                    (operators::INDEX, _) => (Seg::Index(c.args[1].clone()), false),
                    (operators::OPT_INDEX, _) => (Seg::Index(c.args[1].clone()), true),
                    (operators::OPT_SELECT, Expr::Literal(LiteralValue::String(f))) => {
                        (Seg::Field(f.inner().to_string()), true)
                    }
                    _ => break,
                };
                segs.push((seg.0, cur.id));
                optional.push(seg.1);
                cur = &c.args[0];
            }
            _ => break,
        }
    }
    segs.reverse();
    optional.reverse();
    let k0 = optional.iter().position(|o| *o)?;
    Some((cur.clone(), segs, k0))
}

fn is_optional_chain(e: &IdedExpr) -> bool {
    flatten(e).is_some()
}

/// `root` followed by `segs`, as PLAIN reads — every node a fresh copy.
fn plain(helper: &mut MacroExprHelper, root: &IdedExpr, segs: &[(Seg, u64)]) -> IdedExpr {
    let mut e = helper.copy(root);
    for (seg, id) in segs {
        e = match seg {
            Seg::Field(f) => helper.expr_for(
                *id,
                Expr::Select(SelectExpr {
                    operand: Box::new(e),
                    field: f.clone(),
                    test: false,
                }),
            ),
            Seg::Index(k) => {
                let k = helper.copy(k);
                helper.expr_for(
                    *id,
                    Expr::Call(CallExpr {
                        func_name: operators::INDEX.to_string(),
                        target: None,
                        args: vec![e, k],
                    }),
                )
            }
        };
    }
    e
}

fn and(helper: &mut MacroExprHelper, a: IdedExpr, b: IdedExpr) -> IdedExpr {
    helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::LOGICAL_AND.to_string(),
        target: None,
        args: vec![a, b],
    }))
}

/// `test(k0) && … && test(n)` over the chain, and `P_n` — the chain read plainly. `test(i)` is
/// `has(P_{i-1}.f)` for a field and `k in P_{i-1}` for an index, so each conjunct proves its path
/// and every prefix, and every read in `P_n` and in each later test is proven by its siblings.
/// `P_{k0-1}`, the plain prefix before the first `.?`, is an ordinary read nothing here proves.
fn guards(
    helper: &mut MacroExprHelper,
    root: &IdedExpr,
    segs: &[(Seg, u64)],
    k0: usize,
) -> (IdedExpr, IdedExpr) {
    let mut conj: Option<IdedExpr> = None;
    for (i, (seg, id)) in segs.iter().enumerate().skip(k0) {
        let prefix = plain(helper, root, &segs[..i]);
        let test = match seg {
            Seg::Field(f) => helper.expr_for(
                *id,
                Expr::Select(SelectExpr {
                    operand: Box::new(prefix),
                    field: f.clone(),
                    test: true,
                }),
            ),
            Seg::Index(k) => {
                let k = helper.copy(k);
                let test = helper.expr_for(
                    *id,
                    Expr::Call(CallExpr {
                        func_name: operators::IN.to_string(),
                        target: None,
                        args: vec![k, prefix],
                    }),
                );
                helper.mark(test.id, OptionalRewrite::IndexPresence);
                test
            }
        };
        conj = Some(match conj {
            None => test,
            Some(c) => and(helper, c, test),
        });
    }
    let last = plain(helper, root, segs);
    (conj.expect("a chain has an optional segment"), last)
}

/// `chain.orValue(d)` -> `test(k0) && … && test(n) ? P_n : d`. The default is evaluated only when
/// the value is absent (`diverges: orValue's default is lazy`).
fn or_value_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    mut args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    let target = target.expect("`orValue` is a method");
    let default = args.remove(0);
    let (root, segs, k0) = flatten(&target).expect("an optional chain");
    let (conj, last) = guards(helper, &root, &segs, k0);
    let read = crate::unparse::unparse(&target).unwrap_or_else(|_| "the read".to_string());
    let rendered_default =
        crate::unparse::unparse(&default).unwrap_or_else(|_| "the default".to_string());
    let e = helper.next_expr(Expr::Call(CallExpr {
        func_name: operators::CONDITIONAL.to_string(),
        target: None,
        args: vec![conj, last, default],
    }));
    helper.mark(
        e.id,
        OptionalRewrite::OrValue {
            read,
            default: rendered_default,
        },
    );
    Ok(e)
}

/// `chain.hasValue()` -> `test(k0) && … && test(n)`.
fn has_value_expander(
    helper: &mut MacroExprHelper,
    target: Option<IdedExpr>,
    _args: Vec<IdedExpr>,
) -> Result<IdedExpr, ParseError> {
    let target = target.expect("`hasValue` is a method");
    let (root, segs, k0) = flatten(&target).expect("an optional chain");
    Ok(guards(helper, &root, &segs, k0).0)
}
