//! The mix equation's harness: a typed roster, a generator of programs and bindings over it, and
//! the one row function every mix test compares through.
//!
//! For a checked boolean program `P`, a set `K` of roots bound as known and a completion `U`
//! binding every other declared root, one ROW is:
//!
//! ```text
//! column 1   P.evaluate(K ∪ U)                          the original, over bound values
//! column 2   env.specialize(P, K)?.evaluate(U)          the residual, over bound values
//! column 3   residual.decide(JsonFacts(U))              the residual, read by field
//! column 4   P.decide(JsonFacts(K ∪ U))                 a GUARD: the original, read by field
//! ```
//!
//! Columns 3 and 4 exist only for a program whose fields are all scalars (`Facts` answers scalars
//! only); the row counts how often each ran. Four DIFFERENT computations: two programs, each on two
//! hosts.
//!
//! Two outcomes AGREE when both are `Ok(b)` with the same `b`, or both are `Err(_)`. Error
//! identity is never compared: an evaluation error embeds the program's source text, which differs
//! between `P` and its residual by construction.
//!
//! Precondition of the property: every bound value conforms to its declared type. `bind` enforces
//! that for JSON, and this harness binds through `bind` only.

use serde_json::{json, Value as J};
use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::{
    CelActivation, CelEnvironment, CelError, CelLimits, CelProgram, CelTy, FastProgram, FastScratch,
};

use super::gen::{Gen, JsonFacts};
use super::record_opt;

/// Every root of [`roster`], in declaration order.
pub const ROOTS: [&str; 11] = ["a", "b", "s", "t", "p", "q", "ls", "ln", "d", "r", "m"];

/// Every root is sometimes known and sometimes not; nothing about a name decides which.
pub fn roster(limits: CelLimits) -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(limits);
    e.declare("a", CelTy::Num)
        .declare("b", CelTy::Num)
        .declare("s", CelTy::Str)
        .declare("t", CelTy::Str)
        .declare("p", CelTy::Bool)
        .declare("q", CelTy::Bool)
        .declare("ls", CelTy::list(CelTy::Str))
        .declare("ln", CelTy::list(CelTy::Num))
        .declare("d", CelTy::Duration)
        .declare(
            "r",
            record_opt(
                "r",
                &[
                    ("n", CelTy::Num),
                    ("s", CelTy::Str),
                    ("l", CelTy::list(CelTy::Str)),
                    ("o", CelTy::Str),
                ],
                &["o"],
            ),
        )
        .declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    e
}

// ---- one row ----

/// A column's outcome, with an error rendered for the report.
pub type Outcome = Result<bool, String>;

fn outcome(r: Result<bool, CelError>) -> Outcome {
    r.map_err(|e| e.to_string())
}

/// `Ok(b)` with the same `b`, or `Err` on both sides.
pub fn agree(x: &Outcome, y: &Outcome) -> bool {
    match (x, y) {
        (Ok(a), Ok(b)) => a == b,
        (Err(_), Err(_)) => true,
        _ => false,
    }
}

const EMIT_FAILED: &str = "EMIT FAILED";

/// One evaluated case.
pub struct Row {
    pub source: String,
    pub known: Vec<(&'static str, J)>,
    pub completion: Vec<(&'static str, J)>,
    pub max_unroll: usize,
    /// `fork::unparse` of the original tree — what the residual's `source()` would be if nothing
    /// folded.
    pub original_rendered: String,
    pub original_loops: usize,
    /// `Err` is a failing row: `specialize` refusing a program `compile` accepted.
    pub residual: Result<CelProgram, String>,
    pub residual_loops: usize,
    pub c1: Outcome,
    pub c2: Outcome,
    /// `None`: the residual reads a field `Facts` does not serve.
    pub c3: Option<Outcome>,
    /// `None`: the original reads a field `Facts` does not serve.
    pub c4: Option<Outcome>,
}

impl Row {
    /// The property: columns 2 and 3 agree with column 1.
    pub fn holds(&self) -> bool {
        self.ran_fast()
            && agree(&self.c1, &self.c2)
            && self.c3.as_ref().is_none_or(|c3| agree(&self.c1, c3))
    }

    /// Did the residual lower? There is no fallback: a residual the backend cannot lower is a
    /// failing row.
    pub fn ran_fast(&self) -> bool {
        self.residual.is_ok() && !matches!(&self.c2, Err(e) if e.starts_with(EMIT_FAILED))
    }

    /// The guard: the original read by field agrees with the original over bound values. When it
    /// does not, a column-3 disagreement is a host defect, not a specializer one.
    pub fn guard_holds(&self) -> bool {
        self.c4.as_ref().is_none_or(|c4| agree(&self.c1, c4))
    }

    pub fn residual_source(&self) -> &str {
        match &self.residual {
            Ok(p) => p.source(),
            Err(_) => "<no residual>",
        }
    }

    /// Everything a reader needs to reproduce and triage the row.
    pub fn report(&self, label: &str) -> String {
        let blame = if !self.guard_holds() {
            "HOST DEFECT (column 4 disagrees with column 1 on the ORIGINAL program; \
             tests/metamorphic.rs::every_host_answers_alike should have caught it)"
        } else if let Err(e) = &self.residual {
            return format!(
                "{label}\n  specialize REFUSED a program compile accepted: {e}\n{}",
                self.context()
            );
        } else {
            "SPECIALIZER DEFECT"
        };
        format!(
            "{label}: {blame}\n{}\n  column 1 (P, K ∪ U):             {:?}\n  column 2 (residual, U):          {:?}\n  column 3 (residual, Facts U):    {:?}\n  column 4 (P, Facts K ∪ U):       {:?}",
            self.context(),
            self.c1,
            self.c2,
            self.c3,
            self.c4
        )
    }

    fn context(&self) -> String {
        let obj = |pairs: &[(&str, J)]| {
            J::Object(
                pairs
                    .iter()
                    .map(|(k, v)| (k.to_string(), v.clone()))
                    .collect(),
            )
        };
        format!(
            "  authored:   {}\n  known:      {}\n  completion: {}\n  max_unroll: {}\n  residual:   {}",
            self.source,
            obj(&self.known),
            obj(&self.completion),
            self.max_unroll,
            self.residual_source()
        )
    }
}

fn bind_all(env: &CelEnvironment, pairs: &[(&str, J)]) -> CelActivation {
    let mut a = env.activation();
    for (name, value) in pairs {
        a.bind(name, value)
            .unwrap_or_else(|e| panic!("`{name}` = {value} binds: {e}"));
    }
    a
}

/// Evaluate one case in all four columns. A program `compile` refuses is a GENERATOR bug and
/// panics with its source — it is never skipped.
pub fn row(
    env: &CelEnvironment,
    source: &str,
    known: Vec<(&'static str, J)>,
    completion: Vec<(&'static str, J)>,
) -> Row {
    let original = env
        .compile(source)
        .unwrap_or_else(|e| panic!("GENERATOR BUG: `{source}` does not compile:\n{e}"));
    let full: Vec<(&str, J)> = known.iter().chain(completion.iter()).cloned().collect();
    let k = bind_all(env, &known);
    let u = bind_all(env, &completion);
    let ku = bind_all(env, &full);

    let facts = |p: &CelProgram, json: &[(&str, J)]| -> Option<Outcome> {
        let code = FastProgram::new(p).ok()?;
        // `d` is the roster's one duration; JSON spells it as a string, which `JsonFacts` would
        // serve as one. A duration read by field is `Facts::duration_ms`, not exercised here.
        if code.fields().iter().any(|f| f.root() == "d") {
            return None;
        }
        let f = JsonFacts::new(code.fields(), json)?;
        Some(outcome(code.decide(&f, &mut FastScratch::default())))
    };
    let c1 = outcome(original.evaluate(&ku));
    let c4 = facts(&original, &full);
    let original_tree = typed_cel::fork::expression_of(&original);
    let original_rendered =
        typed_cel::fork::unparse(original_tree).expect("a compiled tree renders");
    let original_loops = comprehensions(original_tree);

    let residual = env.specialize(&original, &k).map_err(|e| e.to_string());
    let (c2, c3, residual_loops) = match &residual {
        Ok(res) => {
            // A residual the backend cannot lower is a defect in its own right; it is reported as
            // a column value that no `Ok` or evaluation error can be mistaken for.
            let c2 = match FastProgram::new(res) {
                Ok(_) => outcome(res.evaluate(&u)),
                Err(e) => Err(format!("{EMIT_FAILED} on the residual: {e}")),
            };
            let c3 = facts(res, &completion);
            (c2, c3, comprehensions(typed_cel::fork::expression_of(res)))
        }
        Err(e) => (Err(e.clone()), None, original_loops),
    };
    Row {
        source: source.to_string(),
        known,
        completion,
        max_unroll: env.limits().max_unroll,
        original_rendered,
        original_loops,
        residual,
        residual_loops,
        c1,
        c2,
        c3,
        c4,
    }
}

/// How many `Expr::Comprehension` nodes `e` holds.
pub fn comprehensions(e: &IdedExpr) -> usize {
    let own = usize::from(matches!(e.expr, Expr::Comprehension(_)));
    own + match &e.expr {
        Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => 0,
        Expr::Select(s) => comprehensions(&s.operand),
        Expr::Call(c) => {
            c.target.as_deref().map_or(0, comprehensions)
                + c.args.iter().map(comprehensions).sum::<usize>()
        }
        Expr::List(l) => l.elements.iter().map(comprehensions).sum(),
        Expr::Map(m) => m
            .entries
            .iter()
            .map(|en| {
                let EntryExpr::MapEntry(me) = &en.expr;
                comprehensions(&me.key) + comprehensions(&me.value)
            })
            .sum(),
        Expr::Comprehension(c) => [
            &c.iter_range,
            &c.accu_init,
            &c.loop_cond,
            &c.loop_step,
            &c.result,
        ]
        .into_iter()
        .map(comprehensions)
        .sum(),
    }
}

// ---- generating cases ----

/// One generated case: the program, the known and completion bindings, and the limits.
pub struct Case {
    pub source: String,
    pub known: Vec<(&'static str, J)>,
    pub completion: Vec<(&'static str, J)>,
    pub limits: CelLimits,
}

/// Draw case `index` of a run. Every root is known with probability 1/2, except that every 50th
/// case knows all of them and every 50th + 25 knows none.
pub fn case(g: &mut Gen, index: usize) -> Case {
    let source = MixGen {
        g: &mut *g,
        used: Vec::new(),
    }
    .boolean(4, &mut Vec::new());
    let values = values(g);
    let (mut known, mut completion) = (Vec::new(), Vec::new());
    for (name, value) in values {
        let is_known = match index % 50 {
            0 => true,
            25 => false,
            _ => g.below(2) == 0,
        };
        if is_known {
            known.push((name, value));
        } else {
            completion.push((name, value));
        }
    }
    let max_unroll = [0, 1, 2, 256][g.below(4)];
    Case {
        source,
        known,
        completion,
        limits: CelLimits {
            max_unroll,
            ..CelLimits::default()
        },
    }
}

const NUMS: [f64; 6] = [0.0, 1.0, -1.0, 2.5, 7.0, 100.0];
const STRS: [&str; 7] = ["", "a", "b", "ab", "/etc", "/etc/x", "/etcetera"];
const DURATIONS: [&str; 4] = ["0s", "1s", "90s", "-5ms"];

/// A value for every root of [`roster`], in [`ROOTS`] order.
pub fn values(g: &mut Gen) -> Vec<(&'static str, J)> {
    let num = |g: &mut Gen| json!(NUMS[g.below(NUMS.len())]);
    let str_ = |g: &mut Gen| J::from(STRS[g.below(STRS.len())]);
    let strs = |g: &mut Gen| J::Array((0..g.below(5)).map(|_| str_(g)).collect());
    let nums = |g: &mut Gen| J::Array((0..g.below(5)).map(|_| num(g)).collect());
    let mut r = serde_json::Map::new();
    r.insert("n".into(), num(g));
    r.insert("s".into(), str_(g));
    r.insert("l".into(), strs(g));
    if g.below(2) == 0 {
        r.insert("o".into(), str_(g));
    }
    let mut m = serde_json::Map::new();
    for _ in 0..g.below(4) {
        m.insert(STRS[g.below(STRS.len())].to_string(), num(g));
    }
    vec![
        ("a", num(g)),
        ("b", num(g)),
        ("s", str_(g)),
        ("t", str_(g)),
        ("p", J::Bool(g.below(2) == 0)),
        ("q", J::Bool(g.below(2) == 0)),
        ("ls", strs(g)),
        ("ln", nums(g)),
        ("d", J::from(DURATIONS[g.below(DURATIONS.len())])),
        ("r", J::Object(r)),
        ("m", J::Object(m)),
    ]
}

/// A comprehension variable in scope: its name and whether it is a `num` (else a `str`).
type Var = (&'static str, bool);

/// The names a nested comprehension variable takes, one per nesting level. None is a root.
const STR_VARS: [&str; 2] = ["x", "y"];
const NUM_VARS: [&str; 2] = ["i", "j"];

/// The typed grammar. Every production is checker-valid over [`roster`].
struct MixGen<'g> {
    g: &'g mut Gen,
    /// Every comprehension variable a leaf has read, in order — how a scoped body proves it used
    /// its variable.
    used: Vec<&'static str>,
}

const CMP: [&str; 6] = ["<", "<=", "==", "!=", ">", ">="];
const STR_LITS: [&str; 5] = ["\"\"", "\"a\"", "\"b\"", "\"/etc\"", "\"/etc/x\""];

impl MixGen<'_> {
    fn below(&mut self, n: usize) -> usize {
        self.g.below(n)
    }

    fn pick(&mut self, xs: &[&'static str]) -> &'static str {
        self.g.pick(xs)
    }

    fn boolean(&mut self, depth: u32, scope: &mut Vec<Var>) -> String {
        if depth == 0 {
            return self
                .pick(&["p", "q", "true", "false", "has(r.o)"])
                .to_string();
        }
        let d = depth - 1;
        // A third nested comprehension multiplies the checker's cost estimate past `max_cost`.
        let loops = scope.len() < 2;
        let mut roll = self.below(38);
        if !loops && (24..=33).contains(&roll) {
            roll = 4;
        }
        match roll {
            0 => self.pick(&["p", "q", "true", "false"]).to_string(),
            1..=3 => {
                let op = self.pick(&CMP);
                format!(
                    "({} {op} {})",
                    self.cmp_num(d, scope),
                    self.cmp_num(d, scope)
                )
            }
            4 => format!("({} == {})", self.string(d, scope), self.string(d, scope)),
            5 | 6 => {
                let f = self.pick(&["startsWith", "endsWith", "contains"]);
                format!("{}.{f}({})", self.string(d, scope), self.string(d, scope))
            }
            7 => format!("{}.matches(\"^/etc\")", self.string(d, scope)),
            8 => format!("({} in {})", self.string(d, scope), self.list(d, scope)),
            9 => format!("({} in ln)", self.num(d, scope)),
            10 => format!("({} in m)", self.string(d, scope)),
            11..=13 => format!("({} && {})", self.boolean(d, scope), self.boolean(d, scope)),
            14..=16 => format!("({} || {})", self.boolean(d, scope), self.boolean(d, scope)),
            17 => format!("(!{})", self.boolean(d, scope)),
            18 => format!(
                "({} ? {} : {})",
                self.boolean(d, scope),
                self.boolean(d, scope),
                self.boolean(d, scope)
            ),
            19 => "has(r.o)".to_string(),
            20 => format!("(d {} duration(\"1s\"))", self.pick(&CMP)),
            21 => format!("(size({}) > {})", self.list(d, scope), self.num(d, scope)),
            22 => self.pick(&["(1 / 0 == 1)", "(ln[3] > 0.0)"]).to_string(),
            23 => format!("(r.o == {})", self.string(d, scope)),
            24 | 25 => {
                let q = self.pick(&["exists", "all", "exists_one"]);
                let range = self.list(d, scope);
                let (v, body) = self.scoped_str(d, scope);
                format!("{range}.{q}({v}, {body})")
            }
            26 => {
                let q = self.pick(&["exists", "all"]);
                let (v, body) = self.scoped_num(d, scope);
                format!("ln.{q}({v}, {body})")
            }
            27 => {
                scope.push(("k", false));
                let n = self.num(d, scope);
                scope.pop();
                format!("m.all(k, m[k] > {n})")
            }
            // An element that errors for SOME elements beside a bool that may decide the chain:
            // what reaches absorption inside an unrolled or kept loop.
            28 | 29 => {
                let q = self.pick(&["exists", "all"]);
                let op = if q == "exists" { "||" } else { "&&" };
                let range = self.list(d, scope);
                let v = STR_VARS[scope.len()];
                scope.push((v, false));
                self.used.push(v);
                let other = self.boolean(d, scope);
                scope.pop();
                // An integer division by zero for the empty element only.
                let erring = self
                    .pick(&["(1 / ({v} == \"\" ? 0 : 1) == 1)", "({v} == r.o)"])
                    .replace("{v}", v);
                if self.below(2) == 0 {
                    format!("{range}.{q}({v}, {erring} {op} {other})")
                } else {
                    format!("{range}.{q}({v}, {other} {op} {erring})")
                }
            }
            // A loop whose elements the fold DECIDES with the identity value, except the empty
            // one, which reads `r.o` — undecided when `r` is unknown, an error when `o` is
            // absent. Over a known range the decided copies must drop out of the unrolled chain
            // and never end it: only the absorbing value may.
            30..=33 => {
                let range = self.pick(&["ls", "r.l"]);
                let v = STR_VARS[scope.len()];
                let (q, decided) = if self.below(2) == 0 {
                    ("all", format!("{v} != \"#\""))
                } else {
                    ("exists", format!("{v} == \"#\""))
                };
                format!("{range}.{q}({v}, {v} == \"\" ? (r.o == {v}) : {decided})")
            }
            // An erroring operand beside a (possibly known) absorbing one, outside any loop.
            _ => {
                let erring = self.pick(&[
                    "(r.o == s)",
                    "(1 / 0 == 1)",
                    "(ln[3] > 0.0)",
                    "(m[\"a\"] > 0.0)",
                ]);
                let other = self.boolean(d, scope);
                let op = self.pick(&["&&", "||"]);
                if self.below(2) == 0 {
                    format!("({erring} {op} {other})")
                } else {
                    format!("({other} {op} {erring})")
                }
            }
        }
    }

    /// A bool body with a fresh `str` comprehension variable that the body actually reads.
    fn scoped_str(&mut self, depth: u32, scope: &mut Vec<Var>) -> (&'static str, String) {
        let v = STR_VARS[scope.len()];
        (v, self.scoped(v, false, depth, scope))
    }

    /// A bool body with a fresh `num` comprehension variable that the body actually reads.
    fn scoped_num(&mut self, depth: u32, scope: &mut Vec<Var>) -> (&'static str, String) {
        let v = NUM_VARS[scope.len()];
        (v, self.scoped(v, true, depth, scope))
    }

    fn scoped(
        &mut self,
        v: &'static str,
        is_num: bool,
        depth: u32,
        scope: &mut Vec<Var>,
    ) -> String {
        scope.push((v, is_num));
        let before = self.used.len();
        let body = self.boolean(depth, scope);
        let read = self.used[before..].contains(&v);
        let body = if read {
            body
        } else {
            // The body never reached the variable: join it with a comparison that does.
            let use_it = if is_num {
                let op = self.pick(&CMP);
                format!("({v} {op} {})", self.num(depth.saturating_sub(1), scope))
            } else {
                let f = self.pick(&["startsWith", "endsWith", "contains"]);
                format!("{v}.{f}({})", self.string(depth.saturating_sub(1), scope))
            };
            let op = self.pick(&["&&", "||"]);
            format!("({use_it} {op} {body})")
        };
        self.used.push(v);
        scope.pop();
        body
    }

    /// A `num` operand of a comparison — an integer LITERAL, which widens to a double and keeps its
    /// rows `Ok`.
    fn cmp_num(&mut self, depth: u32, scope: &mut Vec<Var>) -> String {
        if self.below(6) == 0 {
            return self.pick(&["1", "2"]).to_string();
        }
        self.num(depth, scope)
    }

    fn num(&mut self, depth: u32, scope: &mut Vec<Var>) -> String {
        let vars: Vec<&'static str> = scope.iter().filter(|v| v.1).map(|v| v.0).collect();
        if depth == 0 || self.below(2) == 0 {
            if !vars.is_empty() && self.below(2) == 0 {
                let v = vars[self.below(vars.len())];
                self.used.push(v);
                return v.to_string();
            }
            return self
                .pick(&[
                    "a", "b", "r.n", "ln[0]", "m[\"a\"]", "0.0", "1.0", "2.5", "-1.0",
                ])
                .to_string();
        }
        let d = depth - 1;
        match self.below(6) {
            0 => format!("({} + {})", self.num(d, scope), self.num(d, scope)),
            1 => format!("({} - {})", self.num(d, scope), self.num(d, scope)),
            2 => format!("({} * {})", self.num(d, scope), self.num(d, scope)),
            3 => format!("({} / {})", self.num(d, scope), self.num(d, scope)),
            4 => format!("(-{})", self.num(d, scope)),
            _ => format!(
                "({} ? {} : {})",
                self.boolean(d, scope),
                self.num(d, scope),
                self.num(d, scope)
            ),
        }
    }

    fn string(&mut self, depth: u32, scope: &mut Vec<Var>) -> String {
        let vars: Vec<&'static str> = scope.iter().filter(|v| !v.1).map(|v| v.0).collect();
        if depth == 0 || self.below(3) != 0 {
            if !vars.is_empty() && self.below(2) == 0 {
                let v = vars[self.below(vars.len())];
                self.used.push(v);
                return v.to_string();
            }
            let leaf = self.pick(&["s", "t", "r.s", "ls[0]", "", "", ""]);
            if leaf.is_empty() {
                return self.pick(&STR_LITS).to_string();
            }
            return leaf.to_string();
        }
        let d = depth - 1;
        if self.below(3) == 0 {
            format!(
                "({} ? {} : {})",
                self.boolean(d, scope),
                self.string(d, scope),
                self.string(d, scope)
            )
        } else {
            format!("({} + {})", self.string(d, scope), self.string(d, scope))
        }
    }

    fn list(&mut self, depth: u32, scope: &mut Vec<Var>) -> String {
        if depth == 0 || self.below(2) == 0 {
            return self.pick(&["ls", "r.l"]).to_string();
        }
        let d = depth - 1;
        let loops = scope.len() < 2;
        match self.below(if loops { 3 } else { 1 }) {
            0 => format!("[\"x\", {}]", self.string(d, scope)),
            1 => {
                let range = self.list(d, scope);
                let v = STR_VARS[scope.len()];
                scope.push((v, false));
                let appended = self.string(d, scope);
                scope.pop();
                format!("{range}.map({v}, {v} + {appended})")
            }
            _ => {
                let range = self.list(d, scope);
                let (v, body) = self.scoped_str(d, scope);
                format!("{range}.filter({v}, {body})")
            }
        }
    }
}
