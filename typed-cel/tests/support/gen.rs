//! Holding the backend to the evaluator: the comparison helpers every differential shares, and the
//! generator `tests/vm_differential.rs` runs them over.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use typed_cel::fork::objects::Value;
use typed_cel::{CelEnvironment, CelError, CelKey, CelTy, CelValue, ExecutionError, LazyValue};

/// Kind-strict structural equality. `Value`'s own `PartialEq` says `NaN != NaN`, which is not what
/// "the VM agrees" means. Maps compare by
/// length and per-key lookup, never by `Debug` text — each `HashMap` iterates in its own random
/// order.
pub fn same_value(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => (x.is_nan() && y.is_nan()) || x == y,
        (Value::String(x), Value::String(y)) => x == y,
        (Value::Bytes(x), Value::Bytes(y)) => x == y,
        (Value::Duration(x), Value::Duration(y)) => x == y,
        (Value::List(x), Value::List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| same_value(p, q))
        }
        (Value::Map(x), Value::Map(y)) => {
            x.map.len() == y.map.len()
                && x.map
                    .iter()
                    .all(|(k, v)| y.map.get(k).is_some_and(|w| same_value(v, w)))
        }
        (Value::Opaque(_), Value::Opaque(_)) => a == b,
        _ => false,
    }
}

/// Errors by `==` (a map inside an error compares order-free that way), falling back to `Debug`
/// text so an error carrying a NaN still matches itself.
pub fn same_error(a: &ExecutionError, b: &ExecutionError) -> bool {
    a == b || format!("{a:?}") == format!("{b:?}")
}

/// Both `Ok` with [`same_value`]s, or both `Err` with [`same_error`]s.
pub fn same_outcome(a: &Result<Value, ExecutionError>, b: &Result<Value, ExecutionError>) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => same_value(x, y),
        (Err(x), Err(y)) => same_error(x, y),
        _ => false,
    }
}

// ---- generating what to compare them on ----

/// The seeds every generated run uses. Fixed, so a failure reproduces from its printed
/// (seed, index) with no environment variable — remote `cargo` does not forward one.
pub const SEEDS: [u64; 3] = [
    0x9E37_79B9_7F4A_7C15,
    0xD1B5_4A32_D192_ED03,
    0x2545_F491_4F6C_DD1D,
];

/// A typed comprehension variable in scope: its name and whether it is a `Num` (else a `Str`).
type Typed = (&'static str, bool);

/// xorshift64*. The crate has no RNG dependency and this needs none.
pub struct Gen {
    s: u64,
}

impl Gen {
    pub fn new(seed: u64) -> Gen {
        Gen { s: seed.max(1) }
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.s;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.s = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    pub fn pick(&mut self, xs: &[&'static str]) -> &'static str {
        xs[self.below(xs.len())]
    }

    /// A checker-valid `bool` expression over `roster()`.
    pub fn typed_bool(&mut self, depth: u32) -> String {
        self.boolean(depth, &mut Vec::new())
    }

    // ---- the typed grammar ----

    fn boolean(&mut self, depth: u32, scope: &mut Vec<Typed>) -> String {
        if depth == 0 {
            return self
                .pick(&["f", "true", "false", "has(r.o)", "('a' in m)"])
                .to_string();
        }
        let d = depth - 1;
        const CMP: &[&str] = &["==", "!=", "<", "<=", ">", ">="];
        let mut roll = self.below(22);
        // A third nested comprehension multiplies the checker's cost estimate past
        // `CelLimits::max_cost` (100 assumed elements per level), so at two levels deep the
        // comprehension rows become the `size(xs)` row.
        if scope.len() >= 2 && (15..=18).contains(&roll) {
            roll = 19;
        }
        match roll {
            0 => self.pick(&["f", "true", "false"]).to_string(),
            1 | 2 => {
                let op = self.pick(CMP);
                format!("({} {op} {})", self.num(d, scope), self.num(d, scope))
            }
            3 => {
                let op = self.pick(&["==", "!=", "<"]);
                format!("({} {op} {})", self.string(d, scope), self.string(d, scope))
            }
            4 | 5 => format!("({} && {})", self.boolean(d, scope), self.boolean(d, scope)),
            6 | 7 => format!("({} || {})", self.boolean(d, scope), self.boolean(d, scope)),
            8 => format!("(!{})", self.boolean(d, scope)),
            9 => format!(
                "({} ? {} : {})",
                self.boolean(d, scope),
                self.boolean(d, scope),
                self.boolean(d, scope)
            ),
            10 => {
                let m = self.pick(&["startsWith", "contains", "endsWith"]);
                format!("{}.{m}({})", self.string(d, scope), self.string(d, scope))
            }
            11 => format!("({} in ss)", self.string(d, scope)),
            12 => format!("({} in xs)", self.num(d, scope)),
            13 => "('a' in m)".to_string(),
            14 => "has(r.o)".to_string(),
            15 | 16 => {
                let q = self.pick(&["all", "exists", "exists_one"]);
                scope.push(("x", true));
                let body = self.boolean(d, scope);
                scope.pop();
                format!("xs.{q}(x, {body})")
            }
            17 => {
                let q = self.pick(&["all", "exists", "exists_one"]);
                scope.push(("v", false));
                let body = self.boolean(d, scope);
                scope.pop();
                format!("ss.{q}(v, {body})")
            }
            18 => {
                let q = self.pick(&["all", "exists", "exists_one"]);
                scope.push(("k", false));
                let body = self.boolean(d, scope);
                scope.pop();
                format!("m.{q}(k, {body})")
            }
            _ => {
                let op = self.pick(CMP);
                format!("(size(xs) {op} {})", self.num(d, scope))
            }
        }
    }

    /// A `Num`. `1` and `0` are integer LITERALS: they parse as written and are doubles once
    /// evaluated, so beside a bound double they exercise the widening rather than a mismatch.
    fn num(&mut self, depth: u32, scope: &mut Vec<Typed>) -> String {
        let vars: Vec<&'static str> = scope.iter().filter(|v| v.1).map(|v| v.0).collect();
        let leaf = |g: &mut Gen| -> String {
            if !vars.is_empty() && g.below(3) == 0 {
                return vars[g.below(vars.len())].to_string();
            }
            g.pick(&[
                "n", "r.a", "r.o", "xs[0]", "m['a']", "m['z']", "0.0", "1.0", "2.5", "1", "0",
                "size(xs)",
            ])
            .to_string()
        };
        if depth == 0 || self.below(2) == 0 {
            return leaf(self);
        }
        let op = self.pick(&["+", "-", "*", "/"]);
        format!(
            "({} {op} {})",
            self.num(depth - 1, scope),
            self.num(depth - 1, scope)
        )
    }

    fn string(&mut self, depth: u32, scope: &mut Vec<Typed>) -> String {
        let vars: Vec<&'static str> = scope.iter().filter(|v| !v.1).map(|v| v.0).collect();
        if depth == 0 || self.below(3) != 0 {
            if !vars.is_empty() && self.below(3) == 0 {
                return vars[self.below(vars.len())].to_string();
            }
            return self.pick(&["s", "r.t", "ss[0]", "'a'", "''"]).to_string();
        }
        format!(
            "({} + {})",
            self.string(depth - 1, scope),
            self.string(depth - 1, scope)
        )
    }
}

/// The roster the typed modes compile against. `r.o` is OPTIONAL so a binding can omit it and
/// `r.o` / `has(r.o)` reach `NoSuchKey` / `false` at run time.
pub fn roster() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare("n", CelTy::Num);
    e.declare("s", CelTy::Str);
    e.declare("f", CelTy::Bool);
    e.declare("xs", CelTy::list(CelTy::Num));
    e.declare("ss", CelTy::list(CelTy::Str));
    e.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    e.declare(
        "r",
        super::record_opt(
            "r",
            &[("a", CelTy::Num), ("t", CelTy::Str), ("o", CelTy::Num)],
            &["o"],
        ),
    );
    e
}

/// One binding per root of `roster()`.
pub fn typed_json(g: &mut Gen) -> Vec<(&'static str, serde_json::Value)> {
    use serde_json::{json, Value as J};
    let nums = [json!(0), json!(1), json!(-2.5), json!(3)];
    let strs = ["", "a", "ab", "b"];
    let num = |g: &mut Gen| nums[g.below(nums.len())].clone();
    let n = num(g);
    let s = J::from(strs[g.below(strs.len())]);
    let f = J::Bool(g.below(2) == 0);
    let xs = J::Array((0..g.below(4)).map(|_| num(g)).collect());
    let ss = J::Array(
        (0..g.below(4))
            .map(|_| J::from(strs[g.below(strs.len())]))
            .collect(),
    );
    let mut m = serde_json::Map::new();
    for k in ["a", "b", "c"] {
        if g.below(2) == 0 {
            m.insert(k.to_string(), num(g));
        }
    }
    let mut r = serde_json::Map::new();
    r.insert("a".into(), num(g));
    r.insert("t".into(), J::from(strs[g.below(strs.len())]));
    if g.below(2) == 0 {
        r.insert("o".into(), num(g));
    }
    vec![
        ("n", n),
        ("s", s),
        ("f", f),
        ("xs", xs),
        ("ss", ss),
        ("m", J::Object(m)),
        ("r", J::Object(r)),
    ]
}

/// A `LazyValue` over a JSON object that counts every `member` and `keys` call.
#[derive(Debug)]
pub struct JsonLazy {
    fields: serde_json::Map<String, serde_json::Value>,
    keys: Vec<CelKey>,
    pub members: Arc<AtomicUsize>,
    pub key_calls: Arc<AtomicUsize>,
}

impl JsonLazy {
    pub fn new(fields: serde_json::Map<String, serde_json::Value>) -> JsonLazy {
        let keys = fields.keys().map(|k| CelKey::new(k)).collect();
        JsonLazy {
            fields,
            keys,
            members: Arc::new(AtomicUsize::new(0)),
            key_calls: Arc::new(AtomicUsize::new(0)),
        }
    }
}

impl LazyValue for JsonLazy {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.members.fetch_add(1, Ordering::SeqCst);
        match self.fields.get(name) {
            Some(serde_json::Value::Number(n)) => Ok(CelValue::Num(n.as_f64().expect("finite"))),
            Some(serde_json::Value::String(s)) => Ok(CelValue::Str(s.clone())),
            Some(serde_json::Value::Bool(b)) => Ok(CelValue::Bool(*b)),
            Some(other) => panic!("JsonLazy serves scalars only, not {other}"),
            None => Err(CelError::NoSuchMember {
                key: name.to_string(),
            }),
        }
    }

    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        self.key_calls.fetch_add(1, Ordering::SeqCst);
        Some(Box::new(self.keys.iter()))
    }
}

// ---- host functions ----

/// A roster with host functions registered: `twice(double) -> double`, `tag(string) -> string`
/// (which FAILS on `"b"`, so a host error reaches the absorption paths), and the member
/// `string.rev() -> string`.
#[allow(dead_code)]
pub fn host_roster() -> CelEnvironment {
    fn fail(what: &str) -> CelError {
        CelError::Evaluation {
            source: Arc::from("host"),
            message: format!("{what} refused its argument"),
        }
    }
    let mut e = CelEnvironment::new();
    e.declare("n", CelTy::Num);
    e.declare("s", CelTy::Str);
    e.declare("ss", CelTy::list(CelTy::Str));
    e.declare(
        "r",
        super::record_opt("r", &[("a", CelTy::Num), ("o", CelTy::Num)], &["o"]),
    );
    e.register_host(
        "twice",
        &[CelTy::Num],
        CelTy::Num,
        false,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::Num(n)] => Ok(CelValue::Num(n * 2.0)),
            _ => Err(fail("twice")),
        }),
    )
    .expect("registers");
    e.register_host(
        "tag",
        &[CelTy::Str],
        CelTy::Str,
        false,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::Str(s)] if s != "b" => Ok(CelValue::Str(format!("#{s}"))),
            _ => Err(fail("tag")),
        }),
    )
    .expect("registers");
    e.register_host(
        "rev",
        &[CelTy::Str],
        CelTy::Str,
        true,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::Str(s)] => Ok(CelValue::Str(s.chars().rev().collect())),
            _ => Err(fail("rev")),
        }),
    )
    .expect("registers");
    e
}

/// One binding per root of `host_roster()`.
#[allow(dead_code)]
pub fn host_typed_json(g: &mut Gen) -> Vec<(&'static str, serde_json::Value)> {
    use serde_json::{json, Value as J};
    let strs = ["", "a", "ab", "b"];
    let nums = [json!(0), json!(1), json!(-2.5)];
    let n = nums[g.below(nums.len())].clone();
    let s = J::from(strs[g.below(strs.len())]);
    let ss = J::Array(
        (0..g.below(4))
            .map(|_| J::from(strs[g.below(strs.len())]))
            .collect(),
    );
    let mut r = serde_json::Map::new();
    r.insert("a".into(), nums[g.below(nums.len())].clone());
    if g.below(2) == 0 {
        r.insert("o".into(), nums[g.below(nums.len())].clone());
    }
    vec![("n", n), ("s", s), ("ss", ss), ("r", J::Object(r))]
}

#[allow(dead_code)]
impl Gen {
    /// A checker-valid `bool` expression over `host_roster()`, with host calls wherever a value
    /// may be.
    pub fn host_bool(&mut self, depth: u32) -> String {
        self.hbool(depth, &mut Vec::new())
    }

    fn hbool(&mut self, depth: u32, scope: &mut Vec<&'static str>) -> String {
        if depth == 0 {
            return self.pick(&["true", "false", "has(r.o)"]).to_string();
        }
        let d = depth - 1;
        match self.below(10) {
            0 | 1 => {
                let op = self.pick(&["==", "!=", "<", ">="]);
                format!("({} {op} {})", self.hnum(d), self.hnum(d))
            }
            2 | 3 => {
                let op = self.pick(&["==", "!="]);
                format!("({} {op} {})", self.hstr(d, scope), self.hstr(d, scope))
            }
            4 => {
                let m = self.pick(&["startsWith", "endsWith"]);
                format!("{}.{m}({})", self.hstr(d, scope), self.hstr(d, scope))
            }
            5 => format!("({} && {})", self.hbool(d, scope), self.hbool(d, scope)),
            6 => format!("({} || {})", self.hbool(d, scope), self.hbool(d, scope)),
            7 => format!(
                "({} ? {} : {})",
                self.hbool(d, scope),
                self.hbool(d, scope),
                self.hbool(d, scope)
            ),
            8 if scope.is_empty() => {
                let q = self.pick(&["all", "exists"]);
                scope.push("v");
                let body = self.hbool(d, scope);
                scope.pop();
                format!("ss.{q}(v, {body})")
            }
            _ => format!("(!{})", self.hbool(d, scope)),
        }
    }

    fn hnum(&mut self, depth: u32) -> String {
        if depth == 0 || self.below(3) == 0 {
            return self.pick(&["n", "r.a", "r.o", "1.0", "0.0"]).to_string();
        }
        match self.below(3) {
            0 => format!("twice({})", self.hnum(depth - 1)),
            1 => format!("({} + {})", self.hnum(depth - 1), self.hnum(depth - 1)),
            _ => format!("twice(twice({}))", self.hnum(depth - 1)),
        }
    }

    fn hstr(&mut self, depth: u32, scope: &mut Vec<&'static str>) -> String {
        if depth == 0 || self.below(3) == 0 {
            if !scope.is_empty() && self.below(2) == 0 {
                return scope[self.below(scope.len())].to_string();
            }
            return self.pick(&["s", "'a'", "'b'", "''", "ss[0]"]).to_string();
        }
        match self.below(3) {
            0 => format!("tag({})", self.hstr(depth - 1, scope)),
            1 => format!("{}.rev()", self.hstr(depth - 1, scope)),
            _ => format!(
                "({} + {})",
                self.hstr(depth - 1, scope),
                self.hstr(depth - 1, scope)
            ),
        }
    }
}
