//! The dialect's one number, at run time. The checker has a single numeric type (`CelTy::Num`); a
//! VALUE of it is held exactly in one of three representations — an `i64`, a `u64` or an `f64` —
//! so an integer a document carries is never rounded on its way to a comparison.
//!
//! The representation is an engine detail, never a type: `Int(3)` and `Float(3.0)` are the same
//! number, compare equal, find the same set members and the same map key. The engine builds the
//! CANONICAL form (`from_f64`, `from_i128`) so that display, goldens and interning are
//! deterministic, but nothing here assumes a value it is handed is canonical.

use std::cmp::Ordering;
use std::fmt;

/// A number value: an `i64`, a `u64`, or an `f64`.
#[derive(Clone, Copy, Debug)]
pub enum CelNum {
    Int(i64),
    /// Only above `i64::MAX` when canonical; any `u64` is accepted and compared correctly.
    UInt(u64),
    Float(f64),
}

/// Integer text outside `[i64::MIN, u64::MAX]`, or text that is not a number: refused rather than
/// rounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Inexact;

/// `2^63` and `2^64`, both exact in `f64`. The bounds are these — never `i64::MAX as f64`, which
/// rounds UP to `2^63` and would let `2^63` into `Int`, where `as i64` saturates.
const TWO_63: f64 = 9_223_372_036_854_775_808.0;
const TWO_64: f64 = 18_446_744_073_709_551_616.0;

impl CelNum {
    /// The canonical form of a double: an integral, finite, NONZERO value inside
    /// `[i64::MIN, u64::MAX]` is an integer (`Int` if it fits, else `UInt`); anything else stays a
    /// `Float` — NaN, ±inf, fractions, out-of-range, and both zeros. A float zero keeps its sign
    /// through negation and division (`-(0.0)` is `-0.0`, `1 / -(0.0)` is `-inf`, as IEEE says),
    /// which an integer zero has no way to carry.
    pub fn from_f64(f: f64) -> CelNum {
        if f.fract() == 0.0 && f != 0.0 {
            if (-TWO_63..TWO_63).contains(&f) {
                return CelNum::Int(f as i64);
            }
            if (TWO_63..TWO_64).contains(&f) {
                return CelNum::UInt(f as u64);
            }
        }
        CelNum::Float(f)
    }

    /// The canonical form of an exact integer, or `None` outside `[i64::MIN, u64::MAX]`.
    pub fn from_i128(v: i128) -> Option<CelNum> {
        if let Ok(i) = i64::try_from(v) {
            return Some(CelNum::Int(i));
        }
        u64::try_from(v).ok().map(CelNum::UInt)
    }

    /// JSON number TEXT, read exactly: integer syntax
    /// outside `[i64::MIN, u64::MAX]` is `Inexact` instead of a rounded double. `-0` is `-0.0`;
    /// a fraction or an exponent goes through `f64` and is canonicalized (`1e3` is `Int(1000)`).
    pub fn parse_json(t: &str) -> Result<CelNum, Inexact> {
        let digits = t.strip_prefix('-').unwrap_or(t);
        if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
            if digits.bytes().all(|b| b == b'0') && t.starts_with('-') {
                return Ok(CelNum::Float(-0.0));
            }
            // `i128` holds 38 digits; longer integer text fails to parse, which is `Inexact`.
            return t
                .parse::<i128>()
                .ok()
                .and_then(CelNum::from_i128)
                .ok_or(Inexact);
        }
        t.parse::<f64>().map(CelNum::from_f64).map_err(|_| Inexact)
    }

    /// The nearest double. Rounds an integer above `2^53`; for arithmetic with a `Float` operand
    /// (where IEEE semantics are the rule), never for comparison.
    pub fn as_f64(self) -> f64 {
        match self {
            CelNum::Int(i) => i as f64,
            CelNum::UInt(u) => u as f64,
            CelNum::Float(f) => f,
        }
    }

    fn as_i128(self) -> Option<i128> {
        match self {
            CelNum::Int(i) => Some(i.into()),
            CelNum::UInt(u) => Some(u.into()),
            CelNum::Float(_) => None,
        }
    }

    /// The same value in canonical form.
    pub fn canonical(self) -> CelNum {
        match self {
            CelNum::Float(f) => CelNum::from_f64(f),
            n => n
                .as_i128()
                .and_then(CelNum::from_i128)
                .expect("an integer representation fits the integer range"),
        }
    }

    /// Exact order by mathematical value. `None` iff a NaN is involved. Never assumes canonical
    /// form.
    #[inline]
    pub fn cmp_exact(self, o: CelNum) -> Option<Ordering> {
        // The common mixed pair — a JSON integer against a fractional bound — needs no `i128`: an
        // `i64` within 2^53 converts to `f64` exactly, so the double compare IS the exact one.
        match (self, o) {
            (CelNum::Int(i), CelNum::Float(f)) => return cmp_i64_f64(i, f),
            (CelNum::Float(f), CelNum::Int(i)) => return cmp_i64_f64(i, f).map(Ordering::reverse),
            _ => {}
        }
        match (self.as_i128(), o.as_i128()) {
            (Some(a), Some(b)) => Some(a.cmp(&b)),
            (Some(a), None) => cmp_int_float(a, o.as_f64()),
            (None, Some(b)) => cmp_int_float(b, self.as_f64()).map(Ordering::reverse),
            (None, None) => self.as_f64().partial_cmp(&o.as_f64()),
        }
    }

    /// Exact equality by mathematical value; NaN equals nothing, `-0.0` equals `0`.
    pub fn eq_exact(self, o: CelNum) -> bool {
        self.cmp_exact(o) == Some(Ordering::Equal)
    }

    /// One key per mathematical value (set membership, interning of equal constants). `None` for
    /// NaN, which is a member of nothing.
    pub fn key_bits(self) -> Option<(u8, u64)> {
        match self.canonical() {
            CelNum::Int(i) => Some((0, i as u64)),
            CelNum::UInt(u) => Some((1, u)),
            CelNum::Float(f) if f.is_nan() => None,
            // `-0.0` is the key of `Int(0)`.
            CelNum::Float(f) if f == 0.0 => Some((0, 0)),
            CelNum::Float(f) => Some((2, f.to_bits())),
        }
    }

    /// The value as a map key or list index: an integral value in `i64` range. `-0.0` is `0`; a
    /// `UInt` is no key (numeric map keys are `i64`).
    pub fn integral_key(self) -> Option<i64> {
        match self.canonical() {
            CelNum::Int(i) => Some(i),
            CelNum::Float(f) if f == 0.0 => Some(0),
            _ => None,
        }
    }
}

/// By exact mathematical value: `Int(3) == Float(3.0)`, NaN equal to nothing — the dialect's `==`.
impl PartialEq for CelNum {
    fn eq(&self, o: &CelNum) -> bool {
        self.eq_exact(*o)
    }
}

/// By exact mathematical value, `None` for a NaN — the dialect's `<`.
impl PartialOrd for CelNum {
    fn partial_cmp(&self, o: &CelNum) -> Option<Ordering> {
        self.cmp_exact(*o)
    }
}

impl fmt::Display for CelNum {
    /// An integer prints without a fraction; a double prints as Rust's shortest round-trip form.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CelNum::Int(i) => write!(f, "{i}"),
            CelNum::UInt(u) => write!(f, "{u}"),
            CelNum::Float(x) => write!(f, "{x}"),
        }
    }
}

impl From<i64> for CelNum {
    fn from(i: i64) -> Self {
        CelNum::Int(i)
    }
}

impl From<u64> for CelNum {
    /// Canonical: a `u64` inside `i64` range is an `Int`.
    fn from(u: u64) -> Self {
        CelNum::from_i128(u.into()).expect("every u64 fits")
    }
}

/// An `i64` against a float, exactly: through `f64` when the integer is one an `f64` holds
/// exactly (|i| <= 2^53), else through `i128`.
#[inline(always)]
pub(crate) fn cmp_i64_f64(i: i64, f: f64) -> Option<Ordering> {
    if i.unsigned_abs() <= 1 << 53 {
        (i as f64).partial_cmp(&f)
    } else {
        cmp_int_float(i.into(), f)
    }
}

/// An integer (as `i128`, covering every `i64` and `u64`) against a float, exactly. Out of line:
/// callers inline [`cmp_i64_f64`], whose common case never reaches here.
#[inline(never)]
fn cmp_int_float(i: i128, f: f64) -> Option<Ordering> {
    if f.is_nan() {
        return None;
    }
    if f >= TWO_64 {
        return Some(Ordering::Less); // above every u64
    }
    if f < -TWO_63 {
        return Some(Ordering::Greater); // below every i64
    }
    let t = f.trunc(); // integral, in [-2^63, 2^64): exact in i128
    match i.cmp(&(t as i128)) {
        Ordering::Equal if f > t => Some(Ordering::Less), // i == trunc(f) < f
        Ordering::Equal if f < t => Some(Ordering::Greater), // negative fraction: f < trunc(f) == i
        o => Some(o),
    }
}

/// The four arithmetic operators the dialect has on numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NumOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl NumOp {
    /// The operator's name in an overflow error, as a duration's overflow spells it.
    pub(crate) fn name(self) -> &'static str {
        match self {
            NumOp::Add => "add",
            NumOp::Sub => "sub",
            NumOp::Mul => "mul",
            NumOp::Div => "div",
        }
    }
}

/// Integer overflow: the exact result is outside `[i64::MIN, u64::MAX]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Overflow;

/// `a op b`. Two integers: exact, in checked `i128`, overflow refused. A `Float` on either side:
/// IEEE `f64`, canonicalized. Division of two integers is REAL division: an exact quotient is an
/// integer, an inexact one a `Float`, a zero divisor the IEEE answer (`1/0 == +inf`, `0/0` NaN).
pub(crate) fn arith(op: NumOp, a: CelNum, b: CelNum) -> Result<CelNum, Overflow> {
    match (a.as_i128(), b.as_i128()) {
        (Some(x), Some(y)) => match op {
            NumOp::Add => x.checked_add(y).and_then(CelNum::from_i128).ok_or(Overflow),
            NumOp::Sub => x.checked_sub(y).and_then(CelNum::from_i128).ok_or(Overflow),
            NumOp::Mul => x.checked_mul(y).and_then(CelNum::from_i128).ok_or(Overflow),
            NumOp::Div if y == 0 => Ok(CelNum::from_f64(a.as_f64() / b.as_f64())),
            NumOp::Div if x % y == 0 => CelNum::from_i128(x / y).ok_or(Overflow),
            NumOp::Div => Ok(CelNum::Float(a.as_f64() / b.as_f64())),
        },
        _ => {
            let (x, y) = (a.as_f64(), b.as_f64());
            Ok(CelNum::from_f64(match op {
                NumOp::Add => x + y,
                NumOp::Sub => x - y,
                NumOp::Mul => x * y,
                NumOp::Div => x / y,
            }))
        }
    }
}

/// `-a`. An integer negates exactly (`-i64::MIN` is a `UInt`; `-u64::MAX` overflows); a float
/// negates as IEEE, so `-(0.0)` is `-0.0`.
pub(crate) fn neg(a: CelNum) -> Result<CelNum, Overflow> {
    match a.as_i128() {
        None => Ok(CelNum::Float(-a.as_f64())),
        Some(i) => CelNum::from_i128(-i).ok_or(Overflow),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Ordering::{Equal, Greater, Less};

    fn same(a: CelNum, b: CelNum) -> bool {
        match (a, b) {
            (CelNum::Int(x), CelNum::Int(y)) => x == y,
            (CelNum::UInt(x), CelNum::UInt(y)) => x == y,
            (CelNum::Float(x), CelNum::Float(y)) => x.to_bits() == y.to_bits(),
            _ => false,
        }
    }

    #[track_caller]
    fn is(got: CelNum, want: CelNum) {
        assert!(same(got, want), "got {got:?}, want {want:?}");
    }

    #[test]
    fn parse_json_is_exact_for_integer_syntax() {
        let ok = |t: &str| CelNum::parse_json(t).unwrap_or_else(|_| panic!("{t}"));
        is(ok("9007199254740993"), CelNum::Int(9007199254740993));
        is(ok("18446744073709551615"), CelNum::UInt(u64::MAX));
        is(ok("-9223372036854775808"), CelNum::Int(i64::MIN));
        is(ok("-0"), CelNum::Float(-0.0));
        is(ok("0"), CelNum::Int(0));
        is(ok("0.0"), CelNum::Float(0.0));
        is(ok("1e3"), CelNum::Int(1000));
        is(ok("2.0"), CelNum::Int(2));
        is(ok("0.5"), CelNum::Float(0.5));
        is(ok("1e400"), CelNum::Float(f64::INFINITY));
        for t in [
            "18446744073709551616",
            "-9223372036854775809",
            "123456789012345678901234567890123456789012",
        ] {
            assert_eq!(CelNum::parse_json(t).map(|_| ()), Err(Inexact), "{t}");
        }
    }

    #[test]
    fn from_f64_is_canonical() {
        is(CelNum::from_f64(3.0), CelNum::Int(3));
        is(CelNum::from_f64(-0.0), CelNum::Float(-0.0));
        is(CelNum::from_f64(0.0), CelNum::Float(0.0));
        is(CelNum::from_f64(-3.0), CelNum::Int(-3));
        is(CelNum::from_f64(2f64.powi(63)), CelNum::UInt(1 << 63));
        is(CelNum::from_f64(-(2f64.powi(63))), CelNum::Int(i64::MIN));
        is(
            CelNum::from_f64(2f64.powi(64)),
            CelNum::Float(2f64.powi(64)),
        );
        is(CelNum::from_f64(0.5), CelNum::Float(0.5));
        is(
            CelNum::from_f64(f64::INFINITY),
            CelNum::Float(f64::INFINITY),
        );
        assert!(matches!(CelNum::from_f64(f64::NAN), CelNum::Float(f) if f.is_nan()));
    }

    #[test]
    fn compare_is_exact_across_representations() {
        use CelNum::{Float as F, Int as I, UInt as U};
        let two63 = 9223372036854775808.0;
        let table = [
            (I(9007199254740993), F(9007199254740992.0), Some(Greater)),
            (I(i64::MAX), F(two63), Some(Less)),
            (U(1 << 63), F(two63), Some(Equal)),
            (I(-1), U(0), Some(Less)),
            (I(0), F(-0.0), Some(Equal)),
            (I(2), F(2.5), Some(Less)),
            (I(-2), F(-2.5), Some(Greater)),
            (I(-3), F(-2.5), Some(Less)),
            (U(u64::MAX), F(2f64.powi(64)), Some(Less)),
            (I(i64::MIN), F(-two63), Some(Equal)),
            (I(i64::MIN), F(-two63 * 2.0), Some(Greater)),
            (I(1), F(f64::NAN), None),
            (F(f64::NAN), F(f64::NAN), None),
            (U(5), F(f64::NAN), None),
        ];
        for (a, b, want) in table {
            assert_eq!(a.cmp_exact(b), want, "{a:?} vs {b:?}");
            assert_eq!(
                b.cmp_exact(a),
                want.map(Ordering::reverse),
                "{b:?} vs {a:?}"
            );
        }
    }

    /// A deterministic xorshift, so a failure reproduces.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
    }

    /// Values biased toward the edges where an `f64` path and an exact path disagree.
    fn pool() -> Vec<CelNum> {
        let mut v = Vec::new();
        let ints: [i128; 16] = [
            0,
            1,
            -1,
            2,
            (1 << 53) - 1,
            1 << 53,
            (1 << 53) + 1,
            -(1 << 53) - 1,
            (1 << 63) - 1,
            1 << 63,
            (1 << 63) + 1,
            -(1 << 63),
            -(1 << 63) + 1,
            u64::MAX as i128,
            u64::MAX as i128 - 1,
            12345,
        ];
        for i in ints {
            let n = CelNum::from_i128(i).unwrap();
            v.push(n);
            if let Ok(u) = u64::try_from(i) {
                v.push(CelNum::UInt(u));
            }
            let f = i as f64;
            for g in [f, f.next_up(), f.next_down()] {
                v.push(CelNum::Float(g));
            }
        }
        for f in [
            0.0,
            -0.0,
            0.5,
            -0.5,
            1.5,
            -2.5,
            1e300,
            -1e300,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            2f64.powi(64),
            -(2f64.powi(63)),
        ] {
            v.push(CelNum::Float(f));
        }
        v
    }

    /// The ground truth, computed a different way from `cmp_exact`: an integer against a finite
    /// float by comparing the integer with `floor(f)` and then the fraction.
    fn truth(a: CelNum, b: CelNum) -> Option<Ordering> {
        fn exact(n: CelNum) -> Result<i128, f64> {
            match n {
                CelNum::Int(i) => Ok(i.into()),
                CelNum::UInt(u) => Ok(u.into()),
                CelNum::Float(f) => Err(f),
            }
        }
        fn int_vs_float(i: i128, f: f64) -> Option<Ordering> {
            if f.is_nan() {
                return None;
            }
            if f.is_infinite() {
                return Some(if f > 0.0 { Less } else { Greater });
            }
            if f.abs() >= 1e30 {
                return Some(if f > 0.0 { Less } else { Greater });
            }
            let fl = f.floor();
            let fl_i = fl as i128;
            match i.cmp(&fl_i) {
                Equal if f != fl => Some(Less),
                o => Some(o),
            }
        }
        match (exact(a), exact(b)) {
            (Ok(x), Ok(y)) => Some(x.cmp(&y)),
            (Ok(x), Err(f)) => int_vs_float(x, f),
            (Err(f), Ok(y)) => int_vs_float(y, f).map(Ordering::reverse),
            (Err(f), Err(g)) => f.partial_cmp(&g),
        }
    }

    #[test]
    fn compare_agrees_with_i128_and_f64_ground_truth() {
        let pool = pool();
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..100_000 {
            let a = pool[(rng.next() % pool.len() as u64) as usize];
            let b = pool[(rng.next() % pool.len() as u64) as usize];
            let got = a.cmp_exact(b);
            assert_eq!(got, truth(a, b), "{a:?} vs {b:?}");
            assert_eq!(a.eq_exact(b), got == Some(Equal), "{a:?} vs {b:?}");
        }
    }

    #[test]
    fn every_spelling_of_a_value_is_the_same_value() {
        for v in pool() {
            let mut spellings = vec![v, v.canonical()];
            if let Some(i) = match v {
                CelNum::Int(i) => Some(i128::from(i)),
                CelNum::UInt(u) => Some(i128::from(u)),
                CelNum::Float(f) if f.is_finite() && f.fract() == 0.0 && f.abs() < 1e30 => {
                    Some(f as i128)
                }
                _ => None,
            } {
                if let Ok(n) = i64::try_from(i) {
                    spellings.push(CelNum::Int(n));
                }
                if let Ok(n) = u64::try_from(i) {
                    spellings.push(CelNum::UInt(n));
                }
                let f = i as f64;
                if f as i128 == i {
                    spellings.push(CelNum::Float(f));
                }
            }
            for a in &spellings {
                for b in &spellings {
                    if v.cmp_exact(v).is_none() {
                        assert_eq!(a.key_bits(), None);
                        continue;
                    }
                    assert_eq!(a.cmp_exact(*b), Some(Equal), "{a:?} vs {b:?}");
                    assert_eq!(a.key_bits(), b.key_bits(), "{a:?} vs {b:?}");
                }
            }
        }
    }

    #[test]
    fn distinct_values_have_distinct_keys() {
        let pool = pool();
        for a in &pool {
            for b in &pool {
                if a.cmp_exact(*b) != Some(Equal) && a.key_bits().is_some() {
                    assert_ne!(a.key_bits(), b.key_bits(), "{a:?} vs {b:?}");
                }
            }
        }
    }

    #[test]
    fn integer_arithmetic_is_exact_and_checked() {
        use CelNum::{Float as F, Int as I, UInt as U};
        use NumOp::*;
        let ok = |op, a, b| arith(op, a, b).unwrap_or_else(|_| panic!("{op:?} {a:?} {b:?}"));
        is(ok(Add, I(9007199254740993), I(0)), I(9007199254740993));
        is(ok(Add, I(i64::MAX), I(1)), U(1 << 63));
        is(ok(Sub, U(1 << 63), I(1)), I(i64::MAX));
        assert_eq!(arith(Add, U(u64::MAX), I(1)).map(|_| ()), Err(Overflow));
        assert_eq!(arith(Sub, I(i64::MIN), I(1)).map(|_| ()), Err(Overflow));
        assert_eq!(arith(Mul, I(-3), U(1 << 63)).map(|_| ()), Err(Overflow));
        is(ok(Div, I(6), I(3)), I(2));
        is(ok(Div, I(7), I(2)), F(3.5));
        is(ok(Div, I(-7), I(2)), F(-3.5));
        is(ok(Div, I(1), I(0)), F(f64::INFINITY));
        is(ok(Div, I(-1), I(0)), F(f64::NEG_INFINITY));
        assert!(matches!(ok(Div, I(0), I(0)), F(f) if f.is_nan()));
        is(ok(Div, I(i64::MIN), I(-1)), U(1 << 63));
        is(neg(I(i64::MIN)).unwrap(), U(1 << 63));
        is(neg(U(1 << 63)).unwrap(), I(i64::MIN));
        assert_eq!(neg(U(u64::MAX)).map(|_| ()), Err(Overflow));
        is(neg(F(0.0)).unwrap(), F(-0.0));
        is(neg(I(0)).unwrap(), I(0));
    }

    #[test]
    fn float_arithmetic_is_ieee_then_canonical() {
        use CelNum::{Float as F, Int as I};
        is(arith(NumOp::Add, F(1.5), F(1.5)).unwrap(), I(3));
        is(arith(NumOp::Add, I(1), F(0.5)).unwrap(), F(1.5));
        is(
            arith(NumOp::Add, F(0.1), F(0.2)).unwrap(),
            F(0.30000000000000004),
        );
        is(
            arith(NumOp::Div, I(1), F(-0.0)).unwrap(),
            F(f64::NEG_INFINITY),
        );
    }
}
