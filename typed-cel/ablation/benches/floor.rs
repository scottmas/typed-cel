//! The floor: what a minimal interpreter over the SAME `Facts` costs on `nested_fields`.
use typed_cel::{Facts, FieldId};

#[derive(Clone, Copy)]
pub enum V<'a> {
    Unset,
    Bool(bool),
    Str(&'a str),
    Err(u16),
}

#[derive(Clone, Copy)]
pub enum Op {
    Read { dst: u8, f: u16, err: u16 },
    Eq { dst: u8, a: u8, b: u8 },
    BrFalse { r: u8, to: u16 },
    EqK { dst: u8, a: u8, k: u16 },
    Absorb { dst: u8, a: u8, err: u16 },
    Catch { dst: u8 },
    Jump { to: u16 },
    Ret { r: u8 },
    RetK { k: u16 },
    Fail,
}

/// The error a spike run ended on; only its presence is compared.
#[allow(dead_code)]
pub struct Miss(pub u16);

/// The same 13 ops `nested_fields` lowers to, op for op.
#[inline(never)]
pub fn run<F: Facts + ?Sized>(ops: &[Op], k: &[V<'static>], facts: &F) -> Result<bool, Miss> {
    let mut regs = [V::Unset; 8];
    let (mut pc, mut inflight) = (0usize, 0u16);
    loop {
        let op = ops[pc];
        pc += 1;
        match op {
            Op::Read { dst, f, err } => match facts.str(FieldId::from_index(f as usize)) {
                Some(s) => regs[dst as usize] = V::Str(s),
                None => {
                    inflight = f + 1;
                    pc = err as usize
                }
            },
            Op::Eq { dst, a, b } => {
                regs[dst as usize] = V::Bool(match (regs[a as usize], regs[b as usize]) {
                    (V::Str(x), V::Str(y)) => x == y,
                    (V::Bool(x), V::Bool(y)) => x == y,
                    _ => false,
                })
            }
            Op::BrFalse { r, to } => {
                if matches!(regs[r as usize], V::Bool(false)) {
                    pc = to as usize
                }
            }
            Op::EqK { dst, a, k: kk } => {
                regs[dst as usize] = V::Bool(match (regs[a as usize], k[kk as usize]) {
                    (V::Str(x), V::Str(y)) => x == y,
                    _ => false,
                })
            }
            Op::Absorb { dst, a, err } => match (regs[a as usize], regs[dst as usize]) {
                (V::Bool(_), _) | (V::Err(_), V::Bool(false)) => {}
                (V::Err(e), _) => {
                    inflight = e;
                    pc = err as usize
                }
                _ => {
                    inflight = u16::MAX;
                    pc = err as usize
                }
            },
            Op::Catch { dst } => regs[dst as usize] = V::Err(inflight),
            Op::Jump { to } => pc = to as usize,
            Op::Ret { r } => {
                return match regs[r as usize] {
                    V::Bool(b) => Ok(b),
                    _ => Err(Miss(u16::MAX)),
                }
            }
            Op::RetK { k: kk } => {
                return match k[kk as usize] {
                    V::Bool(b) => Ok(b),
                    _ => Err(Miss(u16::MAX)),
                }
            }
            Op::Fail => return Err(Miss(inflight)),
        }
    }
}

pub fn nested() -> (Vec<Op>, Vec<V<'static>>) {
    use Op::*;
    (
        vec![
            Read {
                dst: 2,
                f: 0,
                err: 11,
            },
            Read {
                dst: 3,
                f: 1,
                err: 11,
            },
            Eq { dst: 1, a: 2, b: 3 },
            BrFalse { r: 1, to: 9 },
            Read {
                dst: 2,
                f: 2,
                err: 8,
            },
            EqK { dst: 0, a: 2, k: 0 },
            Absorb {
                dst: 0,
                a: 1,
                err: 8,
            },
            Ret { r: 0 },
            Fail,
            RetK { k: 1 },
            Ret { r: 0 },
            Catch { dst: 1 },
            Jump { to: 4 },
        ],
        vec![V::Str("gold"), V::Bool(false)],
    )
}

/// Superinstructions: read-read-compare-branch, read-const-compare-branch.
#[derive(Clone, Copy)]
pub enum FOp {
    CondEqFF {
        a: u16,
        b: u16,
        else_: u16,
        err: u16,
    },
    CondEqFK {
        a: u16,
        k: u16,
        else_: u16,
        err: u16,
    },
    RetK(bool),
    Fail,
}

#[inline(never)]
pub fn run_fused<F: Facts + ?Sized>(
    ops: &[FOp],
    k: &[&'static str],
    facts: &F,
) -> Result<bool, Miss> {
    let mut pc = 0usize;
    loop {
        let op = ops[pc];
        pc += 1;
        match op {
            FOp::CondEqFF { a, b, else_, err } => match (
                facts.str(FieldId::from_index(a as usize)),
                facts.str(FieldId::from_index(b as usize)),
            ) {
                (Some(x), Some(y)) => {
                    if x != y {
                        pc = else_ as usize
                    }
                }
                _ => pc = err as usize,
            },
            FOp::CondEqFK {
                a,
                k: kk,
                else_,
                err,
            } => match facts.str(FieldId::from_index(a as usize)) {
                Some(x) => {
                    if x != k[kk as usize] {
                        pc = else_ as usize
                    }
                }
                None => pc = err as usize,
            },
            FOp::RetK(b) => return Ok(b),
            FOp::Fail => return Err(Miss(0)),
        }
    }
}

pub fn nested_fused() -> (Vec<FOp>, Vec<&'static str>) {
    use FOp::*;
    (
        vec![
            CondEqFF {
                a: 0,
                b: 1,
                else_: 3,
                err: 4,
            },
            CondEqFK {
                a: 2,
                k: 0,
                else_: 3,
                err: 4,
            },
            RetK(true),
            RetK(false),
            Fail,
        ],
        vec!["gold"],
    )
}

/// A tree of boxed closures over `&dyn Facts`, CEL `&&` absorption included.
pub mod closures {
    use typed_cel::{Facts, FieldId};
    pub type B = Box<dyn Fn(&dyn Facts) -> Result<bool, u16>>;
    pub type S = Box<dyn for<'a> Fn(&'a dyn Facts) -> Result<&'a str, u16>>;
    pub fn read(f: usize) -> S {
        Box::new(move |x| x.str(FieldId::from_index(f)).ok_or(f as u16))
    }
    pub fn konst(k: &'static str) -> S {
        Box::new(move |_| Ok(k))
    }
    pub fn eq(a: S, b: S) -> B {
        Box::new(move |x| Ok(a(x)? == b(x)?))
    }
    pub fn and(a: B, b: B) -> B {
        Box::new(move |x| match a(x) {
            Ok(false) => Ok(false),
            Ok(true) => b(x),
            Err(e) => match b(x) {
                Ok(false) => Ok(false),
                _ => Err(e),
            },
        })
    }
    pub fn nested() -> B {
        and(eq(read(0), read(1)), eq(read(2), konst("gold")))
    }
}
