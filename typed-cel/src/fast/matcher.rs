//! String set matchers, built once per program from literals.
//!
//! `x == "a" || x == "b" || x.startsWith("c/")` — and `L.exists(r, x == r || x.startsWith(r +
//! "/"))` over a known `L`, and `x in [literal strings]` — ask ONE question of `x`: is it one of a
//! set of strings, or does it begin with one of a set of prefixes? A matcher answers it without
//! evaluating the chain: equality by a scan or a binary search, prefixes by a scan or by one probe
//! of the greatest prefix not above `x`, whichever is cheaper for the set's size.
//!
//! Every member carries its length and its first 16 bytes as one integer (its [`head`]), so a
//! comparison is an integer compare, and only a member longer than 16 bytes that matches that far
//! reads the rest. Through `memcmp`/`bcmp` (a PLT call per candidate) the matchers were a third to
//! two thirds of a specialized decision: `fs_open_13` 372 -> 242 cycles, `prefix_1000` 680 -> 358
//! (`ablation --cycles`).

/// Above this many keys a sorted set is searched; at or below it, scanned. A scan of a handful of
/// short keys beats a binary search's unpredictable branches.
pub(crate) const LINEAR_MAX: usize = 16;

/// The bytes a [`Key`]'s head holds.
const HEAD: usize = 16;

/// A string's first [`HEAD`] bytes, zero-padded, big-endian: two strings' heads order as the
/// strings do wherever they differ (a zero pad sorts before every byte a longer string has there,
/// as the shorter string does), so a head decides an order or an equality without the bytes behind
/// it, and only a tie — a shared first `HEAD` bytes, or a NUL where the other string ended — reads
/// the rest.
#[inline(always)]
fn head(s: &[u8]) -> u128 {
    // Built in registers from big-endian loads, each shifted to where its bytes belong; where two
    // loads overlap they carry the same bytes, so OR-ing them is exact.
    let n = s.len();
    let be8 = |at: usize| u64::from_be_bytes(s[at..at + 8].try_into().expect("8 bytes"));
    let be4 = |at: usize| u32::from_be_bytes(s[at..at + 4].try_into().expect("4 bytes")) as u64;
    let (hi, lo) = if n >= HEAD {
        (be8(0), be8(8))
    } else if n > 8 {
        (be8(0), be8(n - 8) << (8 * (HEAD - n)))
    } else if n == 8 {
        (be8(0), 0)
    } else if n >= 4 {
        ((be4(0) << 32) | (be4(n - 4) << (64 - 8 * n)), 0)
    } else if n > 0 {
        let byte = |i: usize| (s[i] as u64) << (56 - 8 * i);
        (byte(0) | byte(n / 2) | byte(n - 1), 0)
    } else {
        (0, 0)
    };
    ((hi as u128) << 64) | lo as u128
}

/// A set member, with what answers most comparisons precomputed: its length, its [`head`], and
/// the mask that keeps a head's first `len` bytes (a prefix test).
#[derive(Debug)]
pub(crate) struct Key {
    s: Box<str>,
    len: usize,
    head: u128,
    mask: u128,
}

impl Key {
    fn new(s: Box<str>) -> Key {
        let len = s.len();
        let mask = match len {
            0 => 0,
            n if n >= HEAD => u128::MAX,
            n => u128::MAX << (8 * (HEAD - n)),
        };
        Key {
            head: head(s.as_bytes()),
            len,
            mask,
            s,
        }
    }

    /// `x == self`, given `x`'s head.
    #[inline(always)]
    fn is(&self, x: &[u8], xh: u128) -> bool {
        self.len == x.len() && self.head == xh && (self.len <= HEAD || tail_is(x, &self.s))
    }

    /// `x.starts_with(self)`, given `x`'s head.
    #[inline(always)]
    fn prefixes(&self, x: &[u8], xh: u128) -> bool {
        self.len <= x.len()
            && xh & self.mask == self.head
            && (self.len <= HEAD || tail_is(x, &self.s))
    }

    /// How `self` orders against `x`, given `x`'s head.
    #[inline(always)]
    fn cmp(&self, x: &[u8], xh: u128) -> std::cmp::Ordering {
        self.head.cmp(&xh).then_with(|| self.s.as_bytes().cmp(x))
    }
}

/// `x` begins with all of `k` — past the head both already share: out of line and cold, so a
/// scan's hot loop, which rejects nearly every key by its length or its head, keeps no registers
/// for it.
#[cold]
#[inline(never)]
fn tail_is(x: &[u8], k: &str) -> bool {
    x.starts_with(k.as_bytes())
}

/// Equality against a set of strings.
#[derive(Debug)]
pub(crate) enum KeySet {
    Linear(Vec<Key>),
    Sorted(Vec<Key>),
}

impl KeySet {
    pub(crate) fn new(mut keys: Vec<Box<str>>) -> KeySet {
        keys.sort();
        keys.dedup();
        let keys: Vec<Key> = keys.into_iter().map(Key::new).collect();
        if keys.len() <= LINEAR_MAX {
            KeySet::Linear(keys)
        } else {
            KeySet::Sorted(keys)
        }
    }

    #[cfg(test)]
    fn contains(&self, s: &str) -> bool {
        self.contains_at(s.as_bytes(), head(s.as_bytes()))
    }

    /// [`contains`](KeySet::contains), `x`'s head given.
    #[inline(always)]
    fn contains_at(&self, x: &[u8], xh: u128) -> bool {
        match self {
            KeySet::Linear(keys) => keys.iter().any(|k| k.is(x, xh)),
            KeySet::Sorted(keys) => keys.binary_search_by(|k| k.cmp(x, xh)).is_ok(),
        }
    }
}

/// "Begins with one of these prefixes."
///
/// Held PREFIX-FREE: a prefix that another kept prefix begins is dropped, since the shorter one
/// already answers for it. That is what makes the sorted probe exact — if some kept `p` is a prefix
/// of `x`, then `p <= x`, and any kept `q` with `p < q <= x` would itself have `p` as a prefix
/// (a string between `p` and an extension of `p` extends `p`), which a prefix-free set excludes.
/// So the greatest kept prefix not above `x` is the only candidate.
#[derive(Debug)]
pub(crate) enum PrefixSet {
    Linear(Vec<Key>),
    Sorted(Vec<Key>),
}

impl PrefixSet {
    pub(crate) fn new(mut prefixes: Vec<Box<str>>) -> PrefixSet {
        prefixes.sort();
        prefixes.dedup();
        let mut kept: Vec<Box<str>> = Vec::with_capacity(prefixes.len());
        for p in prefixes {
            // Sorted order puts every extension of a kept prefix right after it, so checking the
            // last one kept is enough.
            if kept.last().is_some_and(|k| p.starts_with(&**k)) {
                continue;
            }
            kept.push(p);
        }
        let kept: Vec<Key> = kept.into_iter().map(Key::new).collect();
        if kept.len() <= LINEAR_MAX {
            PrefixSet::Linear(kept)
        } else {
            PrefixSet::Sorted(kept)
        }
    }

    #[cfg(test)]
    fn any_prefix_of(&self, s: &str) -> bool {
        self.any_prefix_at(s.as_bytes(), head(s.as_bytes()))
    }

    /// [`any_prefix_of`](PrefixSet::any_prefix_of), `x`'s head given.
    #[inline(always)]
    fn any_prefix_at(&self, x: &[u8], xh: u128) -> bool {
        match self {
            PrefixSet::Linear(ps) => ps.iter().any(|p| p.prefixes(x, xh)),
            PrefixSet::Sorted(ps) => {
                let at = ps.partition_point(|p| p.cmp(x, xh) != std::cmp::Ordering::Greater);
                at > 0 && ps[at - 1].prefixes(x, xh)
            }
        }
    }
}

/// `x` equals one of `eq`, or begins with one of `prefix`.
#[derive(Debug)]
pub(crate) struct StrMatcher {
    pub(crate) eq: KeySet,
    pub(crate) prefix: PrefixSet,
}

impl StrMatcher {
    pub(crate) fn new(eq: Vec<Box<str>>, prefix: Vec<Box<str>>) -> StrMatcher {
        StrMatcher {
            eq: KeySet::new(eq),
            prefix: PrefixSet::new(prefix),
        }
    }

    /// One call per test: `s`'s head built once, both halves scanned inline.
    #[inline(never)]
    pub(crate) fn matches(&self, s: &str) -> bool {
        let (x, xh) = (s.as_bytes(), head(s.as_bytes()));
        self.eq.contains_at(x, xh) || self.prefix.any_prefix_at(x, xh)
    }

    /// Whether this matcher searches a sorted set, for either half — for the tests that must cover
    /// both shapes.
    pub(crate) fn is_sorted(&self) -> bool {
        matches!(self.eq, KeySet::Sorted(_)) || matches!(self.prefix, PrefixSet::Sorted(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn boxed(xs: &[&str]) -> Vec<Box<str>> {
        xs.iter().map(|s| Box::from(*s)).collect()
    }

    /// `head` is the string's first 16 bytes, zero-padded, big-endian, at every length 0-24.
    #[test]
    fn head_is_the_first_bytes_padded() {
        let base: Vec<u8> = (1..=24u8).collect();
        for n in 0..=24 {
            let mut b = [0u8; HEAD];
            let k = n.min(HEAD);
            b[..k].copy_from_slice(&base[..k]);
            assert_eq!(head(&base[..n]), u128::from_be_bytes(b), "length {n}");
        }
    }

    /// Every set shape answers as the naive scan does, for keys and inputs across the head width
    /// (0-40 bytes), sharing long prefixes, differing only past byte 16, carrying NUL bytes (a head
    /// pads with zeros) and multi-byte characters, both below and above `LINEAR_MAX`.
    #[test]
    fn every_set_answers_as_a_scan() {
        // `""` and `"/"` prefix every path, so a set holding one is that one prefix: they come
        // last, and only the whole list holds them.
        let words = [
            "/a",
            "/ws",
            "/ws/",
            "/ws/a/b.txt",
            "/wsx",
            "/w/d0000/",
            "/w/d0000/sub1/",
            "/w/d0000/sub12/",
            "/home/user/projects/a",
            "/home/user/projects/b",
            "/home/user/projects/a/deeper/still/x",
            "a\0",
            "a",
            "a\0b",
            "\0",
            "é/ü",
            "é/",
            "GET",
            "HEAD",
            "OPTIONS",
            "0123456789abcdef",
            "0123456789abcdef0",
            "0123456789abcdeg",
            "0123456789abcde",
            "/",
            "",
        ];
        let inputs: Vec<String> = words
            .iter()
            .map(|w| w.to_string())
            .chain(words.iter().map(|w| format!("{w}x")))
            .chain(words.iter().map(|w| format!("{w}/q")))
            // Each word less its last character.
            .chain(words.iter().map(|w| {
                let mut c = w.chars();
                c.next_back();
                c.as_str().to_string()
            }))
            // Each word with its last character changed: the same length and, past `HEAD`, the
            // same head as a member it is not.
            .chain(words.iter().filter(|w| !w.is_empty()).map(|w| {
                let mut c = w.chars();
                c.next_back();
                format!("{}~", c.as_str())
            }))
            .collect();
        // Up to 16 keys the set is scanned (11 and 16 hold the long words), past it searched.
        for take in [1, 3, 8, 11, 16, words.len()] {
            for pad in [0, LINEAR_MAX + 4] {
                let mut set: Vec<Box<str>> =
                    words.iter().take(take).map(|w| Box::from(*w)).collect();
                for i in 0..pad {
                    set.push(format!("~zz{i:03}/").into());
                }
                let keys = KeySet::new(set.clone());
                let prefixes = PrefixSet::new(set.clone());
                for x in &inputs {
                    assert_eq!(
                        keys.contains(x),
                        set.iter().any(|k| &**k == x.as_str()),
                        "{set:?} contains {x:?}"
                    );
                    assert_eq!(
                        prefixes.any_prefix_of(x),
                        set.iter().any(|p| x.starts_with(&**p)),
                        "{set:?} has a prefix of {x:?}"
                    );
                }
            }
        }
    }

    /// The sorted probe agrees with a scan over every set, including nested prefixes and a byte
    /// below `/` between a prefix and its extension.
    #[test]
    fn the_sorted_probe_is_a_scan() {
        let sets: &[&[&str]] = &[
            &["/a/", "/a/b/", "/a-", "/a.", "/"],
            &["/ws/", "/wsx/", "/ws-a/", "/w/"],
            &["", "/x/"],
        ];
        let paths = [
            "/a/x", "/a-b", "/a.c", "/b", "/ws/x", "/wsx", "/ws-a/q", "/w/", "", "x",
        ];
        for set in sets {
            // Pad past LINEAR_MAX with prefixes nothing here starts with.
            let mut all = boxed(set);
            for i in 0..(LINEAR_MAX + 4) {
                all.push(format!("~zz{i:03}/").into());
            }
            let sorted = PrefixSet::new(all.clone());
            // `""` is a prefix of everything, so it reduces a set to itself.
            assert_eq!(
                matches!(sorted, PrefixSet::Sorted(_)),
                !set.contains(&""),
                "{set:?}"
            );
            for p in paths {
                let scan = all.iter().any(|q| p.starts_with(&**q));
                assert_eq!(sorted.any_prefix_of(p), scan, "{set:?} ∋? prefix of {p:?}");
            }
        }
    }
}

/// A set of numbers, as `==` sees them: `-0.0` is `0.0`, and NaN — equal to nothing — is never a
/// member. Sorted bit patterns, answered by binary search.
#[derive(Debug)]
pub(crate) struct NumSet {
    bits: Box<[u64]>,
}

impl NumSet {
    pub(crate) fn new(nums: impl IntoIterator<Item = f64>) -> NumSet {
        let mut bits: Vec<u64> = nums
            .into_iter()
            .filter(|n| !n.is_nan())
            .map(canonical)
            .collect();
        bits.sort_unstable();
        bits.dedup();
        NumSet {
            bits: bits.into_boxed_slice(),
        }
    }

    pub(crate) fn contains(&self, n: f64) -> bool {
        !n.is_nan() && self.bits.binary_search(&canonical(n)).is_ok()
    }
}

/// `n`'s bits, with the two zeros made one.
fn canonical(n: f64) -> u64 {
    if n == 0.0 {
        0.0f64.to_bits()
    } else {
        n.to_bits()
    }
}
