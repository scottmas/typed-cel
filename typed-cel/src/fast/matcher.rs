//! String set matchers, built once per program from literals.
//!
//! `x == "a" || x == "b" || x.startsWith("c/")` — and `L.exists(r, x == r || x.startsWith(r +
//! "/"))` over a known `L`, and `x in [literal strings]` — ask ONE question of `x`: is it one of a
//! set of strings, or does it begin with one of a set of prefixes? A matcher answers it without
//! evaluating the chain: equality by a scan or a binary search, prefixes by a scan or by one probe
//! of the greatest prefix not above `x`, whichever is cheaper for the set's size.

/// Above this many keys a sorted set is searched; at or below it, scanned. A scan of a handful of
/// short keys beats a binary search's unpredictable branches.
pub(crate) const LINEAR_MAX: usize = 16;

/// Equality against a set of strings.
#[derive(Debug)]
pub(crate) enum KeySet {
    Linear(Vec<Box<str>>),
    Sorted(Vec<Box<str>>),
}

impl KeySet {
    pub(crate) fn new(mut keys: Vec<Box<str>>) -> KeySet {
        keys.sort();
        keys.dedup();
        if keys.len() <= LINEAR_MAX {
            KeySet::Linear(keys)
        } else {
            KeySet::Sorted(keys)
        }
    }

    pub(crate) fn contains(&self, s: &str) -> bool {
        match self {
            KeySet::Linear(keys) => keys.iter().any(|k| &**k == s),
            KeySet::Sorted(keys) => keys.binary_search_by(|k| (**k).cmp(s)).is_ok(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        match self {
            KeySet::Linear(k) | KeySet::Sorted(k) => k.is_empty(),
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
    Linear(Vec<Box<str>>),
    Sorted(Vec<Box<str>>),
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
        if kept.len() <= LINEAR_MAX {
            PrefixSet::Linear(kept)
        } else {
            PrefixSet::Sorted(kept)
        }
    }

    pub(crate) fn any_prefix_of(&self, s: &str) -> bool {
        match self {
            PrefixSet::Linear(ps) => ps.iter().any(|p| s.starts_with(&**p)),
            PrefixSet::Sorted(ps) => {
                let at = ps.partition_point(|p| &**p <= s);
                at > 0 && s.starts_with(&*ps[at - 1])
            }
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        match self {
            PrefixSet::Linear(k) | PrefixSet::Sorted(k) => k.is_empty(),
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

    #[inline]
    pub(crate) fn matches(&self, s: &str) -> bool {
        (!self.eq.is_empty() && self.eq.contains(s))
            || (!self.prefix.is_empty() && self.prefix.any_prefix_of(s))
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
