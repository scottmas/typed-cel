//! Demand extraction: what an expression READS, as data.
//!
//! The crate's most unusual export and the one with no analogue in any other CEL implementation.
//! The inherited `Program::references()` is not it — measured, it returns ROOTS only
//! (`["files", "metrics", "uptime"]` for a three-clause expression), so it cannot drive
//! demand-based population.
//!
//! Two consumers need the answer, for different reasons:
//!
//! - **A host populates only these paths.** An expression evaluated repeatedly (on every tick of a
//!   monitor, say) has to cost work proportional to the EXPRESSION rather than to the state it
//!   ranges over. A policy naming one file leaves the state's file map at one entry no matter how
//!   many files exist.
//! - **An operator can answer "what does this policy watch?" from the artifact**, without running
//!   it.
//!
//! It is also what makes the language optional-free: every demanded path exists in the activation
//! from load, zero-valued, so there is no absence to write syntax for.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// One step of a path.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum Segment {
    /// A declared top-level variable.
    Root(String),
    /// A literal key or field name.
    Key(String),
    /// A comprehension iterating the whole container — `listeners.exists(p, listeners[p]…)`.
    Wild,
}

impl std::fmt::Display for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Segment::Root(r) => write!(f, "{r}"),
            Segment::Key(k) => write!(f, "{k:?}"),
            Segment::Wild => write!(f, "*"),
        }
    }
}

/// Every literal path an expression reads, plus the roots a comprehension iterates whole.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct DemandSet {
    paths: BTreeSet<Vec<Segment>>,
    wide_roots: BTreeSet<String>,
}

impl DemandSet {
    /// Every path, sorted and deduplicated, with no path that is a strict prefix of another.
    ///
    /// The prefix pruning is what makes `files["/a"].closed.elapsed > 5s` yield exactly one path
    /// rather than the four its spine passes through — a demand set full of prefixes reads as
    /// "this policy watches the whole `files` map", which is the opposite of the claim.
    pub fn paths(&self) -> impl Iterator<Item = &[Segment]> {
        self.paths.iter().map(Vec::as_slice)
    }

    /// Roots a comprehension iterates whole. A root here means "populate every key", bounded by
    /// the leaf fields recorded in [`DemandSet::paths`] for that root — a wide root is not a
    /// licence to materialize whole entries.
    pub fn wide_roots(&self) -> impl Iterator<Item = &str> {
        self.wide_roots.iter().map(String::as_str)
    }

    /// The declared variables this expression touches at all.
    pub fn roots(&self) -> BTreeSet<&str> {
        self.paths
            .iter()
            .filter_map(|p| match p.first() {
                Some(Segment::Root(r)) => Some(r.as_str()),
                _ => None,
            })
            .collect()
    }

    /// Every `<root> ▸ <a> ▸ <b> ▸ <c>` read, as `(root, a, b, c)`.
    ///
    /// The library reports SHAPE; the caller decides what a shape means. This used to be
    /// `windows()`, which asked "which rolling maxima does this need?" by testing
    /// `root == "metrics" && agg == "max"` — one environment's vocabulary compiled into a
    /// general-purpose type, so renaming a variable in a roster edited a library file.
    ///
    /// A LONGER path matches too: a read may descend past the fourth segment, and the caller that
    /// cares about the first four should not have to care that `files["/a"].closed.elapsed`
    /// continued. A SHORTER one does not — three segments are not a keyed read, and reporting one
    /// as such would hand the caller a tuple it would have to re-validate.
    pub fn keyed_reads(&self) -> impl Iterator<Item = (&str, &str, &str, &str)> {
        self.paths.iter().filter_map(|p| match p.as_slice() {
            [Segment::Root(root), Segment::Key(a), Segment::Key(b), Segment::Key(c), ..] => {
                Some((root.as_str(), a.as_str(), b.as_str(), c.as_str()))
            }
            _ => None,
        })
    }

    /// Merge another set in. The policy-level demand set is the union over every expression.
    pub fn union(&mut self, other: &DemandSet) {
        self.paths.extend(other.paths.iter().cloned());
        self.wide_roots.extend(other.wide_roots.iter().cloned());
        self.prune();
    }

    /// "Which expressions read this path" — the inverse index an event-driven wake needs, so a
    /// close that matters re-evaluates two grants rather than fifty.
    pub fn reverse_index<'a, K: Ord + Clone>(
        sets: &'a [(K, &'a DemandSet)],
    ) -> BTreeMap<&'a [Segment], Vec<K>> {
        let mut out: BTreeMap<&'a [Segment], Vec<K>> = BTreeMap::new();
        for (key, set) in sets {
            for path in set.paths() {
                out.entry(path).or_default().push(key.clone());
            }
        }
        out
    }

    pub(crate) fn record(&mut self, path: Vec<Segment>) {
        if !path.is_empty() {
            self.paths.insert(path);
        }
    }

    pub(crate) fn widen(&mut self, root: String) {
        self.wide_roots.insert(root);
    }

    /// Drop every path that is a strict prefix of another. Called once, when checking finishes.
    pub(crate) fn finish(&mut self) {
        self.prune();
    }

    fn prune(&mut self) {
        let all: Vec<Vec<Segment>> = self.paths.iter().cloned().collect();
        self.paths = all
            .iter()
            .filter(|p| {
                !all.iter()
                    .any(|q| q.len() > p.len() && q.starts_with(p.as_slice()))
            })
            .cloned()
            .collect();
    }
}

impl std::fmt::Display for DemandSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let rendered: Vec<String> = self
            .paths
            .iter()
            .map(|p| {
                p.iter()
                    .map(Segment::to_string)
                    .collect::<Vec<_>>()
                    .join(" ▸ ")
            })
            .collect();
        write!(f, "[{}]", rendered.join(", "))
    }
}
