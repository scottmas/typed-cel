//! The roots one run reads, by name.

use crate::CelValue;

/// The roots one run reads, by name. Small: a program reads a handful of roots, so a linear search
/// beats hashing, and a clone is one `Arc` bump per root.
#[derive(Clone, Default, Debug)]
pub(crate) struct Bindings {
    roots: Vec<(Box<str>, CelValue)>,
}

impl Bindings {
    pub(crate) fn get(&self, name: &str) -> Option<&CelValue> {
        self.roots
            .iter()
            .rev()
            .find(|(n, _)| &**n == name)
            .map(|(_, v)| v)
    }

    /// Bind `name`, replacing an earlier binding of it.
    pub(crate) fn set(&mut self, name: &str, value: CelValue) {
        match self.roots.iter_mut().find(|(n, _)| &**n == name) {
            Some(slot) => slot.1 = value,
            None => self.roots.push((name.into(), value)),
        }
    }

    pub(crate) fn names(&self) -> impl Iterator<Item = &str> {
        self.roots.iter().map(|(n, _)| &**n)
    }
}
