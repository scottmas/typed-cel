//! The payloads of a literal: plain scalars, as the parser read them.
//!
//! These were the fork's value types, which were also its run-time values; with the fork's value
//! model deleted they are only syntax. The names and shapes are kept so the parser and the checker
//! read unchanged.

use std::ops::Deref;
use std::string::String as StdString;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Bool(bool);

impl Bool {
    pub fn into_inner(self) -> bool {
        self.0
    }

    pub fn inner(&self) -> &bool {
        &self.0
    }
}

impl Deref for Bool {
    type Target = bool;
    fn deref(&self) -> &bool {
        &self.0
    }
}

impl From<bool> for Bool {
    fn from(b: bool) -> Bool {
        Bool(b)
    }
}

impl From<Bool> for bool {
    fn from(b: Bool) -> bool {
        b.0
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Bytes(Vec<u8>);

impl Bytes {
    pub fn into_inner(self) -> Vec<u8> {
        self.0
    }

    pub fn inner(&self) -> &[u8] {
        &self.0
    }
}

impl Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(b: Vec<u8>) -> Bytes {
        Bytes(b)
    }
}

impl From<Bytes> for Vec<u8> {
    fn from(b: Bytes) -> Vec<u8> {
        b.0
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Double(f64);

impl Double {
    pub fn into_inner(self) -> f64 {
        self.0
    }

    pub fn inner(&self) -> &f64 {
        &self.0
    }
}

impl Deref for Double {
    type Target = f64;
    fn deref(&self) -> &f64 {
        &self.0
    }
}

impl From<f64> for Double {
    fn from(f: f64) -> Double {
        Double(f)
    }
}

impl From<Double> for f64 {
    fn from(f: Double) -> f64 {
        f.0
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct String(StdString);

impl String {
    pub fn into_inner(self) -> StdString {
        self.0
    }

    pub fn inner(&self) -> &str {
        &self.0
    }
}

impl Deref for String {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl From<StdString> for String {
    fn from(s: StdString) -> String {
        String(s)
    }
}

impl From<&str> for String {
    fn from(s: &str) -> String {
        String(s.into())
    }
}

impl From<String> for StdString {
    fn from(s: String) -> StdString {
        s.0
    }
}
