//! `EXCLUSIONS.toml` — the cases the dialect does not implement, and why.
//!
//! EXCLUDED is the dangerous outcome, because it is the one a tired person reaches for to make a
//! red go away. Two things stop that: every rule must carry a `reason`, and every reason must be
//! an id that appears in the README's dialect tables (`exclusions_cite_the_readme`). Excluding a
//! case therefore means editing the document that DEFINES the language — which is exactly the
//! friction that should exist.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;

use super::case::Case;

#[derive(Debug, Deserialize)]
pub struct Exclusions {
    #[serde(default, rename = "exclude")]
    pub rules: Vec<Rule>,
}

// `deny_unknown_fields`, so a key this reader does not know — a misspelled `section`, or a field
// from an older format — is an error rather than a rule that quietly matches more than it says.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Rule {
    /// Corpus file stem, e.g. `proto2`. Required — there is no wildcard over files, so an
    /// exclusion can never quietly grow to cover the whole corpus.
    pub file: String,
    /// Section name, or `*` / absent for every section in the file.
    #[serde(default)]
    pub section: Option<String>,
    /// Case name, or absent for every case in the matched sections.
    #[serde(default)]
    pub case: Option<String>,
    /// Must match a dialect-row id in README.md, verbatim.
    pub reason: String,
}

impl Rule {
    pub fn matches(&self, case: &Case) -> bool {
        if self.file != case.file {
            return false;
        }
        if let Some(section) = &self.section {
            if section != "*" && section != &case.section {
                return false;
            }
        }
        match &self.case {
            Some(name) => name == &case.name,
            None => true,
        }
    }

    /// How the rule reads in a report or an error message.
    pub fn label(&self) -> String {
        format!(
            "{}/{}/{}",
            self.file,
            self.section.as_deref().unwrap_or("*"),
            self.case.as_deref().unwrap_or("*")
        )
    }
}

impl Exclusions {
    pub fn load(path: &Path) -> Result<Exclusions, String> {
        let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        toml::from_str(&src).map_err(|e| format!("{}: {e}", path.display()))
    }

    /// The reason this case is excluded, or `None` if it is meant to run.
    pub fn reason_for(&self, case: &Case) -> Option<&str> {
        self.rules
            .iter()
            .find(|r| r.matches(case))
            .map(|r| r.reason.as_str())
    }

    /// Every distinct reason, with how many cases it excluded. Drives the report's footer.
    pub fn tally<'a>(&'a self, cases: impl Iterator<Item = &'a Case>) -> BTreeMap<&'a str, usize> {
        let mut out: BTreeMap<&str, usize> =
            self.rules.iter().map(|r| (r.reason.as_str(), 0)).collect();
        for case in cases {
            if let Some(reason) = self.reason_for(case) {
                *out.entry(reason).or_default() += 1;
            }
        }
        out
    }

    /// Rules that match no case in the corpus. A rule covering nothing is a false claim of
    /// understanding — it usually means a file was renamed upstream, or a case name was guessed.
    pub fn dead_rules<'a>(&'a self, cases: &[&Case]) -> Vec<&'a Rule> {
        self.rules
            .iter()
            .filter(|r| !cases.iter().any(|c| r.matches(c)))
            .collect()
    }
}
