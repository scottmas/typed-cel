use crate::common::{
    decls::FunctionDecl,
    functions::Function,
    types::{self, Type},
    value::Val,
};
use std::{
    borrow::Cow,
    collections::{
        btree_map::Entry::{Occupied, Vacant},
        BTreeMap,
    },
};

/// An environment for the CEL execution.
///
/// This is where functions and overloads are defined.
///
/// # Example
///
/// ## Function Overloads
///
/// You can add custom function overloads to the environment.
///
/// ```
/// use typed_cel::fork::{common::types, common::value::Val, Env};
/// use std::borrow::Cow;
///
/// let mut env = Env::stdlib();
///
/// // Define a function that takes a number and returns its square.
/// env.add_overload("square", "double_square", vec![types::DOUBLE_TYPE], |args| {
///     let val = args[0].downcast_ref::<typed_cel::fork::common::types::CelDouble>().unwrap();
///     let result: Box<dyn Val> = Box::new(typed_cel::fork::common::types::CelDouble::from(val.inner() * val.inner()));
///     Ok(Cow::Owned(result))
/// }).unwrap();
/// ```
#[derive(Default)]
pub struct Env {
    functions: BTreeMap<String, FunctionDecl>,
}

impl Env {
    /// Returns the standard library environment.
    ///
    /// This environment contains all the standard functions and types as defined by the
    /// CEL specification.
    pub fn stdlib() -> Env {
        let mut env = Env::default();
        types::list::stdlib(&mut env);
        types::map::stdlib(&mut env);
        types::string::stdlib(&mut env);

        #[cfg(feature = "chrono")]
        {
            types::duration::stdlib(&mut env);
        }
        env
    }

    /// Does this table declare any overload named `name`? A host function never takes one.
    pub(crate) fn declares(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Adds a global function overload to the environment.
    ///
    /// The name is the function name (e.g., `_==_`, `size`).
    /// The id is the unique identifier for this overload (e.g., `equals_int64`).
    /// The args are the expected argument types.
    /// The op is the function implementation.
    #[allow(clippy::result_unit_err)]
    pub fn add_overload(
        &mut self,
        name: &str,
        id: &str,
        args: Vec<types::Type>,
        op: Function,
    ) -> Result<(), ()> {
        match self.functions.entry(name.to_owned()) {
            Vacant(vacant_entry) => {
                let mut value = FunctionDecl::new(name);
                value.add_overload(id.to_string(), false, args, op)?;
                vacant_entry.insert(value);
                Ok(())
            }
            Occupied(occupied_entry) => {
                occupied_entry
                    .into_mut()
                    .add_overload(id.to_string(), false, args, op)
            }
        }
    }

    /// Finds a global function overload that matches the given name and arguments.
    pub fn find_overload(&self, name: &str, args: &[Cow<dyn Val>]) -> Option<Function> {
        match self.functions.get(name) {
            None => None,
            Some(fn_decl) => fn_decl.find_overload(false, args),
        }
    }

    /// Adds a member function overload to the environment.
    ///
    /// A member function is one that is called using the receiver syntax (e.g., `x.matches(y)`).
    /// The name is the function name.
    /// The id is the unique identifier for this overload.
    /// The target is the type of the receiver.
    /// The args are the expected argument types (excluding the receiver).
    /// The op is the function implementation.
    #[allow(clippy::result_unit_err)]
    pub fn add_member_overload(
        &mut self,
        name: &str,
        id: &str,
        target: Type,
        args: Vec<types::Type>,
        op: Function,
    ) -> Result<(), ()> {
        let mut args = args;
        args.insert(0, target);
        match self.functions.entry(name.to_owned()) {
            Vacant(vacant_entry) => {
                let mut value = FunctionDecl::new(name);
                value.add_overload(id.to_string(), true, args, op)?;
                vacant_entry.insert(value);
                Ok(())
            }
            Occupied(occupied_entry) => {
                occupied_entry
                    .into_mut()
                    .add_overload(id.to_string(), true, args, op)
            }
        }
    }

    /// Finds a member function overload that matches the given name and arguments.
    pub(crate) fn find_member_overload(
        &self,
        name: &str,
        args: &[Cow<dyn Val>],
    ) -> Option<Function> {
        match self.functions.get(name) {
            None => None,
            Some(fn_decl) => fn_decl.find_overload(true, args),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_env_default() {
        let _: Arc<dyn Send + Sync> = Arc::new(Env::default());
    }
}
