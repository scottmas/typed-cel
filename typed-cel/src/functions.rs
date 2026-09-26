use crate::context::Context;
use crate::magic::This;
use crate::objects::{KeyRef, Value};
use crate::resolvers::Resolver;
use crate::ExecutionError;
use std::borrow::Cow;
use std::sync::Arc;

type Result<T> = std::result::Result<T, ExecutionError>;

/// `FunctionContext` is a context object passed to functions when they are called.
///
/// It contains references to the target object (if the function is called as
/// a method), the program context ([`Context`]) which gives functions access
/// to variables, and the arguments to the function call.
#[derive(Clone)]
pub struct FunctionContext<'context, 'call: 'context> {
    pub name: &'call str,
    pub this: Option<Cow<'context, dyn Val>>,
    pub ptx: &'context Context<'context>,
    pub args: Vec<Cow<'context, dyn Val>>,
    pub arg_idx: usize,
}

impl<'context, 'call: 'context> FunctionContext<'context, 'call> {
    pub fn new(
        name: &'call str,
        this: Option<Cow<'context, dyn Val>>,
        ptx: &'context Context<'context>,
        args: Vec<Cow<'context, dyn Val>>,
    ) -> Self {
        Self {
            name,
            this,
            ptx,
            args,
            arg_idx: 0,
        }
    }

    /// Resolves the given expression using the program's [`Context`].
    pub fn resolve<R>(&self, resolver: R) -> Result<Value>
    where
        R: Resolver,
    {
        resolver.resolve(self)
    }

    /// Returns an execution error for the currently execution function.
    pub fn error<M: ToString>(&self, message: M) -> ExecutionError {
        ExecutionError::function_error(self.name, message)
    }
}

/// Calculates the size of either the target, or the provided args depending on how
/// the function is called.
///
/// If called as a method, the target will be used. If called as a function, the
/// first argument will be used.
///
/// The following [`Value`] variants are supported:
/// * [`Value::List`]
/// * [`Value::Map`]
///
/// # Examples
/// ```skip
/// size([1, 2, 3]) == 3
/// ```
pub fn size(ftx: &FunctionContext, This(this): This<Value>) -> Result<f64> {
    let size = match this {
        Value::List(l) => l.len(),
        Value::Map(m) => m.map.len(),
        value => return Err(ftx.error(format!("cannot determine the size of {value:?}"))),
    };
    Ok(size as f64)
}

/// Returns true if the target contains the provided argument. The actual behavior
/// depends mainly on the type of the target.
///
/// The following [`Value`] variants are supported:
/// * [`Value::List`] - Returns true if the list contains the provided value.
/// * [`Value::Map`] - Returns true if the map contains the provided key.
/// * [`Value::String`] - Returns true if the string contains the provided substring.
/// * [`Value::Bytes`] - Returns true if the bytes contain the provided byte.
///
/// # Example
///
/// ## List
/// ```cel
/// [1, 2, 3].contains(1) == true
/// ```
///
/// ## Map
/// ```cel
/// {"a": 1, "b": 2, "c": 3}.contains("a") == true
/// ```
///
/// ## String
/// ```cel
/// "abc".contains("b") == true
/// ```
///
/// ## Bytes
/// ```cel
/// b"abc".contains(b"c") == true
/// ```
pub fn contains(This(this): This<Value>, arg: Value) -> Result<Value> {
    Ok(match this {
        Value::List(v) => v.contains(&arg),
        Value::Map(v) => {
            v.contains_key(&KeyRef::try_from(&arg).map_err(ExecutionError::UnsupportedKeyType)?)
        }
        Value::String(s) => {
            if let Value::String(arg) = arg {
                s.contains(arg.as_str())
            } else {
                false
            }
        }
        _ => false,
    }
    .into())
}

/// Returns true if a string matches the regular expression.
///
/// # Example
/// ```cel
/// "abc".matches("^[a-z]*$") == true
/// ```
#[cfg(feature = "regex")]
pub fn matches(
    ftx: &FunctionContext,
    This(this): This<Arc<String>>,
    regex: Arc<String>,
) -> Result<bool> {
    match regex::Regex::new(&regex) {
        Ok(re) => Ok(re.is_match(&this)),
        Err(err) => Err(ftx.error(format!("'{regex}' not a valid regex:\n{err}"))),
    }
}

use crate::common::value::Val;
#[cfg(feature = "chrono")]
pub use time::duration;

#[cfg(feature = "chrono")]
pub mod time {
    use super::Result;
    use crate::magic::This;
    use crate::{ExecutionError, Value};
    use std::sync::Arc;

    /// Duration parses the provided argument into a [`Value::Duration`] value.
    ///
    /// The argument must be string, and must be in the format of a duration. See
    /// the [`crate::duration::parse_duration`] documentation for more information on the supported
    /// formats.
    ///
    /// # Examples
    /// - `1h` parses as 1 hour
    /// - `1.5h` parses as 1 hour and 30 minutes
    /// - `1h30m` parses as 1 hour and 30 minutes
    /// - `1h30m1s` parses as 1 hour, 30 minutes, and 1 second
    /// - `1ms` parses as 1 millisecond
    /// - `1.5ms` parses as 1 millisecond and 500 microseconds
    /// - `1ns` parses as 1 nanosecond
    /// - `1.5ns` parses as 1 nanosecond (sub-nanosecond durations not supported)
    pub fn duration(value: Arc<String>) -> crate::functions::Result<Value> {
        Ok(Value::Duration({
            let i = value.as_str();
            let (_, duration) = crate::duration::parse_duration(i)
                .map_err(|e| ExecutionError::function_error("duration", e.to_string()))?;
            Ok(duration)
        }?))
    }

    pub fn get_seconds(This(this): This<Value>) -> Result<Value> {
        Ok(match this {
            Value::Duration(d) => (d.num_seconds() as i32).into(),
            _ => {
                return Err(ExecutionError::function_error(
                    "getSeconds",
                    "expected a duration",
                ))
            }
        })
    }

    pub fn get_milliseconds(This(this): This<Value>) -> Result<Value> {
        Ok(match this {
            Value::Duration(d) => (d.num_milliseconds() as i32).into(),
            _ => {
                return Err(ExecutionError::function_error(
                    "getMilliseconds",
                    "expected a duration",
                ))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::context::Context;
    use crate::tests::test_script;

    fn assert_script(input: &(&str, &str)) {
        assert_eq!(test_script(input.1, None), Ok(true.into()), "{}", input.0);
    }

    fn assert_error(input: &(&str, &str, &str)) {
        assert_eq!(
            test_script(input.1, None).map_err(|e| e.to_string()),
            Err(input.2.to_string()),
            "{}",
            input.0
        );
    }

    #[test]
    fn test_size() {
        [
            ("size of list", "size([1, 2, 3]) == 3"),
            ("size of map", "size({'a': 1, 'b': 2, 'c': 3}) == 3"),
            ("size as a list method", "[1, 2, 3].size() == 3"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_has() {
        let tests = vec![
            ("map has", "has(foo.bar) == true"),
            ("map not has", "has(foo.baz) == false"),
        ];

        for (name, script) in tests {
            let mut ctx = Context::default();
            ctx.add_variable_from_value("foo", std::collections::HashMap::from([("bar", 1)]));
            assert_eq!(test_script(script, Some(ctx)), Ok(true.into()), "{name}");
        }
    }

    #[test]
    fn test_map() {
        [
            ("map list", "[1, 2, 3].map(x, x * 2) == [2, 4, 6]"),
            ("map list 2", "[1, 2, 3].map(y, y + 1) == [2, 3, 4]"),
            ("map list filter", "[1, 2, 3].map(y, y == 2, y + 1) == [3]"),
            (
                "nested map",
                "[[1, 2], [2, 3]].map(x, x.map(x, x * 2)) == [[2, 4], [4, 6]]",
            ),
            (
                "map to list",
                r#"{'John': 'smart'}.map(key, key) == ['John']"#,
            ),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_filter() {
        [("filter list", "[1, 2, 3].filter(x, x > 2) == [3]")]
            .iter()
            .for_each(assert_script);
    }

    #[test]
    fn test_all() {
        [
            ("all list #1", "[0, 1, 2].all(x, x >= 0)"),
            ("all list #2", "[0, 1, 2].all(x, x > 0) == false"),
            ("all map", "{0: 0, 1:1, 2:2}.all(x, x >= 0) == true"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_exists() {
        [
            ("exist list #1", "[0, 1, 2].exists(x, x > 0)"),
            ("exist list #2", "[0, 1, 2].exists(x, x == 3) == false"),
            ("exist list #3", "[0, 1, 2, 2].exists(x, x == 2)"),
            ("exist map", "{0: 0, 1:1, 2:2}.exists(x, x > 0)"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_exists_one() {
        [
            ("exist list #1", "[0, 1, 2].exists_one(x, x > 0) == false"),
            ("exist list #2", "[0, 1, 2].exists_one(x, x == 0)"),
            ("exist map", "{0: 0, 1:1, 2:2}.exists_one(x, x == 2)"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_starts_with() {
        [
            ("starts with true", "'foobar'.startsWith('foo') == true"),
            ("starts with false", "'foobar'.startsWith('bar') == false"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_ends_with() {
        [
            ("ends with true", "'foobar'.endsWith('bar') == true"),
            ("ends with false", "'foobar'.endsWith('foo') == false"),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[cfg(feature = "chrono")]
    #[cfg(feature = "chrono")]
    #[test]
    fn test_duration() {
        [
            ("duration equal 1", "duration('1s') == duration('1000ms')"),
            ("duration equal 2", "duration('1m') == duration('60s')"),
            ("duration equal 3", "duration('1h') == duration('60m')"),
            ("duration comparison 1", "duration('1m') > duration('1s')"),
            ("duration comparison 2", "duration('1m') < duration('1h')"),
            (
                "duration subtraction",
                "duration('1h') - duration('1m') == duration('59m')",
            ),
            (
                "duration addition",
                "duration('1h') + duration('1m') == duration('1h1m')",
            ),
            (
                "duration getSeconds",
                "duration('2h30m45s').getSeconds() == 9045",
            ),
            (
                "duration getMilliseconds",
                "duration('1s500ms').getMilliseconds() == 1500",
            ),
            (
                "duration getSeconds overflow",
                "duration('90s').getSeconds() == 90",
            ),
        ]
        .iter()
        .for_each(assert_script);
    }

    #[test]
    fn test_contains() {
        let tests = vec![("string", "'foobar'.contains('bar') == true")];

        for (name, script) in tests {
            assert_eq!(test_script(script, None), Ok(true.into()), "{name}");
        }
    }

    #[cfg(feature = "regex")]
    #[test]
    fn test_matches() {
        let tests = vec![
            ("string", "'foobar'.matches('^[a-zA-Z]*$') == true"),
            (
                "map",
                "{'1': 'abc', '2': 'def', '3': 'ghi'}.all(key, key.matches('^[a-zA-Z]*$')) == false",
            ),
        ];

        for (name, script) in tests {
            assert_eq!(
                test_script(script, None),
                Ok(true.into()),
                ".matches failed for '{name}'"
            );
        }
    }

    #[cfg(feature = "regex")]
    #[test]
    fn test_matches_err() {
        assert_eq!(
            test_script(
                "'foobar'.matches('(foo') == true", None),
            Err(
                crate::ExecutionError::FunctionError {
                    function: "matches".to_string(),
                    message: "'(foo' not a valid regex:\nregex parse error:\n    (foo\n    ^\nerror: unclosed group".to_string()
                }
            )
        );
    }

    #[test]
    fn no_bool_coercion() {
        [
            ("string || bool", "'' || false", "No such overload"),
            ("int || bool", "1 || false", "No such overload"),
            ("float || bool", "0.1|| false", "No such overload"),
            ("list || bool", "[] || false", "No such overload"),
            ("map || bool", "{} || false", "No such overload"),
            ("null || bool", "null || false", "No such overload"),
        ]
        .iter()
        .for_each(assert_error)
    }
}
