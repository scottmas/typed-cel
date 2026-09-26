use chrono::Duration;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::char;
use nom::combinator::{map, opt};
use nom::error::{Error, ErrorKind};
use nom::multi::many1;
use nom::number::complete::double;
use nom::IResult;

/// Parses a duration string into a [`Duration`]. Duration strings support the
/// following grammar:
///
/// DurationString -> Sign? Number Unit String?
/// Sign           -> '-'
/// Number         -> Digit+ ('.' Digit+)?
/// Digit          -> '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
/// Unit           -> 'h' | 'm' | 's' | 'ms' | 'us' | 'ns'
/// String         -> DurationString
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
pub fn parse_duration(i: &str) -> IResult<&str, Duration> {
    let (i, neg) = opt(parse_negative)(i)?;
    if i == "0" {
        return Ok((i, Duration::zero()));
    }
    let (rest, parts) = many1(parse_number_unit)(i)?;
    // `acc + *next` panics on overflow in a debug build and wraps in release, and neither is a
    // duration. The fold is checked, and the RESULT is held to the language's range rather than to
    // `chrono::TimeDelta`'s — see `in_cel_range`, which is 34x tighter.
    let total = parts
        .iter()
        .try_fold(Duration::zero(), |acc, next| acc.checked_add(next))
        .filter(in_cel_range)
        .ok_or_else(|| out_of_range(i))?;
    Ok((rest, if neg.is_some() { -total } else { total }))
}

/// CEL's duration range: ±315576000000 seconds, which is ±10000 years.
///
/// NOT `chrono::TimeDelta`'s range, and the difference is the whole reason this constant exists.
/// `TimeDelta::nanoseconds` tops out at ±i64 nanoseconds — about 292 years — so a value can be
/// perfectly legal in the LANGUAGE and unrepresentable through that constructor, and a value can be
/// representable and still outside the language. Two such values also `checked_add` without
/// tripping anything, which is why checking only where a literal is parsed leaves the arithmetic
/// wrong.
pub const CEL_DURATION_MAX_SECS: i64 = 315_576_000_000;

/// Is `d` inside the range CEL gives a duration?
///
/// The sub-second arm is load-bearing: `num_seconds` truncates toward zero, so the bound plus one
/// nanosecond reports as exactly the bound and a comparison on seconds alone lets it through.
pub(crate) fn in_cel_range(d: &Duration) -> bool {
    let secs = d.num_seconds();
    match secs.abs().cmp(&CEL_DURATION_MAX_SECS) {
        std::cmp::Ordering::Less => true,
        std::cmp::Ordering::Greater => false,
        std::cmp::Ordering::Equal => d.subsec_nanos() == 0,
    }
}

/// The out-of-range refusal, as a nom error.
///
/// A `Failure` rather than an `Error` so `many1` does not backtrack and report the input as merely
/// unparseable: the digits ARE a duration, and the thing wrong with it is its size. It must not be
/// a panic — `timestamps/duration_range/add_under` exists precisely to catch a decoder that aborts
/// instead of returning, and a panic in the evaluator violates the crate's recovery rule.
fn out_of_range(i: &str) -> nom::Err<Error<&str>> {
    nom::Err::Failure(Error::new(i, ErrorKind::TooLarge))
}

enum Unit {
    Nanosecond,
    Microsecond,
    Millisecond,
    Second,
    Minute,
    Hour,
}

impl Unit {
    fn nanos(&self) -> i64 {
        match self {
            Unit::Nanosecond => 1,
            Unit::Microsecond => 1_000,
            Unit::Millisecond => 1_000_000,
            Unit::Second => 1_000_000_000,
            Unit::Minute => 60 * 1_000_000_000,
            Unit::Hour => 60 * 60 * 1_000_000_000,
        }
    }
}

fn parse_number_unit(i: &str) -> IResult<&str, Duration> {
    let (rest, num) = double(i)?;
    let (rest, unit) = parse_unit(rest)?;
    let duration = to_duration(num, unit).ok_or_else(|| out_of_range(i))?;
    Ok((rest, duration))
}

fn parse_negative(i: &str) -> IResult<&str, ()> {
    let (i, _): (&str, char) = char('-')(i)?;
    Ok((i, ()))
}

fn parse_unit(i: &str) -> IResult<&str, Unit> {
    alt((
        map(tag("ms"), |_| Unit::Millisecond),
        map(tag("us"), |_| Unit::Microsecond),
        map(tag("ns"), |_| Unit::Nanosecond),
        map(char('h'), |_| Unit::Hour),
        map(char('m'), |_| Unit::Minute),
        map(char('s'), |_| Unit::Second),
    ))(i)
}

/// One `<number><unit>` component, or `None` if it cannot be represented at all.
///
/// Built from SECONDS plus a remainder rather than from total nanoseconds. `Duration::nanoseconds`
/// takes an `i64`, and a float-to-int cast in Rust SATURATES rather than failing — so the old
/// one-liner turned `320000000000s` into `i64::MAX` nanoseconds and handed back a plausible-looking
/// 292-year span that nothing downstream could tell from a value the author wrote.
///
/// The language's range check is deliberately NOT here: it belongs once, on the summed result, so
/// that `1h30m` is judged as the duration it denotes rather than component by component.
fn to_duration(num: f64, unit: Unit) -> Option<Duration> {
    let total_nanos = num * unit.nanos() as f64;
    if !total_nanos.is_finite() {
        return None;
    }
    let secs = (total_nanos / 1e9).trunc();
    if secs < i64::MIN as f64 || secs > i64::MAX as f64 {
        return None;
    }
    let rem = (total_nanos - secs * 1e9).trunc();
    Duration::try_seconds(secs as i64)?.checked_add(&Duration::nanoseconds(rem as i64))
}

#[cfg(test)]
mod tests {
    use crate::duration::parse_duration;
    use chrono::Duration;

    fn assert_duration(input: &str, expected: Duration) {
        let (_, duration) = parse_duration(input).unwrap();
        assert_eq!(duration, expected, "{input}");
    }

    macro_rules! assert_durations {
        ($($str:expr => $duration:expr),*$(,)?) => {
            #[test]
            fn test_durations() {
                $(
                    assert_duration($str, $duration);
                )*
            }
        };
    }

    assert_durations! {
        "1s" => Duration::seconds(1),
        "-1s" => Duration::seconds(-1),
        "1.1s" => Duration::seconds(1) + Duration::milliseconds(100),
        "1.5m" => Duration::minutes(1) + Duration::seconds(30),
        "1m1s" => Duration::minutes(1) + Duration::seconds(1),
        "1h1m1s" => Duration::hours(1) + Duration::minutes(1) + Duration::seconds(1),
        "1ms" => Duration::milliseconds(1),
        "1us" => Duration::microseconds(1),
        "1ns" => Duration::nanoseconds(1),
        "1.1ns" => Duration::nanoseconds(1),
        "1.123us" => Duration::microseconds(1) + Duration::nanoseconds(123),
        "0s" => Duration::zero(),
        "0h0m0s" => Duration::zero(),
        "0h0m1s" => Duration::seconds(1),
        "0" => Duration::zero(),
        "-0" => Duration::zero(),
    }
}
