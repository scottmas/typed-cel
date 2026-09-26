//! What a streamed document looks like to a [`crate::StreamedRun`].

/// One step of a JSON document, in document order.
///
/// Text arrives DECODED and in FRAGMENTS whose boundaries are arbitrary; every fragment is a `&str`,
/// so a boundary never splits a UTF-8 sequence. [`Event::Number`] carries a COMPLETE token; a producer
/// past its own cap sends [`Event::NumberTooLong`], which carries no text.
///
/// Producing events (tokenizing the bytes) is the caller's job: this crate only consumes them.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Event<'a> {
    BeginObject,
    EndObject,
    BeginArray,
    EndArray,
    /// An object member's key, in fragments.
    BeginKey,
    KeyText(&'a str),
    EndKey,
    /// A string VALUE, in fragments.
    BeginString,
    Text(&'a str),
    EndString,
    /// A complete number token, as written.
    Number(&'a str),
    /// A number token past the producer's cap. No text: nothing may judge it.
    NumberTooLong,
    Bool(bool),
    Null,
}
