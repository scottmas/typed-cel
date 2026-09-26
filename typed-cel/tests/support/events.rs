//! Owned `typed_cel::Event`s, and a small document-order tokenizer that splits text into
//! fragments — the event vectors the governed-value and streamed-run tests feed.

use typed_cel::Event;

#[derive(Clone, Debug, PartialEq)]
pub enum Ev {
    BeginObject,
    EndObject,
    BeginArray,
    EndArray,
    BeginKey,
    KeyText(String),
    EndKey,
    BeginString,
    Text(String),
    EndString,
    Number(String),
    NumberTooLong,
    Bool(bool),
    Null,
}

impl Ev {
    pub fn as_event(&self) -> Event<'_> {
        match self {
            Ev::BeginObject => Event::BeginObject,
            Ev::EndObject => Event::EndObject,
            Ev::BeginArray => Event::BeginArray,
            Ev::EndArray => Event::EndArray,
            Ev::BeginKey => Event::BeginKey,
            Ev::KeyText(t) => Event::KeyText(t),
            Ev::EndKey => Event::EndKey,
            Ev::BeginString => Event::BeginString,
            Ev::Text(t) => Event::Text(t),
            Ev::EndString => Event::EndString,
            Ev::Number(t) => Event::Number(t),
            Ev::NumberTooLong => Event::NumberTooLong,
            Ev::Bool(b) => Event::Bool(*b),
            Ev::Null => Event::Null,
        }
    }
}

/// `json_text`'s events in DOCUMENT order (so duplicate keys survive), every string and key split
/// into fragments of at most `frag` bytes on char boundaries.
pub fn to_events(json_text: &str, frag: usize) -> Vec<Ev> {
    let mut t = Tok {
        s: json_text.as_bytes(),
        at: 0,
        frag: frag.max(1),
        out: Vec::new(),
    };
    t.value();
    t.ws();
    assert_eq!(t.at, t.s.len(), "trailing text in {json_text:?}");
    t.out
}

struct Tok<'a> {
    s: &'a [u8],
    at: usize,
    frag: usize,
    out: Vec<Ev>,
}

impl Tok<'_> {
    fn ws(&mut self) {
        while self.at < self.s.len() && self.s[self.at].is_ascii_whitespace() {
            self.at += 1;
        }
    }

    fn eat(&mut self, c: u8) {
        self.ws();
        assert_eq!(
            self.s[self.at], c,
            "expected {:?} at {}",
            c as char, self.at
        );
        self.at += 1;
    }

    fn value(&mut self) {
        self.ws();
        match self.s[self.at] {
            b'{' => {
                self.at += 1;
                self.out.push(Ev::BeginObject);
                self.ws();
                if self.s[self.at] == b'}' {
                    self.at += 1;
                } else {
                    loop {
                        self.ws();
                        let k = self.string();
                        self.out.push(Ev::BeginKey);
                        for f in split(&k, self.frag) {
                            self.out.push(Ev::KeyText(f));
                        }
                        self.out.push(Ev::EndKey);
                        self.eat(b':');
                        self.value();
                        self.ws();
                        let c = self.s[self.at];
                        self.at += 1;
                        if c == b'}' {
                            break;
                        }
                        assert_eq!(c, b',');
                    }
                }
                self.out.push(Ev::EndObject);
            }
            b'[' => {
                self.at += 1;
                self.out.push(Ev::BeginArray);
                self.ws();
                if self.s[self.at] == b']' {
                    self.at += 1;
                } else {
                    loop {
                        self.value();
                        self.ws();
                        let c = self.s[self.at];
                        self.at += 1;
                        if c == b']' {
                            break;
                        }
                        assert_eq!(c, b',');
                    }
                }
                self.out.push(Ev::EndArray);
            }
            b'"' => {
                let v = self.string();
                self.out.push(Ev::BeginString);
                for f in split(&v, self.frag) {
                    self.out.push(Ev::Text(f));
                }
                self.out.push(Ev::EndString);
            }
            b't' => self.word("true", Ev::Bool(true)),
            b'f' => self.word("false", Ev::Bool(false)),
            b'n' => self.word("null", Ev::Null),
            _ => {
                let start = self.at;
                while self.at < self.s.len() && b"+-.0123456789eE".contains(&self.s[self.at]) {
                    self.at += 1;
                }
                let n = std::str::from_utf8(&self.s[start..self.at]).unwrap();
                self.out.push(Ev::Number(n.to_string()));
            }
        }
    }

    fn word(&mut self, w: &str, ev: Ev) {
        assert!(self.s[self.at..].starts_with(w.as_bytes()));
        self.at += w.len();
        self.out.push(ev);
    }

    /// A decoded string. Only the escapes the rows use.
    fn string(&mut self) -> String {
        self.eat(b'"');
        let mut out = Vec::new();
        loop {
            let c = self.s[self.at];
            self.at += 1;
            match c {
                b'"' => break,
                b'\\' => {
                    let e = self.s[self.at];
                    self.at += 1;
                    out.push(match e {
                        b'n' => b'\n',
                        b't' => b'\t',
                        other => other,
                    });
                }
                other => out.push(other),
            }
        }
        String::from_utf8(out).unwrap()
    }
}

/// `s` in pieces of at most `n` bytes, never splitting a char. An empty string is no pieces.
pub fn split(s: &str, n: usize) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        if !cur.is_empty() && cur.len() + ch.len_utf8() > n {
            out.push(std::mem::take(&mut cur));
        }
        cur.push(ch);
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}
