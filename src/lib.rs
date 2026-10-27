//! # packed_seq
//!
//! Append-only CBOR *sequences* (RFC 8742) with Packed-CBOR-style compression
//! (`draft-ietf-cbor-packed-19`), built on `ciborium`.
//!
//! ## File convention (the "application environment" of the draft, section 3)
//!
//! * The file is a plain CBOR sequence: `item item item ...`.
//! * A **dictionary record** is a top-level item
//!   `1113([ [shared items...], [argument items...], undefined ])`.
//!   Unlike the draft's *prepending* table-setup tag, a record in this file
//!   format **appends** its items to the file-wide tables, so existing table
//!   indices never change and previously written entries stay valid forever.
//!   Records may occur anywhere; each only affects entries after it.
//! * Every other top-level item is an **entry**, packed against the tables
//!   accumulated so far. Entries carry no table-setup tag of their own.
//!
//! ## Supported subset of the draft
//!
//! * Decoding: shared references (simple 0..15, tag 6(int)), straight and
//!   inverted argument references (tags 128..143, tag 6([int, rump])), with
//!   concatenation of text/byte strings, arrays and maps.
//! * Encoding: shared references and straight (prefix) references on text.
//! * Not implemented: function tags (105/106/114), integration tag 1115,
//!   `undefined`-as-deletion in map concatenation, packed table items,
//!   tag 1112 error values. Dictionary items are stored *unpacked*, which also
//!   rules out reference loops by construction.
//!
//! `ciborium::Value` cannot represent simple values, so this crate uses
//! `ciborium-ll` for the wire level and a private tree type for packed items.

use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::path::Path;

pub use ciborium::value::{Integer, Value};
use ciborium_ll::{simple, Decoder, Encoder, Header};

const TAG_REF: u64 = 6;
const TAG_TABLE: u64 = 1113;
const TAG_STRAIGHT: std::ops::RangeInclusive<u64> = 128..=135;
const TAG_INVERTED: std::ops::RangeInclusive<u64> = 136..=143;
const MAX_DEPTH: usize = 128;

// ---------------------------------------------------------------- errors ---

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),
    #[error("malformed CBOR at offset {0}")]
    Syntax(usize),
    #[error("truncated CBOR item (torn write?)")]
    Truncated,
    #[error("nesting too deep")]
    TooDeep,
    #[error("reference to undefined shared item {0}")]
    UnknownShared(usize),
    #[error("reference to undefined argument item {0}")]
    UnknownArgument(usize),
    #[error("invalid packed reference: {0}")]
    BadReference(&'static str),
    #[error("cannot concatenate these item types")]
    BadConcat,
    #[error("unsupported: {0}")]
    Unsupported(String),
    #[error("serde: {0}")]
    Serde(String),
}
pub type Result<T> = std::result::Result<T, Error>;

impl From<ciborium_ll::Error<io::Error>> for Error {
    fn from(e: ciborium_ll::Error<io::Error>) -> Self {
        match e {
            ciborium_ll::Error::Io(e) if e.kind() == io::ErrorKind::UnexpectedEof => Error::Truncated,
            ciborium_ll::Error::Io(e) => Error::Io(e),
            ciborium_ll::Error::Syntax(o) => Error::Syntax(o),
        }
    }
}

// ------------------------------------------------- wire-level item tree ---

/// A CBOR item including simple values (which `ciborium::Value` lacks).
#[derive(Clone, Debug, PartialEq)]
enum Node {
    Int(Integer),
    Bytes(Vec<u8>),
    Text(String),
    Float(f64),
    Simple(u8),
    Tag(u64, Box<Node>),
    Array(Vec<Node>),
    Map(Vec<(Node, Node)>),
}

fn read_node<R: Read>(dec: &mut Decoder<&mut R>, depth: usize) -> Result<Node> {
    let h = dec.pull()?;
    node_from_header(dec, h, depth)
}

fn node_from_header<R: Read>(dec: &mut Decoder<&mut R>, h: Header, depth: usize) -> Result<Node> {
    if depth > MAX_DEPTH {
        return Err(Error::TooDeep);
    }
    Ok(match h {
        Header::Positive(n) => Node::Int(Integer::from(n)),
        Header::Negative(n) => Node::Int(
            Integer::try_from(-1i128 - n as i128).map_err(|_| Error::Syntax(dec.offset()))?,
        ),
        Header::Float(f) => Node::Float(f),
        Header::Simple(s) => Node::Simple(s),
        Header::Tag(t) => Node::Tag(t, Box::new(read_node(dec, depth + 1)?)),
        Header::Break => return Err(Error::Syntax(dec.offset())),
        Header::Bytes(len) => {
            let (mut out, mut buf) = (Vec::new(), [0u8; 512]);
            let mut segs = dec.bytes(len);
            while let Some(mut seg) = segs.pull()? {
                while let Some(chunk) = seg.pull(&mut buf)? {
                    out.extend_from_slice(chunk);
                }
            }
            Node::Bytes(out)
        }
        Header::Text(len) => {
            let (mut out, mut buf) = (String::new(), [0u8; 512]);
            let mut segs = dec.text(len);
            while let Some(mut seg) = segs.pull()? {
                while let Some(chunk) = seg.pull(&mut buf)? {
                    out.push_str(chunk);
                }
            }
            Node::Text(out)
        }
        // Never pre-allocate from an untrusted length.
        Header::Array(Some(n)) => {
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(read_node(dec, depth + 1)?);
            }
            Node::Array(v)
        }
        Header::Array(None) => {
            let mut v = Vec::new();
            loop {
                match dec.pull()? {
                    Header::Break => break,
                    h => v.push(node_from_header(dec, h, depth + 1)?),
                }
            }
            Node::Array(v)
        }
        Header::Map(Some(n)) => {
            let mut v = Vec::new();
            for _ in 0..n {
                let k = read_node(dec, depth + 1)?;
                v.push((k, read_node(dec, depth + 1)?));
            }
            Node::Map(v)
        }
        Header::Map(None) => {
            let mut v = Vec::new();
            loop {
                match dec.pull()? {
                    Header::Break => break,
                    h => {
                        let k = node_from_header(dec, h, depth + 1)?;
                        v.push((k, read_node(dec, depth + 1)?));
                    }
                }
            }
            Node::Map(v)
        }
    })
}

fn write_node(enc: &mut Encoder<&mut Vec<u8>>, n: &Node) -> io::Result<()> {
    match n {
        Node::Int(i) => {
            let v: i128 = (*i).into();
            enc.push(if v >= 0 { Header::Positive(v as u64) } else { Header::Negative((-1 - v) as u64) })
        }
        Node::Bytes(b) => enc.bytes(b, None),
        Node::Text(s) => enc.text(s, None),
        Node::Float(f) => enc.push(Header::Float(*f)),
        Node::Simple(s) => enc.push(Header::Simple(*s)),
        Node::Tag(t, inner) => {
            enc.push(Header::Tag(*t))?;
            write_node(enc, inner)
        }
        Node::Array(items) => {
            enc.push(Header::Array(Some(items.len())))?;
            items.iter().try_for_each(|i| write_node(enc, i))
        }
        Node::Map(items) => {
            enc.push(Header::Map(Some(items.len())))?;
            items.iter().try_for_each(|(k, v)| {
                write_node(enc, k)?;
                write_node(enc, v)
            })
        }
    }
}

fn encode_node(n: &Node) -> Result<Vec<u8>> {
    let mut buf = Vec::new();
    write_node(&mut Encoder::from(&mut buf), n)?;
    Ok(buf)
}

fn value_to_node(v: &Value) -> Node {
    match v {
        Value::Integer(i) => Node::Int(*i),
        Value::Bytes(b) => Node::Bytes(b.clone()),
        Value::Float(f) => Node::Float(*f),
        Value::Text(s) => Node::Text(s.clone()),
        Value::Bool(b) => Node::Simple(if *b { simple::TRUE } else { simple::FALSE }),
        Value::Null => Node::Simple(simple::NULL),
        Value::Tag(t, inner) => Node::Tag(*t, Box::new(value_to_node(inner))),
        Value::Array(a) => Node::Array(a.iter().map(value_to_node).collect()),
        Value::Map(m) => Node::Map(m.iter().map(|(k, v)| (value_to_node(k), value_to_node(v))).collect()),
        _ => Node::Simple(simple::NULL), // Value is #[non_exhaustive]
    }
}

/// Convert a node with *no packed references left* into a `Value`.
fn node_to_value(n: &Node) -> Result<Value> {
    Ok(match n {
        Node::Int(i) => Value::Integer(*i),
        Node::Bytes(b) => Value::Bytes(b.clone()),
        Node::Text(s) => Value::Text(s.clone()),
        Node::Float(f) => Value::Float(*f),
        Node::Simple(simple::FALSE) => Value::Bool(false),
        Node::Simple(simple::TRUE) => Value::Bool(true),
        Node::Simple(simple::NULL) => Value::Null,
        Node::Simple(s) => return Err(Error::Unsupported(format!("simple({s}) in unpacked data"))),
        Node::Tag(t, inner) => Value::Tag(*t, Box::new(node_to_value(inner)?)),
        Node::Array(a) => Value::Array(a.iter().map(node_to_value).collect::<Result<_>>()?),
        Node::Map(m) => Value::Map(
            m.iter().map(|(k, v)| Ok((node_to_value(k)?, node_to_value(v)?))).collect::<Result<_>>()?,
        ),
    })
}

fn head_len(n: u64) -> usize {
    match n {
        0..=23 => 1,
        24..=0xff => 2,
        0x100..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

// ------------------------------------------------------- dictionary ---

/// The file-wide packing tables (draft section 2.1).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Dictionary {
    /// Whole-item sharing. Slots 0..15 cost 1 byte per use, 16..63 cost 2, ...
    pub shared: Vec<Value>,
    /// Prefix/suffix sharing. Slots 0..7 cost 2 bytes per use, 8..31 cost 3, ...
    pub args: Vec<Value>,
}

impl Dictionary {
    fn extend(&mut self, shared: Vec<Value>, args: Vec<Value>) {
        self.shared.extend(shared);
        self.args.extend(args);
    }

    fn shared_item(&self, idx: usize) -> Result<Value> {
        self.shared.get(idx).cloned().ok_or(Error::UnknownShared(idx))
    }

    fn arg_item(&self, idx: usize) -> Result<Value> {
        self.args.get(idx).cloned().ok_or(Error::UnknownArgument(idx))
    }

    /// Reconstruct the original item (draft sections 2.2-2.4).
    fn unpack(&self, node: Node) -> Result<Value> {
        match node {
            Node::Simple(i) if i < 16 => self.shared_item(i as usize),
            Node::Tag(TAG_REF, inner) => match *inner {
                Node::Int(n) => {
                    let n: i128 = n.into();
                    let idx = if n >= 0 { 16 + 2 * n } else { 16 - 2 * n - 1 };
                    self.shared_item(usize::try_from(idx).map_err(|_| Error::BadReference("index"))?)
                }
                Node::Array(mut a) if a.len() == 2 => {
                    let rump = a.pop().unwrap();
                    let Node::Int(n) = a.pop().unwrap() else {
                        return Err(Error::BadReference("tag 6 array must start with an integer"));
                    };
                    let n: i128 = n.into();
                    if n >= 0 {
                        self.argument_ref(usize::try_from(8 + n).map_err(|_| Error::BadReference("index"))?, rump, true)
                    } else {
                        self.argument_ref(usize::try_from(8 - n - 1).map_err(|_| Error::BadReference("index"))?, rump, false)
                    }
                }
                _ => Err(Error::BadReference("tag 6 content must be an integer or [integer, rump]")),
            },
            Node::Tag(t, rump) if TAG_STRAIGHT.contains(&t) => self.argument_ref((t - 128) as usize, *rump, true),
            Node::Tag(t, rump) if TAG_INVERTED.contains(&t) => self.argument_ref((t - 136) as usize, *rump, false),
            Node::Tag(t, inner) => Ok(Value::Tag(t, Box::new(self.unpack(*inner)?))),
            Node::Array(a) => Ok(Value::Array(a.into_iter().map(|n| self.unpack(n)).collect::<Result<_>>()?)),
            Node::Map(m) => Ok(Value::Map(
                m.into_iter().map(|(k, v)| Ok((self.unpack(k)?, self.unpack(v)?))).collect::<Result<_>>()?,
            )),
            other => node_to_value(&other),
        }
    }

    fn argument_ref(&self, idx: usize, rump: Node, straight: bool) -> Result<Value> {
        let arg = self.arg_item(idx)?;
        let rump = self.unpack(rump)?;
        if straight { concat(arg, rump, false) } else { concat(rump, arg, true) }
    }
}

/// Concatenation function, draft section 2.4 (minus the `undefined` rule).
fn concat(lhs: Value, rhs: Value, rump_is_lhs: bool) -> Result<Value> {
    if let Value::Tag(t, _) = &lhs {
        return Err(Error::Unsupported(format!("function tag {t}")));
    }
    match (lhs, rhs) {
        (Value::Array(mut a), Value::Array(b)) => {
            a.extend(b);
            Ok(Value::Array(a))
        }
        (Value::Map(mut a), Value::Map(b)) => {
            for (k, v) in b {
                match a.iter_mut().find(|(k2, _)| *k2 == k) {
                    Some(slot) => slot.1 = v,
                    None => a.push((k, v)),
                }
            }
            Ok(Value::Map(a))
        }
        (l @ (Value::Text(_) | Value::Bytes(_)), r @ (Value::Text(_) | Value::Bytes(_))) => {
            let result_is_text = matches!(if rump_is_lhs { &l } else { &r }, Value::Text(_));
            let mut bytes = match l { Value::Text(s) => s.into_bytes(), Value::Bytes(b) => b, _ => unreachable!() };
            bytes.extend(match r { Value::Text(s) => s.into_bytes(), Value::Bytes(b) => b, _ => unreachable!() });
            if result_is_text {
                String::from_utf8(bytes).map(Value::Text).map_err(|_| Error::BadConcat)
            } else {
                Ok(Value::Bytes(bytes))
            }
        }
        _ => Err(Error::BadConcat),
    }
}

// ------------------------------------------------------------ packer ---

fn shared_ref_node(idx: usize) -> Node {
    if idx < 16 {
        Node::Simple(idx as u8)
    } else {
        let k = (idx - 16) as i128;
        let n = if k % 2 == 0 { k / 2 } else { -((k + 1) / 2) };
        Node::Tag(TAG_REF, Box::new(Node::Int(Integer::try_from(n).unwrap())))
    }
}

fn shared_ref_len(idx: usize) -> usize {
    if idx < 16 {
        1
    } else {
        let k = idx - 16;
        1 + head_len(if k % 2 == 0 { k / 2 } else { (k - 1) / 2 } as u64)
    }
}

fn straight_ref_node(idx: usize, rump: Node) -> Node {
    if idx < 8 {
        Node::Tag(128 + idx as u64, Box::new(rump))
    } else {
        let n = Node::Int(Integer::from((idx - 8) as u64));
        Node::Tag(TAG_REF, Box::new(Node::Array(vec![n, rump])))
    }
}

fn arg_ref_overhead(idx: usize) -> usize {
    if idx < 8 { 2 } else { 2 + head_len((idx - 8) as u64) }
}

/// Packs `Value`s against a [`Dictionary`]. Only rewrites when it saves bytes.
struct Packer {
    dict: Dictionary,
    text_idx: HashMap<String, usize>,
}

impl Packer {
    fn new(dict: Dictionary) -> Self {
        let mut p = Packer { dict: Dictionary::default(), text_idx: HashMap::new() };
        p.extend(dict.shared, dict.args);
        p
    }

    fn dictionary(&self) -> &Dictionary {
        &self.dict
    }

    fn extend(&mut self, shared: Vec<Value>, args: Vec<Value>) {
        for v in shared {
            let idx = self.dict.shared.len();
            if let Value::Text(s) = &v {
                self.text_idx.entry(s.clone()).or_insert(idx);
            }
            self.dict.shared.push(v);
        }
        self.dict.args.extend(args);
    }

    fn find_shared(&self, v: &Value) -> Option<usize> {
        match v {
            Value::Text(s) => self.text_idx.get(s).copied(),
            _ => self.dict.shared.iter().position(|x| x == v),
        }
    }

    fn pack(&self, v: &Value) -> Result<Node> {
        if let Some(idx) = self.find_shared(v) {
            if encode_node(&value_to_node(v))?.len() > shared_ref_len(idx) {
                return Ok(shared_ref_node(idx));
            }
        }
        Ok(match v {
            Value::Text(s) => self.pack_text(s),
            Value::Array(a) => Node::Array(a.iter().map(|x| self.pack(x)).collect::<Result<_>>()?),
            Value::Map(m) => Node::Map(
                m.iter().map(|(k, v)| Ok((self.pack(k)?, self.pack(v)?))).collect::<Result<_>>()?,
            ),
            Value::Tag(t, _) if *t == TAG_REF || *t == TAG_TABLE || TAG_STRAIGHT.contains(t) || TAG_INVERTED.contains(t) => {
                return Err(Error::Unsupported(format!(
                    "tag {t} in application data would be mistaken for a packed reference"
                )));
            }
            Value::Tag(t, inner) => Node::Tag(*t, Box::new(self.pack(inner)?)),
            other => value_to_node(other),
        })
    }

    fn pack_text(&self, s: &str) -> Node {
        let mut best: Option<(usize, usize)> = None; // (arg index, prefix len)
        for (i, a) in self.dict.args.iter().enumerate() {
            if let Value::Text(p) = a {
                if !p.is_empty() && s.starts_with(p.as_str()) && p.len() > arg_ref_overhead(i)
                    && best.map_or(true, |(_, bl)| p.len() > bl)
                {
                    best = Some((i, p.len()));
                }
            }
        }
        match best {
            Some((i, plen)) => straight_ref_node(i, Node::Text(s[plen..].to_string())),
            None => Node::Text(s.to_string()),
        }
    }
}

// -------------------------------------------------- dictionary building ---

/// Heuristic helper: finds repeated text strings (map keys *and* values) worth
/// putting into the shared-item table, hottest first.
#[derive(Default)]
pub struct DictionaryBuilder {
    counts: HashMap<String, usize>,
}

impl DictionaryBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn observe(&mut self, v: &Value) {
        match v {
            Value::Text(s) => *self.counts.entry(s.clone()).or_default() += 1,
            Value::Array(a) => a.iter().for_each(|x| self.observe(x)),
            Value::Map(m) => m.iter().for_each(|(k, v)| {
                self.observe(k);
                self.observe(v);
            }),
            Value::Tag(_, inner) => self.observe(inner),
            _ => {}
        }
    }

    /// Up to `max_items` new shared items, best byte savings first.
    /// Items already in `exclude.shared` are skipped, so this can be called
    /// repeatedly as the file grows to produce *extension* records.
    pub fn build(&self, max_items: usize, exclude: &Dictionary) -> Vec<Value> {
        let known: HashSet<&str> = exclude
            .shared
            .iter()
            .filter_map(|v| if let Value::Text(s) = v { Some(s.as_str()) } else { None })
            .collect();
        let mut c: Vec<(&String, usize)> = self
            .counts
            .iter()
            .filter(|(s, n)| **n >= 2 && !s.is_empty() && !known.contains(s.as_str()))
            .map(|(s, n)| (s, n * (head_len(s.len() as u64) + s.len() - 1)))
            .collect();
        c.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
        c.into_iter().take(max_items).map(|(s, _)| Value::Text(s.clone())).collect()
    }
}

// ------------------------------------------------------------ writer ---

fn dictionary_record(shared: &[Value], args: &[Value]) -> Node {
    Node::Tag(
        TAG_TABLE,
        Box::new(Node::Array(vec![
            Node::Array(shared.iter().map(value_to_node).collect()),
            Node::Array(args.iter().map(value_to_node).collect()),
            Node::Simple(simple::UNDEFINED),
        ])),
    )
}

/// `None` if `node` is an ordinary entry; `Some(..)` if it is a dictionary record.
fn parse_dictionary_record(node: &Node) -> Option<Result<(Vec<Value>, Vec<Value>)>> {
    let Node::Tag(TAG_TABLE, inner) = node else { return None };
    let Node::Array(v) = &**inner else { return None };
    if v.len() != 3 || v[2] != Node::Simple(simple::UNDEFINED) {
        return None;
    }
    let items = |n: &Node| match n {
        Node::Array(a) => a.iter().map(node_to_value).collect::<Result<Vec<_>>>(),
        _ => Err(Error::BadReference("dictionary record tables must be arrays")),
    };
    Some(items(&v[0]).and_then(|s| Ok((s, items(&v[1])?))))
}

pub struct PackedSeqWriter<W: Write> {
    out: W,
    packer: Packer,
}

impl<W: Write> PackedSeqWriter<W> {
    /// Start a new sequence with empty tables.
    pub fn new(out: W) -> Self {
        Self::with_dictionary(out, Dictionary::default())
    }

    /// Continue an existing sequence whose tables are already `dict`
    /// (see [`scan`]). Writes nothing.
    pub fn with_dictionary(out: W, dict: Dictionary) -> Self {
        Self { out, packer: Packer::new(dict) }
    }

    pub fn dictionary(&self) -> &Dictionary {
        self.packer.dictionary()
    }

    /// Append items to the tables, durably recording them in the file first.
    /// Existing indices are unaffected.
    pub fn extend_dictionary(&mut self, shared: Vec<Value>, args: Vec<Value>) -> Result<()> {
        let buf = encode_node(&dictionary_record(&shared, &args))?;
        self.out.write_all(&buf)?;
        self.packer.extend(shared, args);
        Ok(())
    }

    /// Pack and append one entry. Each entry is written with one `write_all`,
    /// so a crash leaves at worst one torn item at the end (repaired by
    /// [`open_append`]).
    pub fn append(&mut self, entry: &Value) -> Result<()> {
        let buf = encode_node(&self.packer.pack(entry)?)?;
        self.out.write_all(&buf)?;
        Ok(())
    }

    pub fn append_serialize<T: serde::Serialize>(&mut self, entry: &T) -> Result<()> {
        let v = Value::serialized(entry).map_err(|e| Error::Serde(e.to_string()))?;
        self.append(&v)
    }

    pub fn flush(&mut self) -> Result<()> {
        Ok(self.out.flush()?)
    }

    pub fn into_inner(self) -> W {
        self.out
    }
}

// ------------------------------------------------------------ reader ---

pub struct PackedSeqReader<R: Read> {
    inner: BufReader<R>,
    dict: Dictionary,
    offset: u64,
    done: bool,
}

impl<R: Read> PackedSeqReader<R> {
    pub fn new(r: R) -> Self {
        Self { inner: BufReader::new(r), dict: Dictionary::default(), offset: 0, done: false }
    }

    pub fn dictionary(&self) -> &Dictionary {
        &self.dict
    }

    /// Bytes of fully read items so far.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    fn next_node(&mut self) -> Result<Option<Node>> {
        if self.inner.fill_buf()?.is_empty() {
            return Ok(None); // clean EOF at an item boundary
        }
        let mut dec = Decoder::from(&mut self.inner);
        let node = read_node(&mut dec, 0)?;
        self.offset += dec.offset() as u64;
        Ok(Some(node))
    }

    /// Next unpacked entry; dictionary records are consumed transparently.
    pub fn next_entry(&mut self) -> Result<Option<Value>> {
        while let Some(node) = self.next_node()? {
            match parse_dictionary_record(&node) {
                Some(rec) => {
                    let (s, a) = rec?;
                    self.dict.extend(s, a);
                }
                None => return Ok(Some(self.dict.unpack(node)?)),
            }
        }
        Ok(None)
    }

    pub fn next_as<T: serde::de::DeserializeOwned>(&mut self) -> Result<Option<T>> {
        match self.next_entry()? {
            Some(v) => Ok(Some(v.deserialized().map_err(|e| Error::Serde(e.to_string()))?)),
            None => Ok(None),
        }
    }
}

impl<R: Read> Iterator for PackedSeqReader<R> {
    type Item = Result<Value>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        match self.next_entry() {
            Ok(Some(v)) => Some(Ok(v)),
            Ok(None) => None,
            Err(e) => {
                self.done = true;
                Some(Err(e))
            }
        }
    }
}

/// Read a whole sequence just to recover its tables and the length of its
/// valid prefix. A torn final item is tolerated (and excluded from the length);
/// any other corruption is an error. Cost is one pass over the file.
pub fn scan<R: Read>(r: R) -> Result<(Dictionary, u64)> {
    let mut rd = PackedSeqReader::new(r);
    loop {
        match rd.next_node() {
            Ok(None) | Err(Error::Truncated) => break,
            Ok(Some(n)) => {
                if let Some(rec) = parse_dictionary_record(&n) {
                    let (s, a) = rec?;
                    rd.dict.extend(s, a);
                }
            }
            Err(e) => return Err(e),
        }
    }
    Ok((rd.dict, rd.offset))
}

/// Open (or create) a sequence file for appending: recovers the tables, cuts
/// off a torn trailing item if there is one, and positions at the end.
/// Single-writer only; take a file lock if several processes may append.
pub fn open_append(path: impl AsRef<Path>) -> Result<PackedSeqWriter<File>> {
    let mut f = OpenOptions::new().read(true).write(true).create(true).open(path)?;
    let (dict, valid) = scan(&f)?;
    f.set_len(valid)?;
    f.seek(SeekFrom::Start(valid))?;
    Ok(PackedSeqWriter::with_dictionary(f, dict))
}

pub fn open_read(path: impl AsRef<Path>) -> Result<PackedSeqReader<File>> {
    Ok(PackedSeqReader::new(File::open(path)?))
}

// ------------------------------------------------------------- tests ---

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    fn t(s: &str) -> Value { Value::Text(s.into()) }
    fn tmp(name: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("packed_seq_{}_{name}", std::process::id()));
        let _ = std::fs::remove_file(&p);
        p
    }

    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    struct Event { ts: u64, level: String, source: String, url: String, msg: String }

    fn event(i: u64) -> Event {
        Event {
            ts: 1_700_000_000 + i,
            level: ["INFO", "WARN", "ERROR"][(i % 3) as usize].into(),
            source: "sensor-gateway".into(),
            url: format!("https://telemetry.example.com/api/v2/devices/{}/readings", i % 7),
            msg: format!("reading {i} accepted"),
        }
    }

    #[test]
    fn draft_examples_unpack() {
        // Section 2.3 of the draft: args ["foobar", h'666f6f62', "fo"].
        let d = Dictionary { shared: vec![], args: vec![t("foobar"), Value::Bytes(b"foob".to_vec()), t("fo")] };
        for (tag, rump) in [(128, "t"), (129, "art"), (130, "obart")] {
            let n = Node::Tag(tag, Box::new(Node::Text(rump.into())));
            assert_eq!(d.unpack(n).unwrap(), t("foobart"));
        }
        // Inverted reference: rump is the left-hand side.
        let d = Dictionary { shared: vec![], args: vec![t("/foo.html")] };
        assert_eq!(d.unpack(Node::Tag(136, Box::new(Node::Text("https://x".into())))).unwrap(), t("https://x/foo.html"));
        // tag 6([N, rump]): straight N>=0 -> 8+N ; inverted N<0 -> 8-N-1.
        let mut args: Vec<Value> = (0..8).map(|_| t("-")).collect();
        args.push(t("A"));      // index 8  <-> 6([0, rump])
        args.push(t("B"));      // index 9  <-> 6([1, rump]) ; inverted: 8-N-1=9 -> N=-2
        let d = Dictionary { shared: vec![], args };
        let arr = |n: i64, r: &str| Node::Tag(6, Box::new(Node::Array(vec![Node::Int(Integer::try_from(n).unwrap()), Node::Text(r.into())])));
        assert_eq!(d.unpack(arr(0, "x")).unwrap(), t("Ax"));
        assert_eq!(d.unpack(arr(1, "x")).unwrap(), t("Bx"));
        assert_eq!(d.unpack(arr(-2, "x")).unwrap(), t("xB"));
    }

    #[test]
    fn shared_index_numbering_matches_table_1() {
        // idx 16..21 <-> 6(0), 6(-1), 6(1), 6(-2), 6(2), 6(-3)
        let expect = [0i64, -1, 1, -2, 2, -3];
        for (k, n) in expect.iter().enumerate() {
            let want = Node::Tag(6, Box::new(Node::Int(Integer::try_from(*n).unwrap())));
            assert_eq!(shared_ref_node(16 + k), want);
            let d = Dictionary { shared: (0..30).map(|i| Value::from(i as i64)).collect(), args: vec![] };
            assert_eq!(d.unpack(want).unwrap(), Value::from((16 + k) as i64));
        }
        assert_eq!(shared_ref_node(15), Node::Simple(15));
    }

    #[test]
    fn roundtrip_compresses_and_appends() {
        let path = tmp("log.cborseq");
        let events: Vec<Event> = (0..300).map(event).collect();

        // Baseline: the same data as a plain, unpacked CBOR sequence.
        let mut plain = Vec::new();
        for e in &events { ciborium::into_writer(e, &mut plain).unwrap(); }

        // Learn a dictionary from the first 50 entries.
        let mut b = DictionaryBuilder::new();
        for e in &events[..50] { b.observe(&Value::serialized(e).unwrap()); }
        let mut w = open_append(&path).unwrap();
        let shared = b.build(16, w.dictionary());
        assert!(shared.contains(&t("sensor-gateway")) && shared.contains(&t("level")));
        w.extend_dictionary(shared, vec![t("https://telemetry.example.com/api/v2/devices/")]).unwrap();
        for e in &events[..100] { w.append_serialize(e).unwrap(); }
        drop(w);

        // Reopen (tables recovered from the file) and keep appending.
        let before = std::fs::metadata(&path).unwrap().len();
        let mut w = open_append(&path).unwrap();
        for e in &events[100..] { w.append_serialize(e).unwrap(); }
        drop(w);
        let after = std::fs::metadata(&path).unwrap().len();
        assert!(after > before);

        // Everything reads back identically.
        let mut r = open_read(&path).unwrap();
        let mut got = Vec::new();
        while let Some(e) = r.next_as::<Event>().unwrap() { got.push(e); }
        assert_eq!(got, events);
        println!("plain: {} bytes, packed: {after} bytes ({:.0}%)", plain.len(), 100.0 * after as f64 / plain.len() as f64);
        assert!(after < plain.len() as u64 * 7 / 10);
    }

    #[test]
    fn dictionary_can_grow_without_breaking_old_entries() {
        let path = tmp("grow.cborseq");
        let mut w = open_append(&path).unwrap();
        w.extend_dictionary(vec![t("a")], vec![]).unwrap();
        w.append(&Value::Array(vec![t("a"), t("a"), t("a")])).unwrap();
        w.extend_dictionary(vec![t("a-much-longer-string")], vec![]).unwrap(); // index 1
        w.append(&Value::Array(vec![t("a-much-longer-string"), t("a")])).unwrap();
        drop(w);
        let all: Vec<Value> = open_read(&path).unwrap().collect::<Result<_>>().unwrap();
        assert_eq!(all[0], Value::Array(vec![t("a"), t("a"), t("a")]));
        assert_eq!(all[1], Value::Array(vec![t("a-much-longer-string"), t("a")]));
    }

    #[test]
    fn torn_tail_is_repaired_on_reopen() {
        let path = tmp("torn.cborseq");
        let mut w = open_append(&path).unwrap();
        w.extend_dictionary(vec![t("key")], vec![]).unwrap();
        w.append(&Value::Map(vec![(t("key"), Value::from(1))])).unwrap();
        let mut f = w.into_inner();
        f.write_all(&[0xa2, 0x00, 0x18]).unwrap(); // half-written map
        drop(f);
        assert!(matches!(open_read(&path).unwrap().nth(1), Some(Err(Error::Truncated))));
        let mut w = open_append(&path).unwrap();
        w.append(&Value::Map(vec![(t("key"), Value::from(2))])).unwrap();
        drop(w);
        let all: Vec<Value> = open_read(&path).unwrap().collect::<Result<_>>().unwrap();
        assert_eq!(all, vec![
            Value::Map(vec![(t("key"), Value::from(1))]),
            Value::Map(vec![(t("key"), Value::from(2))]),
        ]);
    }

    #[test]
    fn rejects_ambiguous_application_tags_and_bad_refs() {
        let mut w = PackedSeqWriter::new(Vec::new());
        assert!(matches!(w.append(&Value::Tag(130, Box::new(t("x")))), Err(Error::Unsupported(_))));
        let d = Dictionary::default();
        assert!(matches!(d.unpack(Node::Simple(3)), Err(Error::UnknownShared(3))));
        assert!(matches!(d.unpack(Node::Tag(128, Box::new(Node::Text("x".into())))), Err(Error::UnknownArgument(0))));
    }

    #[test]
    fn generic_ciborium_cannot_read_packed_entries_without_unpacking() {
        // Documented limitation: simple(0..15) is outside what ciborium::Value models.
        let mut w = PackedSeqWriter::new(Vec::new());
        w.extend_dictionary(vec![t("some shared string")], vec![]).unwrap();
        w.append(&t("some shared string")).unwrap();
        let bytes = w.into_inner();
        let mut cur = std::io::Cursor::new(&bytes[..]);
        let first: std::result::Result<Value, _> = ciborium::from_reader(&mut cur); // the 1113 record: fine
        assert!(first.is_ok());
        let second: std::result::Result<Value, _> = ciborium::from_reader(&mut cur); // simple(0)
        println!("generic decode of simple(0): {second:?}");
        assert!(second.is_err());
    }
}
