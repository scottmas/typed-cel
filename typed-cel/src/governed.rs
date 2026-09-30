//! Governed values: the demanded paths of a document that is still arriving.
//!
//! A program reads a handful of fields of a document streamed as [`Event`]s. The document is never
//! held. Instead:
//!
//! - [`GovernedShape`] is built ONCE per program: the demanded paths under one root, laid over the
//!   root's declared [`CelTy`], as a small trie of `Send + Sync` nodes. Every refusal happens here.
//! - [`GovernedDoc`] is built per document from an `Arc<GovernedShape>`. It is fed events in
//!   document order and settles one cell per trie node. Its root is a [`LazyValue`] whose reads
//!   answer `Pending` until the cell they name has settled.
//! - [`StreamedProgram`] is a body check built once: the shape, the emitted code and the bound
//!   roots. [`StreamedProgram::begin`] makes a [`StreamedRun`] per body, which feeds each event to
//!   the document and resumes the paused run (on the fast backend) only when a cell settled.
//!
//! Validating the WHOLE document — every field the program never reads — is not this module's: a
//! caller that holds a schema runs its validator beside the run, on the same events, and combines
//! the two answers. Producing the events (tokenizing the bytes) is the caller's job too.
//!
//! A [`StreamedRun`] OWNS its document: it feeds it through `&mut` and the paused run reads it by
//! field through [`Facts`] — no `Arc`, no lock, on a path taken once per token. The `Mutex` in
//! [`GovernedDoc`] exists only because that value is SHARED, as a `LazyValue` an evaluator binds;
//! both read the one `DocState`, so the two cannot answer differently.
//!
//! A cell settles ONCE, to what schema-directed binding (`CelActivation::bind`) of the whole
//! document followed by a read would give — the value, or the same error text. Settled cells never
//! change: the first occurrence of a duplicate key stands, and a string settles at its end, never
//! from a prefix.
//!
//! Memory is bounded by the SHAPE and one cap, never by the document: an undemanded member is
//! skipped holding only a depth counter, a key is buffered only up to the longest key the open
//! object must recognise, and the text of demanded strings is capped at
//! [`GOVERNED_CELL_BYTES`] across all cells at once. Past a cap the document reports
//! [`GovernedDoc::capped`] and the cell stays pending — never a truncated value.

use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use crate::demand::{DemandSet, Segment};
use crate::event::Event;
use crate::fast::{FactPoll, Facts, FieldId, Paused, Resumed};
use crate::lazy::{Access, DemandHandle, LazyValue, Presence};
use crate::ty::CelTy;
use crate::CelValue;
use crate::{
    CelActivation, CelBindings, CelBytecode, CelEnvironment, CelError, CelProgram, CelTemplate,
    FastProgram, Vm,
};

/// The settled and accumulating text a document holds at once, across every cell.
pub const GOVERNED_CELL_BYTES: usize = 64 * 1024;

/// What [`GovernedDoc::capped`] names when the text of demanded strings passes the cell cap.
const CAP_CELL_BYTES: &str = "cel.governed_cell_bytes";
/// What [`GovernedDoc::capped`] names when a demanded number's token was too long to be given.
const CAP_NUMBER_TOO_LONG: &str = "cel.number_too_long";

type NodeId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Leaf {
    Bool,
    Num,
    Str,
    Duration,
}

/// A key a container node recognises: a declared field of a record, or a demanded literal key.
#[derive(Debug)]
struct Slot {
    key: String,
    /// The demanded child; `None` for a declared field no path reads (its presence is still
    /// tracked, because `has()` demand names only the operand).
    child: Option<NodeId>,
    /// A declared, non-optional field: absent at the close is the bind error, not `NoSuchMember`.
    required: bool,
}

#[derive(Debug)]
enum Kind {
    Leaf(Leaf),
    /// A record or a string-keyed map. A record's slots are its declared fields, in declaration
    /// order, then any demanded keys its index signature covers; a map's slots are its demanded
    /// keys.
    Container {
        slots: Vec<Slot>,
        /// Accepts keys it does not declare: a map, or a record with an index signature.
        open: bool,
    },
}

#[derive(Debug)]
struct Node {
    /// `body.project.owner` — the path binding would name in its errors.
    path: String,
    /// `ty.name()` of the declared type, for the mismatch text.
    ty_name: String,
    kind: Kind,
}

impl Node {
    fn slots(&self) -> &[Slot] {
        match &self.kind {
            Kind::Container { slots, .. } => slots,
            Kind::Leaf(_) => &[],
        }
    }

    fn slot(&self, key: &str) -> Option<usize> {
        self.slots().iter().position(|s| s.key == key)
    }

    fn open(&self) -> bool {
        matches!(self.kind, Kind::Container { open: true, .. })
    }
}

/// The demanded paths under one root, over that root's declared type. Built once; `Send + Sync`.
#[derive(Debug)]
pub struct GovernedShape {
    root: String,
    /// `nodes[0]` is the root.
    nodes: Vec<Node>,
    cell_cap: usize,
    /// Per node: the longest key it must recognise. A key longer than this matches nothing.
    longest_key: Vec<usize>,
    /// The deepest chain of containers, so a document's frame stack never grows past it.
    depth: usize,
}

fn refuse(path: &str, why: String) -> CelError {
    CelError::Bind {
        message: format!("`{path}`: {why}"),
    }
}

/// A node for `ty` at `path`, or the refusal for a type a streamed value cannot settle.
fn node_for(path: String, ty: &CelTy) -> Result<Node, CelError> {
    let kind = match ty {
        CelTy::Bool => Kind::Leaf(Leaf::Bool),
        CelTy::Num => Kind::Leaf(Leaf::Num),
        CelTy::Str => Kind::Leaf(Leaf::Str),
        CelTy::Duration => Kind::Leaf(Leaf::Duration),
        CelTy::Record(r) => Kind::Container {
            slots: r
                .fields
                .iter()
                .map(|(name, _)| Slot {
                    key: name.clone(),
                    child: None,
                    required: !r.is_optional(name),
                })
                .collect(),
            open: r.index.is_some(),
        },
        CelTy::Map(k, _) if **k == CelTy::Str => Kind::Container {
            slots: Vec::new(),
            open: true,
        },
        // A list is only ever read whole — iterated, sized, compared — and holding one would hold
        // a subtree the document chooses the size of.
        CelTy::List(_) => {
            return Err(refuse(
                &path,
                format!(
                    "a streamed value settles named paths only, and {} is read whole",
                    ty.name()
                ),
            ))
        }
        other => {
            return Err(refuse(
                &path,
                format!(
                    "a streamed value cannot settle {}; it settles bool, double, string and \
                     duration values under records and string-keyed maps",
                    other.name()
                ),
            ))
        }
    };
    Ok(Node {
        path,
        ty_name: ty.name(),
        kind,
    })
}

/// The declared type of `key` under a container of type `ty`.
fn child_ty(ty: &CelTy, key: &str) -> Option<CelTy> {
    match ty {
        CelTy::Record(r) => r.field_or_index(key).cloned(),
        CelTy::Map(_, v) => Some((**v).clone()),
        _ => None,
    }
}

fn render(path: &[Segment]) -> String {
    path.iter()
        .map(|s| match s {
            Segment::Root(r) | Segment::Key(r) => r.as_str(),
            Segment::Wild => "*",
        })
        .collect::<Vec<_>>()
        .join(".")
}

impl GovernedShape {
    /// Refuses (`CelError::Bind`) a wide root, a `Wild` segment under `root`, and any path through
    /// a type a streamed value cannot settle. Paths under other roots are ignored.
    pub fn build(root: &str, ty: &CelTy, demand: &DemandSet) -> Result<GovernedShape, CelError> {
        let ours: Vec<&[Segment]> = demand
            .paths()
            .filter(|p| matches!(p.first(), Some(Segment::Root(r)) if r == root))
            .collect();
        const NAMED_ONLY: &str = "a streamed value settles named paths only; a whole-container \
                                  iteration would need the whole subtree held";
        for p in &ours {
            if let Some(wild) = p.iter().position(|s| *s == Segment::Wild) {
                return Err(refuse(&render(&p[..wild]), NAMED_ONLY.to_string()));
            }
        }
        if demand.wide_roots().any(|r| r == root) {
            return Err(refuse(root, NAMED_ONLY.to_string()));
        }

        let root_node = node_for(root.to_string(), ty)?;
        if matches!(root_node.kind, Kind::Leaf(_)) {
            return Err(refuse(
                root,
                format!(
                    "a streamed root must be a record or a string-keyed map, not {}",
                    ty.name()
                ),
            ));
        }
        // The declared types, kept only while building: `CelTy` holds `Rc`, and the shape is
        // shared across threads.
        let mut tys: Vec<CelTy> = vec![ty.clone()];
        let mut nodes: Vec<Node> = vec![root_node];
        for p in ours {
            let mut cur: usize = 0;
            for seg in &p[1..] {
                let Segment::Key(key) = seg else {
                    return Err(refuse(&render(p), format!("unexpected segment {seg}")));
                };
                if matches!(nodes[cur].kind, Kind::Leaf(_)) {
                    return Err(refuse(
                        &nodes[cur].path,
                        format!(
                            "cannot read `{key}` on a value of type {}",
                            nodes[cur].ty_name
                        ),
                    ));
                }
                let existing = nodes[cur].slot(key);
                if let Some(c) = existing.and_then(|i| nodes[cur].slots()[i].child) {
                    cur = c as usize;
                    continue;
                }
                let path = format!("{}.{key}", nodes[cur].path);
                let Some(cty) = child_ty(&tys[cur], key) else {
                    return Err(refuse(
                        &path,
                        format!("`{key}` is not declared on {}", nodes[cur].ty_name),
                    ));
                };
                let node = node_for(path, &cty)?;
                let id = nodes.len() as NodeId;
                nodes.push(node);
                tys.push(cty);
                let Kind::Container { slots, .. } = &mut nodes[cur].kind else {
                    unreachable!("checked above: a leaf has no children");
                };
                match existing {
                    Some(i) => slots[i].child = Some(id),
                    None => slots.push(Slot {
                        key: key.clone(),
                        child: Some(id),
                        required: false,
                    }),
                }
                cur = id as usize;
            }
        }
        drop(tys);

        let longest_key = nodes
            .iter()
            .map(|n| n.slots().iter().map(|s| s.key.len()).max().unwrap_or(0))
            .collect();
        let depth = container_depth(&nodes, 0);
        Ok(GovernedShape {
            root: root.to_string(),
            nodes,
            cell_cap: GOVERNED_CELL_BYTES,
            longest_key,
            depth,
        })
    }

    /// The text cap, in bytes, across every cell of one document. [`GOVERNED_CELL_BYTES`] unless
    /// set here.
    pub fn with_cell_cap(mut self, bytes: usize) -> GovernedShape {
        self.cell_cap = bytes;
        self
    }

    /// The root this shape governs.
    pub fn root(&self) -> &str {
        &self.root
    }

    /// Does reading the VALUE at `names` below the root land on a record or map node — a read of
    /// a whole container, which a document read by field cannot answer? A path that leaves the
    /// shape is not one: its read fails as the evaluator's does.
    fn reads_container(&self, names: &[String]) -> bool {
        let mut node = 0usize;
        for name in names {
            let n = &self.nodes[node];
            match n.slot(name).and_then(|i| n.slots()[i].child) {
                Some(c) => node = c as usize,
                None => return false,
            }
        }
        matches!(self.nodes[node].kind, Kind::Container { .. })
    }

    /// Every node's path, root first. Diagnostics: what a document of this shape settles.
    pub fn paths(&self) -> impl Iterator<Item = &str> {
        self.nodes.iter().map(|n| n.path.as_str())
    }
}

/// How many containers deep the trie goes under `n`, counting `n`.
fn container_depth(nodes: &[Node], n: usize) -> usize {
    match &nodes[n].kind {
        Kind::Leaf(_) => 0,
        Kind::Container { slots, .. } => {
            1 + slots
                .iter()
                .filter_map(|s| s.child)
                .map(|c| container_depth(nodes, c as usize))
                .max()
                .unwrap_or(0)
        }
    }
}

/// One document's governed value. Cheap to clone (an `Arc`); the clones share one state.
#[derive(Clone, Debug)]
pub struct GovernedDoc {
    inner: Arc<DocInner>,
}

#[derive(Debug)]
struct DocInner {
    shape: Arc<GovernedShape>,
    /// Uncontended by construction — one document is fed by one thread at a time — and here
    /// because a `LazyValue` is `Sync`. Never held across a call back into an evaluator: a read
    /// locks, copies out, unlocks.
    state: Mutex<DocState>,
}

#[derive(Debug)]
struct DocState {
    /// One per node.
    cells: Vec<Cell>,
    /// Per node, per slot: was the key seen in this document's (first) object for that node.
    seen: Vec<Vec<bool>>,
    /// Per node: has its object closed (so an unseen slot is absent).
    closed: Vec<bool>,
    /// One per OPEN tracked object, innermost last.
    frames: Vec<NodeId>,
    /// The key being read, bounded by the open object's longest key.
    key: String,
    /// The key being read is longer than any the open object recognises.
    key_over: bool,
    /// Depth inside an untracked container.
    skip: usize,
    /// Inside an untracked string (strings do not nest, so one bit).
    skip_string: bool,
    /// The next value is untracked.
    skip_next: bool,
    /// The tracked node whose value is next.
    pending_value: Option<NodeId>,
    /// The string leaf accumulating fragments.
    acc: Option<NodeId>,
    /// Bytes of settled and accumulating text, against the shape's cell cap.
    held: usize,
    /// Bumped on every settle and every presence decision.
    generation: u64,
    capped: Option<&'static str>,
    ended: bool,
}

#[derive(Debug)]
enum Cell {
    Unsettled,
    Accumulating(String),
    Value(CelValue),
    /// A record or map node whose object opened: read as a fresh view of it. A view is not stored,
    /// because it holds the document and a cell holding it would be a cycle.
    View,
    Absent,
    /// Rebuilt as `CelError::Bind { message }` on each read.
    Failed(String),
}

impl Cell {
    fn settled(&self) -> bool {
        !matches!(self, Cell::Unsettled | Cell::Accumulating(_))
    }
}

/// What a value-opening event is, in the words `bind` uses.
fn shape_of(e: &Event<'_>) -> &'static str {
    match e {
        Event::BeginObject => "an object",
        Event::BeginArray => "a list",
        Event::BeginString => "a string",
        Event::Number(_) | Event::NumberTooLong => "a number",
        Event::Bool(_) => "a bool",
        Event::Null => "null",
        // Not a value's first event; never reached for a well-nested producer.
        _ => "not a value",
    }
}

impl GovernedDoc {
    pub fn new(shape: Arc<GovernedShape>) -> GovernedDoc {
        let state = DocState::new(&shape);
        GovernedDoc {
            inner: Arc::new(DocInner {
                shape,
                state: Mutex::new(state),
            }),
        }
    }

    /// One event, in document order. After [`capped`](GovernedDoc::capped) or
    /// [`end`](GovernedDoc::end), a no-op.
    pub fn push(&self, e: Event<'_>) {
        self.inner.lock().feed(&self.inner.shape, e);
    }

    /// The producer stopped. Every unsettled cell settles failed; every presence question still
    /// open settles `false`. A no-op once capped: a capped cell stays pending.
    pub fn end(&self) {
        self.inner.lock().finish(&self.inner.shape);
    }

    /// Bumped on every settle and every presence decision; unchanged otherwise. A reader that saw
    /// `Pending` need not look again until this has moved.
    pub fn generation(&self) -> u64 {
        self.inner.lock().generation
    }

    /// The cap this document ran into, if any. Final.
    pub fn capped(&self) -> Option<&'static str> {
        self.inner.lock().capped
    }

    /// What this holds: cells, presence bits, frames, the key buffer, and accumulating + settled
    /// text. Bounded by the shape and the cell cap, never by the document.
    pub fn state_bytes(&self) -> usize {
        self.inner.lock().bytes()
    }

    /// The root's value, to bind with `bind_lazy` / `CelTemplate::instantiate`.
    pub fn value(&self) -> CelValue {
        CelValue::Lazy(Arc::new(View {
            doc: self.inner.clone(),
            node: 0,
        }))
    }
}

impl DocInner {
    fn lock(&self) -> MutexGuard<'_, DocState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// One document OWNED by the run that feeds it: fed through `&mut`, read through `&`. The same
/// [`DocState`] a [`GovernedDoc`] shares, without the sharing.
#[derive(Debug)]
struct Doc {
    shape: Arc<GovernedShape>,
    st: DocState,
}

impl Doc {
    fn new(shape: Arc<GovernedShape>) -> Doc {
        let st = DocState::new(&shape);
        Doc { shape, st }
    }

    fn push(&mut self, e: Event<'_>) {
        self.st.feed(&self.shape, e);
    }

    fn end(&mut self) {
        self.st.finish(&self.shape);
    }

    fn generation(&self) -> u64 {
        self.st.generation
    }

    fn capped(&self) -> Option<&'static str> {
        self.st.capped
    }

    fn state_bytes(&self) -> usize {
        self.st.bytes()
    }
}

/// What one member read of a view answers, before it becomes a value.
enum Got<'d> {
    Pending(DemandHandle),
    Value(&'d CelValue),
    /// A record or map node that opened: read as a view of it.
    View(NodeId),
}

impl DocState {
    fn new(shape: &GovernedShape) -> DocState {
        let n = shape.nodes.len();
        let longest = shape.longest_key.iter().copied().max().unwrap_or(0);
        DocState {
            cells: (0..n).map(|_| Cell::Unsettled).collect(),
            seen: shape
                .nodes
                .iter()
                .map(|node| vec![false; node.slots().len()])
                .collect(),
            closed: vec![false; n],
            frames: Vec::with_capacity(shape.depth),
            key: String::with_capacity(longest),
            key_over: false,
            skip: 0,
            skip_string: false,
            skip_next: false,
            pending_value: Some(0),
            acc: None,
            held: 0,
            generation: 0,
            capped: None,
            ended: false,
        }
    }

    /// One event, in document order; a no-op once capped or ended.
    fn feed(&mut self, shape: &GovernedShape, e: Event<'_>) {
        if self.capped.is_some() || self.ended {
            return;
        }
        self.push(shape, e);
    }

    /// The producer stopped: see [`GovernedDoc::end`].
    fn finish(&mut self, shape: &GovernedShape) {
        if self.capped.is_some() || self.ended {
            return;
        }
        self.ended = true;
        for (n, node) in shape.nodes.iter().enumerate() {
            if let Cell::Accumulating(s) = &self.cells[n] {
                self.held -= s.len();
            }
            if !self.cells[n].settled() {
                self.cells[n] = Cell::Failed(format!(
                    "`{p}`: the document ended before `{p}` was complete",
                    p = node.path
                ));
            }
            self.closed[n] = true;
        }
        self.frames.clear();
        self.acc = None;
        self.pending_value = None;
        self.generation += 1;
    }

    /// See [`GovernedDoc::state_bytes`].
    fn bytes(&self) -> usize {
        let text: usize = self
            .cells
            .iter()
            .map(|c| match c {
                Cell::Accumulating(s) => s.capacity(),
                Cell::Value(CelValue::Str(s)) => s.len(),
                Cell::Failed(m) => m.capacity(),
                _ => 0,
            })
            .sum();
        std::mem::size_of::<DocState>()
            + self.cells.capacity() * std::mem::size_of::<Cell>()
            + self.seen.iter().map(Vec::capacity).sum::<usize>()
            + self.closed.capacity()
            + self.frames.capacity() * std::mem::size_of::<NodeId>()
            + self.key.capacity()
            + text
    }

    /// Node `node`'s own cell, which must have opened as an object before anything under it can
    /// be read. `Ok(None)` means it has.
    fn own(&self, shape: &GovernedShape, node: NodeId) -> Result<Option<DemandHandle>, CelError> {
        match &self.cells[node as usize] {
            Cell::View => Ok(None),
            Cell::Failed(m) => Err(CelError::Bind { message: m.clone() }),
            Cell::Unsettled | Cell::Accumulating(_) => Ok(Some(DemandHandle::new(node))),
            // Not reachable: a view is handed out only for a node that opened.
            Cell::Value(_) | Cell::Absent => Err(CelError::Bind {
                message: format!(
                    "`{}` is not an object in this document",
                    shape.nodes[node as usize].path
                ),
            }),
        }
    }

    /// `name` read on the view of `node` — what `LazyValue::poll_member` answers.
    fn member(&self, shape: &GovernedShape, node: NodeId, name: &str) -> Result<Got<'_>, CelError> {
        let n = &shape.nodes[node as usize];
        if let Some(h) = self.own(shape, node)? {
            return Ok(Got::Pending(h));
        }
        let Some(i) = n.slot(name) else {
            return Err(if n.open() {
                undemanded(shape, node, name)
            } else {
                CelError::NoSuchMember {
                    key: name.to_string(),
                }
            });
        };
        let Some(c) = n.slots()[i].child else {
            return Err(undemanded(shape, node, name));
        };
        match &self.cells[c as usize] {
            Cell::Unsettled | Cell::Accumulating(_) => Ok(Got::Pending(DemandHandle::new(c))),
            Cell::Value(v) => Ok(Got::Value(v)),
            Cell::View => Ok(Got::View(c)),
            Cell::Absent => Err(CelError::NoSuchMember {
                key: name.to_string(),
            }),
            Cell::Failed(m) => Err(CelError::Bind { message: m.clone() }),
        }
    }

    /// `has(x.name)` on the view of `node` — what `LazyValue::poll_has` answers.
    fn presence(
        &self,
        shape: &GovernedShape,
        node: NodeId,
        name: &str,
    ) -> Result<Presence, CelError> {
        let n = &shape.nodes[node as usize];
        // A record that declares no such field and has no index signature: the checker refuses a
        // program that asks, so answer at once rather than pend.
        if n.slot(name).is_none() && !n.open() {
            return Ok(Presence::Known(false));
        }
        if let Some(h) = self.own(shape, node)? {
            return Ok(Presence::Pending(h));
        }
        match n.slot(name) {
            Some(i) if self.seen[node as usize][i] => Ok(Presence::Known(true)),
            Some(_) if self.closed[node as usize] => Ok(Presence::Known(false)),
            Some(i) => Ok(Presence::Pending(DemandHandle::new(
                n.slots()[i].child.unwrap_or(node),
            ))),
            // A key of a map (or an index-signature record) no path names. The checker records
            // the key of every presence question on an open container as demand (`has(x.k)`,
            // `"k" in x`), so a checked program never asks this; the answer is the same refusal
            // an undemanded read gets.
            None => Err(undemanded(shape, node, name)),
        }
    }

    fn settle(&mut self, n: NodeId, cell: Cell) {
        self.cells[n as usize] = cell;
        self.generation += 1;
    }

    /// `n` and every node under it fail with `message`: the value binding would reject.
    fn fail_subtree(&mut self, shape: &GovernedShape, n: NodeId, message: &str) {
        let mut stack = vec![n];
        while let Some(m) = stack.pop() {
            if !self.cells[m as usize].settled() {
                self.cells[m as usize] = Cell::Failed(message.to_string());
            }
            stack.extend(
                shape.nodes[m as usize]
                    .slots()
                    .iter()
                    .filter_map(|s| s.child),
            );
        }
        self.generation += 1;
    }

    /// Skip the value that opens with `e`.
    fn skip_value(&mut self, e: &Event<'_>) {
        match e {
            Event::BeginString => self.skip_string = true,
            Event::BeginObject | Event::BeginArray => self.skip = 1,
            _ => {}
        }
    }

    fn push(&mut self, shape: &GovernedShape, e: Event<'_>) {
        if self.skip_string {
            if e == Event::EndString {
                self.skip_string = false;
            }
            return;
        }
        if self.skip > 0 {
            match e {
                Event::BeginObject | Event::BeginArray => self.skip += 1,
                Event::EndObject | Event::EndArray => self.skip -= 1,
                _ => {}
            }
            return;
        }
        if let Some(n) = self.acc {
            self.accumulate(shape, n, e);
            return;
        }
        if let Some(n) = self.pending_value.take() {
            self.value_starts(shape, n, e);
            return;
        }
        if std::mem::take(&mut self.skip_next) {
            self.skip_value(&e);
            return;
        }
        let Some(&o) = self.frames.last() else {
            // Past the root value. A well-formed producer sends nothing more.
            return;
        };
        let node = &shape.nodes[o as usize];
        match e {
            Event::BeginKey => {
                self.key.clear();
                self.key_over = false;
            }
            Event::KeyText(t) => {
                if self.key_over || self.key.len() + t.len() > shape.longest_key[o as usize] {
                    self.key_over = true;
                } else {
                    self.key.push_str(t);
                }
            }
            Event::EndKey => {
                let slot = if self.key_over {
                    None
                } else {
                    node.slot(&self.key)
                };
                match slot {
                    // A duplicate: the first occurrence stands.
                    Some(i) if self.seen[o as usize][i] => self.skip_next = true,
                    Some(i) => {
                        self.seen[o as usize][i] = true;
                        self.generation += 1;
                        match node.slots()[i].child {
                            Some(c) => self.pending_value = Some(c),
                            None => self.skip_next = true,
                        }
                    }
                    None => self.skip_next = true,
                }
            }
            Event::EndObject => {
                self.frames.pop();
                self.closed[o as usize] = true;
                for (i, slot) in node.slots().iter().enumerate() {
                    let Some(c) = slot.child else { continue };
                    if self.seen[o as usize][i] {
                        continue;
                    }
                    self.cells[c as usize] = if slot.required {
                        Cell::Failed(format!(
                            "`{}`: required by the schema, absent from the value",
                            shape.nodes[c as usize].path
                        ))
                    } else {
                        Cell::Absent
                    };
                }
                self.generation += 1;
            }
            // Not reachable for a well-nested producer: a value always follows its key.
            _ => {}
        }
    }

    /// The value of tracked node `n` opens with `e`.
    fn value_starts(&mut self, shape: &GovernedShape, n: NodeId, e: Event<'_>) {
        let node = &shape.nodes[n as usize];
        match (&node.kind, e) {
            (Kind::Leaf(Leaf::Bool), Event::Bool(b)) => {
                self.settle(n, Cell::Value(CelValue::Bool(b)))
            }
            // Exact: integer text is an integer, and integer text outside `[i64::MIN, u64::MAX]`
            // fails the read rather than rounding to a neighbour.
            (Kind::Leaf(Leaf::Num), Event::Number(t)) => match crate::CelNum::parse_json(t) {
                Ok(v) => self.settle(n, Cell::Value(CelValue::from(v))),
                Err(crate::Inexact) => {
                    let m = format!(
                        "`{}`: schema says {}, value `{t}` is not a number held exactly \
                         (an integer outside [-9223372036854775808, 18446744073709551615])",
                        node.path, node.ty_name
                    );
                    self.settle(n, Cell::Failed(m))
                }
            },
            (Kind::Leaf(Leaf::Num), Event::NumberTooLong) => {
                self.capped = Some(CAP_NUMBER_TOO_LONG)
            }
            (Kind::Leaf(Leaf::Str | Leaf::Duration), Event::BeginString) => {
                self.cells[n as usize] = Cell::Accumulating(String::new());
                self.acc = Some(n);
            }
            (Kind::Container { .. }, Event::BeginObject) => {
                self.settle(n, Cell::View);
                self.frames.push(n);
            }
            (_, other) => {
                let m = format!(
                    "`{}`: schema says {}, value is {}",
                    node.path,
                    node.ty_name,
                    shape_of(&other)
                );
                self.fail_subtree(shape, n, &m);
                self.skip_value(&other);
            }
        }
    }

    /// A fragment or the end of string leaf `n`.
    fn accumulate(&mut self, shape: &GovernedShape, n: NodeId, e: Event<'_>) {
        match e {
            Event::Text(t) => {
                self.held += t.len();
                if self.held > shape.cell_cap {
                    // Never a truncated value: the cell goes back to pending, its text is freed,
                    // and the document is capped.
                    if let Cell::Accumulating(s) =
                        std::mem::replace(&mut self.cells[n as usize], Cell::Unsettled)
                    {
                        self.held -= s.len();
                    }
                    self.held -= t.len();
                    self.acc = None;
                    self.capped = Some(CAP_CELL_BYTES);
                } else if let Cell::Accumulating(s) = &mut self.cells[n as usize] {
                    s.push_str(t);
                }
            }
            Event::EndString => {
                self.acc = None;
                let Cell::Accumulating(s) =
                    std::mem::replace(&mut self.cells[n as usize], Cell::Unsettled)
                else {
                    unreachable!("an accumulating node holds its text");
                };
                let node = &shape.nodes[n as usize];
                let cell = match node.kind {
                    Kind::Leaf(Leaf::Duration) => {
                        self.held -= s.len();
                        match crate::duration::parse_duration(&s) {
                            // Full precision: `1500ns` stays 1500 nanoseconds.
                            Ok((_, d)) => {
                                Cell::Value(CelValue::Duration(crate::CelDuration::of(d)))
                            }
                            Err(e) => Cell::Failed(format!("`{}`: not a duration: {e}", node.path)),
                        }
                    }
                    _ => Cell::Value(CelValue::Str(s.into())),
                };
                self.settle(n, cell);
            }
            // Only fragments sit between a string's begin and end.
            _ => {}
        }
    }
}

/// A record or map node of one document, as CEL reads it.
#[derive(Debug)]
struct View {
    doc: Arc<DocInner>,
    node: NodeId,
}

/// The refusal for a member of `node` no path demanded.
fn undemanded(shape: &GovernedShape, node: NodeId, name: &str) -> CelError {
    CelError::Bind {
        message: format!(
            "`{}.{name}` was not demanded, so this document does not hold it",
            shape.nodes[node as usize].path
        ),
    }
}

impl LazyValue for View {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        match self.poll_member(name)? {
            Access::Ready(v) => Ok(v),
            Access::Pending(h) => Err(CelError::Bind {
                message: format!("`{name}` is not yet available (demand {})", h.id()),
            }),
        }
    }

    fn poll_member(&self, name: &str) -> Result<Access, CelError> {
        let st = self.doc.lock();
        Ok(match st.member(&self.doc.shape, self.node, name)? {
            Got::Pending(h) => Access::Pending(h),
            Got::Value(v) => Access::Ready(v.clone()),
            Got::View(c) => Access::Ready(CelValue::Lazy(Arc::new(View {
                doc: self.doc.clone(),
                node: c,
            }))),
        })
    }

    fn poll_has(&self, name: &str) -> Result<Presence, CelError> {
        self.doc.lock().presence(&self.doc.shape, self.node, name)
    }

    // keys(): None. A governed value is not iterable; comprehensions over it are refused when the
    // shape is built.
}

/// One document, read by the fields of one program: `paths[f]` is the member names below the
/// governed root of field `f`. Only the fields a [`StreamedProgram`] marked as the document's are
/// ever asked of it.
struct DocFacts<'d> {
    doc: &'d Doc,
    paths: &'d [Vec<String>],
}

impl<'d> DocFacts<'d> {
    /// Walk `names` from the root as the evaluator walks views: the answer to the last member, or
    /// where and why the walk stopped.
    fn walk(&self, names: &[String]) -> Result<Got<'d>, FactPoll> {
        let (shape, st) = (&*self.doc.shape, &self.doc.st);
        let mut got = Got::View(0);
        for (at, name) in names.iter().enumerate() {
            let Got::View(node) = got else {
                // Beneath a leaf: the shape refuses a path through one, so never reached.
                return Err(FactPoll::Failed {
                    at,
                    error: CelError::NoSuchMember { key: name.clone() },
                });
            };
            got = match st.member(shape, node, name) {
                Ok(Got::Pending(handle)) => return Err(FactPoll::Pending { at, handle }),
                Ok(g) => g,
                Err(error) => return Err(FactPoll::Failed { at, error }),
            };
        }
        Ok(got)
    }

    /// The settled value of field `f`, once [`poll`](Facts::poll) has answered `Ready`.
    fn leaf(&self, f: FieldId) -> Option<&'d CelValue> {
        match self.walk(&self.paths[f.index()]) {
            Ok(Got::Value(v)) => Some(v),
            _ => None,
        }
    }

    /// The presence of field `f`'s last member, on the view its prefix reaches.
    fn presence(&self, f: FieldId) -> Result<Presence, FactPoll> {
        let names = &self.paths[f.index()];
        let (last, prefix) = names.split_last().expect("a presence path has a member");
        let node = match self.walk(prefix)? {
            Got::View(node) => node,
            // Presence on a leaf: the checker refuses the question.
            _ => {
                return Err(FactPoll::Failed {
                    at: prefix.len(),
                    error: CelError::NoSuchMember { key: last.clone() },
                })
            }
        };
        self.doc
            .st
            .presence(&self.doc.shape, node, last)
            .map_err(|error| FactPoll::Failed {
                at: prefix.len(),
                error,
            })
    }
}

impl Facts for DocFacts<'_> {
    fn bool(&self, f: FieldId) -> Option<bool> {
        match self.leaf(f)? {
            CelValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn num(&self, f: FieldId) -> Option<f64> {
        self.number(f).map(crate::CelNum::as_f64)
    }

    fn number(&self, f: FieldId) -> Option<crate::CelNum> {
        self.leaf(f)?.num()
    }

    fn str(&self, f: FieldId) -> Option<&str> {
        match self.leaf(f)? {
            CelValue::Str(s) => Some(s),
            _ => None,
        }
    }

    fn duration_ms(&self, f: FieldId) -> Option<i64> {
        match self.leaf(f)? {
            CelValue::Duration(d) => Some(d.as_millis()),
            _ => None,
        }
    }

    fn has(&self, f: FieldId) -> bool {
        matches!(self.presence(f), Ok(Presence::Known(true)))
    }

    fn poll(&self, f: FieldId) -> FactPoll {
        match self.walk(&self.paths[f.index()]) {
            Ok(_) => FactPoll::Ready,
            Err(p) => p,
        }
    }

    fn poll_has(&self, f: FieldId) -> FactPoll {
        match self.presence(f) {
            Ok(Presence::Known(_)) => FactPoll::Ready,
            Ok(Presence::Pending(handle)) => FactPoll::Pending {
                at: self.paths[f.index()].len() - 1,
                handle,
            },
            Err(p) => p,
        }
    }
}

/// Everything a body check needs, built once. `Send + Sync`: shared by every flow that begins a
/// run.
pub struct StreamedProgram {
    /// The program on the fast backend, which every run executes.
    fast: Arc<FastProgram>,
    /// Per field of `fast`: is it read from the document (its root is `root`)?
    mine: Arc<[bool]>,
    /// Per field of `fast`: its member names below `root` (empty for a field that is not mine).
    paths: Arc<[Vec<String>]>,
    /// Every root the program reads bound, except `root`, which each run fills.
    template: CelTemplate,
    root: String,
    shape: Arc<GovernedShape>,
}

impl std::fmt::Debug for StreamedProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StreamedProgram")
            .field("root", &self.root)
            .field("shape", &self.shape)
            .field("template", &self.template)
            .finish_non_exhaustive()
    }
}

impl StreamedProgram {
    /// `act` carries every root the program reads except `root`, already bound. `program` is the
    /// program `code` was emitted from: its demand is what the shape is built over. Every refusal
    /// — an undeclared root, a demand a streamed value cannot settle, `root` already bound, a
    /// record or map under `root` read whole — happens here, not at the first body.
    ///
    /// A run executes `code` on the fast backend; `vm` is accepted for the signature's sake and
    /// holds nothing a run needs.
    pub fn new(
        vm: Arc<Vm>,
        env: &CelEnvironment,
        program: &CelProgram,
        code: Arc<CelBytecode>,
        act: CelActivation,
        root: &str,
    ) -> Result<StreamedProgram, CelError> {
        drop(vm);
        let ty = env.types().get(root).ok_or_else(|| CelError::Bind {
            message: format!("`{root}` is not declared in this environment"),
        })?;
        let shape = Arc::new(GovernedShape::build(root, ty, program.demand())?);
        let fast = code.fast.clone();
        let reads = fast.value_reads();
        let mut mine = vec![false; fast.fields().len()];
        let mut paths = vec![Vec::new(); fast.fields().len()];
        for (i, field) in fast.fields().iter().enumerate() {
            if field.root() != root {
                continue;
            }
            let names: Vec<String> = field.segments().map(str::to_string).collect();
            if reads[i] && shape.reads_container(&names) {
                let path = std::iter::once(root)
                    .chain(names.iter().map(String::as_str))
                    .collect::<Vec<_>>()
                    .join(".");
                return Err(refuse(
                    &path,
                    "a streamed value is read by its named scalar members; this record or map \
                     is read whole"
                        .to_string(),
                ));
            }
            mine[i] = true;
            paths[i] = names;
        }
        let template = act.into_template(&[root])?;
        Ok(StreamedProgram {
            fast,
            mine: mine.into(),
            paths: paths.into(),
            template,
            root: root.to_string(),
            shape,
        })
    }

    /// One body. Runs the program at once: it may decide without reading the body.
    pub fn begin(&self) -> StreamedRun {
        // The document is the run's own, read by field; nothing reads `root` through the
        // bindings, which carry only the other roots. The template still wants it filled.
        let bindings = self
            .template
            .instantiate(vec![(self.root.as_str(), CelValue::Null)])
            .expect("the open root was declared when the template was built");
        let mut run = StreamedRun {
            fast: self.fast.clone(),
            mine: self.mine.clone(),
            paths: self.paths.clone(),
            doc: Doc::new(self.shape.clone()),
            bindings,
            vm: Run::Suspended(Paused::start()),
            seen: 0,
            steps: 0,
        };
        run.resume();
        run
    }
}

/// What a [`StreamedRun`] makes of the body so far.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunLiveness {
    /// Nothing has decided against the body: the program accepted, or is still waiting.
    Live,
    /// Refused by a verdict that is `false` or an error. Final.
    Dead,
    /// A cap was reached before the body could be decided. Final.
    Capped(&'static str),
}

/// One body's check: the document and the paused run. `Send`: it rides in its
/// flow between worker threads. Only a pushed event can settle a cell, so the thread that pushes is
/// the one that resumes the run; nothing else ever makes a waiting run runnable.
///
/// The run OWNS the document and every event reaches it through `&mut`: no lock is taken per
/// event (`tests/governed_doc.rs::a_governed_push_takes_no_lock`).
pub struct StreamedRun {
    fast: Arc<FastProgram>,
    mine: Arc<[bool]>,
    paths: Arc<[Vec<String>]>,
    doc: Doc,
    bindings: CelBindings,
    vm: Run,
    /// The document generation the run last ran against.
    seen: u64,
    steps: usize,
}

impl std::fmt::Debug for StreamedRun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StreamedRun")
            .field("vm", &self.vm)
            .field("seen", &self.seen)
            .field("steps", &self.steps)
            .finish_non_exhaustive()
    }
}

#[derive(Debug)]
enum Run {
    /// Paused on a read of the document that has not settled. Holds only its own arena and
    /// references into `fast`'s constants, which the run holds too.
    Suspended(Paused),
    Decided(Result<bool, CelError>),
    /// Ended outside the program (a capped document); its state is gone.
    Released(RunLiveness),
}

impl StreamedRun {
    /// One event, in document order.
    pub fn push(&mut self, e: Event<'_>) -> RunLiveness {
        match &self.vm {
            Run::Released(why) => return *why,
            Run::Decided(r) if !matches!(r, Ok(true)) => return RunLiveness::Dead,
            _ => {}
        }
        if let Run::Suspended(_) = self.vm {
            self.doc.push(e);
            if let Some(what) = self.doc.capped() {
                return self.release(RunLiveness::Capped(what));
            }
            // Resume only when something settled: a fragment of a member nobody reads moves
            // nothing, and resuming on it would cost a run entry per fragment.
            if self.doc.generation() != self.seen {
                self.resume();
            }
        }
        self.liveness()
    }

    /// The document ended. `Ok(true)` only when the run finished `Ok(true)`.
    pub fn finish(mut self) -> Result<bool, CelError> {
        if let Run::Suspended(_) = self.vm {
            self.doc.end();
            self.resume();
        }
        match self.vm {
            Run::Decided(r) => r,
            // Unreachable for a program over the governed root alone, whose every cell settles at
            // `end`; reachable for one that also reads some other lazy that is still pending.
            // Never an accept.
            Run::Suspended(_) => Err(CelError::Bind {
                message: "the program was still waiting after the document ended".into(),
            }),
            Run::Released(_) => Ok(false),
        }
    }

    /// What this run holds: the governed document. The run's registers are bounded by the code,
    /// not by the body.
    pub fn state_bytes(&self) -> usize {
        self.doc.state_bytes()
    }

    /// The run's verdict, once it has one.
    pub fn decided(&self) -> Option<&Result<bool, CelError>> {
        match &self.vm {
            Run::Decided(r) => Some(r),
            _ => None,
        }
    }

    /// How many times this run has been resumed.
    #[doc(hidden)]
    pub fn steps(&self) -> usize {
        self.steps
    }

    /// The run ended outside the program and dropped its state.
    #[doc(hidden)]
    pub fn vm_released(&self) -> bool {
        matches!(self.vm, Run::Released(_))
    }

    fn resume(&mut self) {
        self.seen = self.doc.generation();
        if !matches!(self.vm, Run::Suspended(_)) {
            return;
        }
        let Run::Suspended(paused) =
            std::mem::replace(&mut self.vm, Run::Released(RunLiveness::Live))
        else {
            unreachable!("checked above");
        };
        self.steps += 1;
        let facts = DocFacts {
            doc: &self.doc,
            paths: &self.paths,
        };
        match self.fast.resume(
            paused,
            self.bindings.roots(),
            Some((&facts, &self.mine[..])),
        ) {
            Resumed::Done(r) => self.vm = Run::Decided(r),
            Resumed::Need(_, paused) => self.vm = Run::Suspended(paused),
        }
    }

    fn release(&mut self, why: RunLiveness) -> RunLiveness {
        self.vm = Run::Released(why);
        why
    }

    fn liveness(&self) -> RunLiveness {
        match &self.vm {
            Run::Suspended(_) | Run::Decided(Ok(true)) => RunLiveness::Live,
            Run::Decided(_) => RunLiveness::Dead,
            Run::Released(why) => *why,
        }
    }
}
