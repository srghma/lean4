//! Safe, idiomatic pure-Rust model of the Lean object types — **split per object,
//! and split again into `…Static` and `…Heap` forms**.
//!
//! This is a pure-Rust rewrite: there is **no** `repr(C)`, no `*mut LeanObject`,
//! no ABI boundary to a C runtime. Because static-ness is never erased through an
//! opaque pointer, we can push it into the *type system*.
//!
//! # The two forms of every object
//!
//! * `XxxStatic` — a compile-time / immortal instance. Reference count is *absent*
//!   (the C model's `m_rc == 0` "persistent" sentinel). Fields borrow `'static`
//!   data (`&'static str`, `&'static [T]`), so the value can live in a `static`
//!   item or a `LazyLock`. Never freed.
//! * `XxxHeap`   — a runtime instance owned by an `Rc` (the C model's `m_rc > 0`
//!   single-threaded case). Fields own their data (`String`, `Vec<_>`). Freed when
//!   the last `Rc` drops — i.e. **when the bean count reaches zero**.
//!
//! (The C model's `m_rc < 0` multi-threaded case maps to `Arc`; converting an ST
//! graph to MT is `lean_mark_mt`'s deep-conversion job and is omitted from this
//! demo — see the note on `LeanRef`.)
//!
//! # "Counting beans" — safely, without raw pointers
//!
//! We keep manual reference counting *semantics* (free exactly when the count hits
//! zero) but implement it with `Rc`, whose strong count **is** the bean count:
//!
//! * `lean_inc` ≙ `Rc::clone`   (bean++)
//! * `lean_dec` ≙ `drop`        (bean--, free at 0)
//! * `lean_is_exclusive` ≙ `Rc::get_mut(..).is_some()` (count == 1)
//!
//! The one thing `Rc` gets *wrong* for Lean is that its default `Drop` recurses
//! into children — a million-element `List` would overflow the stack. So `LeanHeap`
//! has a custom `Drop` that reproduces Lean's **iterative** teardown (the `todo`
//! worklist from `object.cpp`), keeping deletion O(1) in stack depth. That is the
//! whole trick to marrying "linear ownership" with "free when rc == 0": let `Rc`
//! own the count, but take deletion into our own hands.
//!
//! Static objects never participate: `lean_inc`/`lean_dec` on them are no-ops,
//! exactly like the `m_rc == 0` fall-through in `lean_dec_ref`.

use std::borrow::Cow;
use std::cell::{OnceCell, RefCell};
use std::rc::Rc;

use atomic_enum::atomic_enum;
use num_bigint::BigInt;

// ─────────────────────────────────────────────────────────────────────────────
// References
// ─────────────────────────────────────────────────────────────────────────────

/// A reference that can appear as a **field of a static object**.
///
/// Crucially it *cannot* be a heap ref. This makes the whole `…Static` family
/// `Sync` and const-constructible for free, and — more importantly — it lets the
/// type system **prove the invariant** that a compile-time-constant object never
/// points into the runtime heap (which would be a dangling/immortal-into-mortal
/// bug). A heap ref simply has no way to be stored here.
#[derive(Copy, Clone, Debug)]
pub enum LeanStaticRef {
    /// Unboxed value (the tagged-pointer scalar world): small `Nat`, `Bool`, …
    Scalar(usize),
    /// Points at another immortal object.
    Static(&'static LeanStatic),
}

/// The universal runtime reference. Replaces `*mut LeanObject`.
///
/// * `Scalar`  — unboxed, no allocation (was: tagged pointer, low bit set).
/// * `Static`  — immortal object, no refcount (was: `m_rc == 0` persistent).
/// * `Heap`    — single-threaded ref-counted object (was: `m_rc > 0`).
///
/// A multi-threaded object (was: `m_rc < 0`) would be a fourth `Shared(Arc<..>)`
/// variant; it is elided here because turning an `Rc` graph into an `Arc` graph
/// (`lean_mark_mt`) requires a deep rewrite that Rust's types cannot do in place.
#[derive(Clone, Debug)]
pub enum LeanRef {
    Scalar(usize),
    Static(&'static LeanStatic),
    Heap(Rc<LeanHeap>),
}

impl From<LeanStaticRef> for LeanRef {
    #[inline]
    fn from(r: LeanStaticRef) -> Self {
        match r {
            LeanStaticRef::Scalar(n) => LeanRef::Scalar(n),
            LeanStaticRef::Static(s) => LeanRef::Static(s),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The two object families
// ─────────────────────────────────────────────────────────────────────────────

/// Immortal (persistent) objects. Every variant is `Sync` and holds only
/// `'static` / owned-`Sync` data, so a `LeanStatic` can live in a `static` item.
///
/// Note which object kinds are **absent**: `Ref`, `Thunk`, `Task`, `Promise`.
/// They require interior mutability (`RefCell`/`OnceCell`), which is not `Sync`,
/// so they genuinely have no static form — they are heap-only. This is the
/// type-level echo of "static-ness is not uniform across object kinds".
#[derive(Debug)]
pub enum LeanStatic {
    Ctor(LeanCtorObjectStatic),
    Array(LeanArrayObjectStatic),
    ScalarArray(LeanScalarArrayStatic),
    String(LeanStringObjectStatic),
    Closure(LeanClosureObjectStatic),
    Mpz(LeanMpzObjectStatic),
    External(LeanExternalObjectStatic),
}

/// Runtime, ref-counted objects. Owns its data; freed when the last `Rc` drops.
/// Has a custom iterative [`Drop`] so long chains don't blow the stack.
#[derive(Debug)]
pub enum LeanHeap {
    Ctor(LeanCtorObjectHeap),
    Array(LeanArrayObjectHeap),
    ScalarArray(LeanScalarArrayHeap),
    String(LeanStringObjectHeap),
    Closure(LeanClosureObjectHeap),
    Mpz(LeanMpzObjectHeap),
    External(LeanExternalObjectHeap),
    // heap-only (need interior mutability → not `Sync` → no static form):
    Ref(LeanRefObjectHeap),
    Thunk(LeanThunkObjectHeap),
    Task(LeanTaskObjectHeap),
    Promise(LeanPromiseObjectHeap),
}

// ─────────────────────────────────────────────────────────────────────────────
// Ctor (tags 0–243)
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct LeanCtorObjectStatic {
    pub tag: u8,
    /// Object fields — provably all static/scalar (see [`LeanStaticRef`]).
    pub objs: &'static [LeanStaticRef],
    /// Packed scalar fields (e.g. a nested `Float`).
    pub scalars: &'static [u8],
}

#[derive(Debug)]
pub struct LeanCtorObjectHeap {
    pub tag: u8,
    pub objs: Vec<LeanRef>,
    pub scalars: Vec<u8>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Array (tag 246) — array of object references
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct LeanArrayObjectStatic {
    pub data: &'static [LeanStaticRef],
}

#[derive(Debug)]
pub struct LeanArrayObjectHeap {
    /// `size` and `capacity` from the C struct are `Vec::len`/`Vec::capacity`.
    pub data: Vec<LeanRef>,
}

// ─────────────────────────────────────────────────────────────────────────────
// ScalarArray (tag 248) — ByteArray / FloatArray / UInt32Array …
// ─────────────────────────────────────────────────────────────────────────────

/// Typed static scalar storage (borrowed). Replaces `uint8_t* + elem_size`.
#[derive(Copy, Clone, Debug)]
pub enum ScalarStatic {
    U8(&'static [u8]),
    U16(&'static [u16]),
    U32(&'static [u32]),
    U64(&'static [u64]),
    USize(&'static [usize]),
    F32(&'static [f32]),
    F64(&'static [f64]),
}

/// Typed owned scalar storage (heap).
#[derive(Clone, Debug)]
pub enum ScalarHeap {
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
    U64(Vec<u64>),
    USize(Vec<usize>),
    F32(Vec<f32>),
    F64(Vec<f64>),
}

#[derive(Debug)]
pub struct LeanScalarArrayStatic {
    pub data: ScalarStatic,
}

#[derive(Debug)]
pub struct LeanScalarArrayHeap {
    pub data: ScalarHeap,
}

// ─────────────────────────────────────────────────────────────────────────────
// String (tag 249)
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct LeanStringObjectStatic {
    /// Unicode code-point count (was `m_length`).
    pub char_count: usize,
    /// UTF-8 bytes, borrowed `'static`. No NUL terminator, no `m_capacity`.
    pub bytes: &'static str,
}

#[derive(Debug)]
pub struct LeanStringObjectHeap {
    pub char_count: usize,
    /// Owned, growable — `String`'s own len/capacity replace `m_size`/`m_capacity`.
    pub bytes: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Closure (tag 245)
// ─────────────────────────────────────────────────────────────────────────────

/// Non-capturing function pointer — `Copy`, usable in a `static`.
pub type LeanFnPtr = fn(&[LeanRef]) -> LeanRef;

/// A callable. `Ptr` for top-level fns, `Dyn` for capturing closures.
pub enum LeanFn {
    Ptr(LeanFnPtr),
    Dyn(Rc<dyn Fn(&[LeanRef]) -> LeanRef>),
}

impl std::fmt::Debug for LeanFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeanFn::Ptr(_) => f.write_str("LeanFn::Ptr(..)"),
            LeanFn::Dyn(_) => f.write_str("LeanFn::Dyn(..)"),
        }
    }
}

#[derive(Debug)]
pub struct LeanClosureObjectStatic {
    /// A `static` closure captures nothing, so only a bare fn pointer is allowed.
    pub fun: LeanFnPtr,
    pub captured: &'static [LeanStaticRef],
    pub arity: u16,
}

#[derive(Debug)]
pub struct LeanClosureObjectHeap {
    pub fun: LeanFn,
    pub captured: Vec<LeanRef>,
    pub arity: u16,
}

// ─────────────────────────────────────────────────────────────────────────────
// Mpz (tag 250) — big integers (replaces GMP `mpz_t`)
// ─────────────────────────────────────────────────────────────────────────────
//
// `BigInt` is not `const`-constructible, so a *static* big-int literal is built
// once inside a `LazyLock` and then referenced as `&'static` — the pure-Rust
// analogue of "allocate at init, then `lean_mark_persistent`". The struct is the
// same shape as the heap one; only the ownership/lifetime differs.

#[derive(Clone, Debug)]
pub struct LeanMpzObjectStatic {
    pub value: BigInt,
}

#[derive(Clone, Debug)]
pub struct LeanMpzObjectHeap {
    pub value: BigInt,
}

// ─────────────────────────────────────────────────────────────────────────────
// External (tag 254) — user data with a custom finalizer
// ─────────────────────────────────────────────────────────────────────────────

/// Replaces `LeanExternalClass { m_finalize, m_foreach } + void* m_data`.
/// `Drop` is the finalizer; `foreach` is GC traversal.
pub trait LeanExternal: std::fmt::Debug {
    fn foreach(&self, visit: &mut dyn FnMut(&LeanRef));
}

#[derive(Debug)]
pub struct LeanExternalObjectStatic {
    /// Immortal external data. Must be `Sync` to live in a `static`.
    pub obj: &'static (dyn LeanExternal + Sync),
}

#[derive(Debug)]
pub struct LeanExternalObjectHeap {
    pub obj: Rc<dyn LeanExternal>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Heap-only mutable objects: Ref, Thunk, Task, Promise
// ─────────────────────────────────────────────────────────────────────────────

/// IO.Ref / ST.Ref (tag 253). Interior-mutable → heap-only.
#[derive(Debug)]
pub struct LeanRefObjectHeap {
    pub value: RefCell<LeanRef>,
}

/// Lazy thunk (tag 251). `value` cached once; `closure` cleared after forcing.
#[derive(Debug)]
pub struct LeanThunkObjectHeap {
    pub value: OnceCell<LeanRef>,
    pub closure: RefCell<Option<LeanRef>>,
}

/// Task (tag 252) — simplified: result cell + the closure to run.
#[derive(Debug)]
pub struct LeanTaskObjectHeap {
    pub value: OnceCell<LeanRef>,
    pub closure: RefCell<Option<LeanRef>>,
}

/// Promise (tag 244) — externally-resolved result cell.
#[derive(Debug)]
pub struct LeanPromiseObjectHeap {
    pub result: OnceCell<LeanRef>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Iterative teardown — the "counting beans" free, made stack-safe
// ─────────────────────────────────────────────────────────────────────────────

impl LeanHeap {
    /// Move every child `LeanRef` out of `self` into `todo`, leaving `self`
    /// child-free. After this returns, dropping `self` touches no other object.
    fn take_children(&mut self, todo: &mut Vec<LeanRef>) {
        match self {
            LeanHeap::Ctor(o) => todo.append(&mut o.objs),
            LeanHeap::Array(o) => todo.append(&mut o.data),
            LeanHeap::Closure(o) => todo.append(&mut o.captured),
            LeanHeap::Ref(o) => {
                todo.push(std::mem::replace(o.value.get_mut(), LeanRef::Scalar(0)));
            }
            LeanHeap::Thunk(o) => {
                if let Some(v) = o.value.take() {
                    todo.push(v);
                }
                if let Some(c) = o.closure.get_mut().take() {
                    todo.push(c);
                }
            }
            LeanHeap::Task(o) => {
                if let Some(v) = o.value.take() {
                    todo.push(v);
                }
                if let Some(c) = o.closure.get_mut().take() {
                    todo.push(c);
                }
            }
            LeanHeap::Promise(o) => {
                if let Some(v) = o.result.take() {
                    todo.push(v);
                }
            }
            // no object children:
            LeanHeap::String(_)
            | LeanHeap::ScalarArray(_)
            | LeanHeap::Mpz(_)
            | LeanHeap::External(_) => {}
        }
    }
}

impl Drop for LeanHeap {
    /// Reproduces `object.cpp`'s iterative `todo`-list deletion. Recursion depth
    /// stays ≤ 2 regardless of graph depth: we take each node's children onto a
    /// heap worklist *before* it drops, so a node's own `Drop` finds nothing to
    /// recurse into.
    fn drop(&mut self) {
        let mut todo: Vec<LeanRef> = Vec::new();
        self.take_children(&mut todo);
        while let Some(child) = todo.pop() {
            // Only heap refs can trigger a free; Static/Scalar just evaporate.
            if let LeanRef::Heap(rc) = child {
                // If we hold the last reference, the bean count is now 0: unwrap
                // the node by value, harvest its children onto `todo`, then let it
                // drop with no children (so its `Drop` does no further recursion).
                if let Ok(mut inner) = Rc::try_unwrap(rc) {
                    inner.take_children(&mut todo);
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reference counting API (the bean counter)
// ─────────────────────────────────────────────────────────────────────────────

/// `lean_inc` — bump the bean count. No-op for immortal/unboxed values.
#[inline]
pub fn lean_inc(o: &LeanRef) -> LeanRef {
    match o {
        LeanRef::Scalar(n) => LeanRef::Scalar(*n),
        LeanRef::Static(s) => LeanRef::Static(s),      // immortal → no count
        LeanRef::Heap(rc) => LeanRef::Heap(Rc::clone(rc)), // bean++
    }
}

/// `lean_dec` — drop the bean count; frees (iteratively) at zero. Immortal and
/// unboxed values are no-ops, matching `lean_dec_ref`'s `m_rc == 0` fall-through.
#[inline]
pub fn lean_dec(o: LeanRef) {
    drop(o);
}

/// `lean_dec_ref` — the "known to be a heap object" fast path.
#[inline]
pub fn lean_dec_ref(o: Rc<LeanHeap>) {
    drop(o);
}

/// `lean_is_exclusive` — true iff this heap object has exactly one owner (`rc == 1`),
/// so it is safe to mutate in place. A static object is never exclusive.
#[inline]
pub fn lean_is_exclusive(o: &LeanRef) -> bool {
    matches!(o, LeanRef::Heap(rc) if Rc::strong_count(rc) == 1)
}

/// Current bean count of a heap ref (for tests / demos). `None` for non-heap.
#[inline]
pub fn lean_ref_count(o: &LeanRef) -> Option<usize> {
    match o {
        LeanRef::Heap(rc) => Some(Rc::strong_count(rc)),
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// String runtime primitives (used by the append variants)
// ─────────────────────────────────────────────────────────────────────────────

/// Allocate a fresh heap string `a ++ b`.
#[inline]
pub fn new_heap_string(a: &str, b: &str) -> Rc<LeanHeap> {
    let mut bytes = String::with_capacity(a.len() + b.len());
    bytes.push_str(a);
    bytes.push_str(b);
    let char_count = bytes.chars().count();
    Rc::new(LeanHeap::String(LeanStringObjectHeap { char_count, bytes }))
}

/// Borrow the UTF-8 of a heap object known to be a string.
#[inline]
pub fn heap_str(o: &LeanHeap) -> &str {
    match o {
        LeanHeap::String(s) => &s.bytes,
        _ => unreachable!("EmitRust guarantees this is a string"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Small-nat helpers (unboxed) & module once-cell
// ─────────────────────────────────────────────────────────────────────────────

/// Largest `Nat` that fits unboxed (was: tagged pointer, one bit reserved).
pub const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;

#[inline]
pub fn lean_small_nat(n: usize) -> LeanRef {
    LeanRef::Scalar(n)
}

/// Guards one-time module initialization. Typed atomic enums replace the raw
/// `AtomicI32 { state, lock }` of `lean_once_cell_t`.
#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellState {
    Uninitialized = 0,
    Initialized = 1,
}

#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellLock {
    Unlocked = 0,
    Locked = 1,
}

pub struct LeanOnceCell {
    pub state: AtomicOnceCellState,
    pub lock: AtomicOnceCellLock,
}

// ─────────────────────────────────────────────────────────────────────────────
// Compile-time constants
// ─────────────────────────────────────────────────────────────────────────────

pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16;
pub const LEAN_MAX_CTOR_FIELDS: u32 = 256;
pub const LEAN_MAX_CTOR_SCALARS_SIZE: u32 = 1024;

// Kept so downstream code that still speaks `Cow` compiles unchanged.
pub type LeanRefs = Cow<'static, [LeanRef]>;
