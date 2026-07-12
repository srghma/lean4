//! Safe, idiomatic Rust model of Lean object types.
//!
//! Design goals:
//! - No raw pointers: `*mut LeanObject` → `LeanRef = Arc<LeanObject>`
//! - No `repr(C)` or `unsafe` blocks in this file
//! - No magic numeric tags: every discriminant is a named enum variant
//! - No GMP / libuv / libc: replaced by `num-bigint`, `std::sync`, `std::thread`
//! - Closures: `Arc<dyn Fn>` instead of `*mut c_void`
//! - External objects: `Arc<dyn LeanExternal>` trait object instead of vtable struct

use std::borrow::Cow;
use std::sync::Arc;
use tokio::sync::{Mutex, OnceCell};

use atomic_enum::atomic_enum;
use num_bigint::BigUint;

// ─── Primary reference type ───────────────────────────────────────────────────

/// Every Lean heap object is reference-counted via `Arc`.
/// Replaces `*mut LeanObject` (and the manual `rc: i32` field).
pub type LeanRef = Arc<LeanObject>;

/// A slice of object references. `Cow::Borrowed` for compile-time statics
/// (EmitRust emits a `static [LeanRef; N]`), `Cow::Owned` for heap objects.
///
/// Note: static initialization requires `LazyLock<LeanRef>` in EmitRust since
/// `Arc::new` is not const. The `Cow::Borrowed` path is used for future
/// const-Arc support or a custom static-ref type.
pub type LeanRefs = Cow<'static, [LeanRef]>;

// ─── Natural numbers (the only scalar-tagged runtime primitive) ───────────────

/// Lean `Nat`. Small values avoid heap allocation; large values use pure-Rust
/// arbitrary-precision arithmetic via `num-bigint` (replaces GMP `mpz_t`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanNat {
    /// Fits in 64 bits (was: tagged pointer with bit 0 set, `lean_box(n)`)
    Small(u64),
    /// Arbitrary precision (was: `LeanMpzObject` / `mpz_t`)
    Big(Box<BigUint>),
}

// ─── External objects — trait replaces the vtable struct ─────────────────────

/// Replaces `LeanExternalClass { m_finalize, m_foreach }` + `*mut c_void` data.
/// - Finalizer → `Drop` on the implementing type
/// - `m_foreach` → `foreach` method for GC traversal
pub trait LeanExternal: Send + Sync {
    fn foreach(&self, visit: &mut dyn FnMut(&LeanRef));
}

// ─── Closure function type ────────────────────────────────────────────────────

/// Replaces `*mut c_void m_fun` + unsafe call convention.
///
/// Two variants:
/// - `Ptr`: bare function pointer — `Copy`, zero heap, usable in `static` items.
/// - `Dyn`: capturing closure on the heap — the common runtime case.
pub enum LeanFn {
    /// Non-capturing closure. EmitRust emits a top-level `fn` and stores its pointer.
    Ptr(fn(&[LeanRef]) -> LeanRef),
    /// Capturing closure. Heap-allocated and reference-counted via `Arc`.
    Dyn(Arc<dyn Fn(&[LeanRef]) -> LeanRef + Send + Sync>),
}

impl Clone for LeanFn {
    fn clone(&self) -> Self {
        match self {
            Self::Ptr(f) => Self::Ptr(*f),
            Self::Dyn(f) => Self::Dyn(Arc::clone(f)),
        }
    }
}

// ─── Scalar data for typed arrays ────────────────────────────────────────────

/// Typed storage for a homogeneous array of scalar values.
/// Replaces `uint8_t* data` + `elem_size: u8` with a safe typed enum —
/// reading a `u32` from `&[u8]` at an offset no longer requires `unsafe`.
///
/// `Cow::Borrowed` for static constant arrays; `Cow::Owned` for heap arrays.
#[derive(Clone, Debug)]
pub enum ScalarData {
    U8   (Cow<'static, [u8   ]>),
    U16  (Cow<'static, [u16  ]>),
    U32  (Cow<'static, [u32  ]>),
    U64  (Cow<'static, [u64  ]>),
    USize(Cow<'static, [usize]>),
    F32  (Cow<'static, [f32  ]>),
    F64  (Cow<'static, [f64  ]>),
}

impl ScalarData {
    pub fn len(&self) -> usize {
        match self {
            Self::U8   (v) => v.len(),
            Self::U16  (v) => v.len(),
            Self::U32  (v) => v.len(),
            Self::U64  (v) => v.len(),
            Self::USize(v) => v.len(),
            Self::F32  (v) => v.len(),
            Self::F64  (v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool { self.len() == 0 }
}

// ─── Module-level once-cell (init guard, not a LeanObject) ───────────────────

/// Guards lazy one-time initialization of module-level constants.
/// Replaces `LeanOnceCell { state: AtomicI32, lock: AtomicI32 }` with typed
/// atomic enum fields via the `atomic_enum` crate.
#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellState { Uninitialized = 0, Initialized = 1 }

#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellLock { Unlocked = 0, Locked = 1 }

pub struct LeanOnceCell {
    pub state: AtomicOnceCellState,
    pub lock:  AtomicOnceCellLock,
}

// ─── Task priority ────────────────────────────────────────────────────────────

/// Replaces the raw `m_prio: u32` field in `LeanTaskImp`.
/// Lean's scheduler defines these levels; higher value = higher priority.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Default)]
pub enum TaskPriority {
    #[default]
    Low    = 0,
    Normal = 1,
    High   = 2,
    Dedicated = 3,
}

// ─── Main object enum ─────────────────────────────────────────────────────────

/// Every Lean runtime value. Replaces the family of C structs:
///
/// | Was (C/Rust struct)     | Now                              |
/// |-------------------------|----------------------------------|
/// | `LeanObject` (header)   | rc factored out via `Arc`        |
/// | `LeanCtorObject<N>`     | `Ctor { ctor_tag, objs, scalars }`|
/// | `LeanClosureObject<N>`  | `Closure { fun, captured, arity }`|
/// | `LeanArrayObject<N>`    | `Array { data }`                 |
/// | `LeanStringObject<N>`   | `String(Cow<'static, str>)`      |
/// | `LeanScalarArray<N>`    | `ScalarArray(ScalarData)`        |
/// | (same sarray struct)    | `StructArray { fields, len }`    |
/// | `LeanThunkObject`       | `Thunk { result, closure }`      |
/// | `LeanTaskObject`        | `Task { result, closure, ... }`  |
/// | `LeanPromiseObject`     | `Promise { result }`             |
/// | `LeanRefObject`         | `Ref { value }`                  |
/// | `LeanExternalObject`    | `External(Arc<dyn LeanExternal>)`|
/// | `LeanMpzObject`         | absorbed into `Nat(LeanNat::Big)`|
pub enum LeanObject {

    // ── Natural numbers (tag: was a tagged pointer, not an object tag) ──────
    /// Replaces both the tagged-pointer small-nat encoding AND `LeanMpzObject`.
    /// `LeanNat::Small(n)` costs zero heap; `LeanNat::Big(b)` costs one Box.
    Nat(LeanNat),

    // ── Constructor — algebraic data type (tags 0–243) ──────────────────────
    Ctor {
        /// Which constructor of the inductive type (0–243).
        ctor_tag: u8,
        /// Object-typed fields. `Cow::Borrowed` for static ctors.
        objs: LeanRefs,
        /// Scalar fields packed by the compiler (e.g. a nested `Float`).
        /// Interpretation is schema-defined by generated accessor code.
        scalars: Cow<'static, [u8]>,
    },

    // ── Lazy thunk (tag 251) ─────────────────────────────────────────────────
    /// Holds an unevaluated closure until first `force`, then caches the result.
    /// `OnceCell` ensures the closure runs at most once; callers can `.await` it.
    Thunk {
        /// Cached result. Written exactly once by whichever task forces first.
        result: OnceCell<LeanRef>,
        /// The closure to run. Cleared after forcing to release captured values.
        closure: Mutex<Option<LeanRef>>,
    },

    // ── Concurrent task (tag 252) ────────────────────────────────────────────
    /// A computation scheduled on the Tokio thread pool.
    /// Replaces `LeanTaskObject` + `LeanTaskImp`.
    ///
    /// With Tokio:
    /// - `OnceCell` replaces `AtomicPtr<LeanObject> m_value` + the C++ dependency
    ///   linked list (`m_head_dep`/`m_next_dep`): any number of async tasks can
    ///   `.await result.get_or_init(...)` and Tokio wakes them all when the cell
    ///   is set — no explicit dependents list needed.
    /// - `m_deleted` is dropped: `Arc` frees the object when the last ref drops.
    Task {
        /// The result, written by the Tokio task when it finishes.
        /// Replaces `AtomicPtr m_value` + the C++ intrusive dependents linked list.
        result: OnceCell<LeanRef>,
        /// The closure to run (cleared once spawned to release captured refs).
        closure: Mutex<Option<LeanRef>>,
        /// Scheduling metadata.
        priority: TaskPriority,
        /// Tokio task handle. `None` before spawn or after the handle is consumed.
        handle: Mutex<Option<tokio::task::JoinHandle<()>>>,
        /// Set to true by `IO.cancel`; checked by the worker before each step.
        canceled: std::sync::atomic::AtomicBool,
        /// If true, keep the task alive even when all external refs drop.
        keep_alive: bool,
    },

    // ── Promise — explicitly resolved task (tag 244) ──────────────────────────
    /// Like `Task` but the result is set externally via `IO.Promise.resolve`.
    Promise {
        result: OnceCell<LeanRef>,
    },

    // ── Closure (tag 245) ────────────────────────────────────────────────────
    /// A partially-applied function.
    /// `fun` holds the underlying callable; `captured` holds already-bound args.
    Closure {
        /// The function body. Takes `captured ++ new_args` and returns one value.
        fun: LeanFn,
        /// Already-bound arguments (partial application).
        captured: LeanRefs,
        /// Number of additional arguments still required before the call fires.
        arity: u16,
    },

    // ── Mutable reference cell — IORef (tag 253) ─────────────────────────────
    /// `tokio::sync::Mutex` so that IORef reads/writes compose naturally with
    /// async Lean computations without blocking the Tokio thread pool.
    Ref {
        value: Mutex<LeanRef>,
    },

    // ── Heap array of Lean objects (tag 246) ─────────────────────────────────
    Array {
        data: LeanRefs,
    },

    // ── Packed array of structs, column-store (tag 247) ──────────────────────
    /// Each element in `fields` holds all values for one struct field across
    /// every row.  `fields[0]` = column 0 for all `len` elements, etc.
    ///
    /// Example: `Point { x: f32, y: f32 }` array of 3 points →
    ///   `fields[0] = ScalarData::F32([x0, x1, x2])`
    ///   `fields[1] = ScalarData::F32([y0, y1, y2])`
    StructArray {
        fields: Vec<ScalarData>,
        len: usize,
    },

    // ── Packed array of a single scalar type — ByteArray, FloatArray (tag 248)
    ScalarArray(ScalarData),

    // ── UTF-8 string (tag 249) ───────────────────────────────────────────────
    /// Lean strings are always valid UTF-8.
    /// `char_count` is the number of Unicode codepoints (was `m_length`).
    /// Replaces `LeanStringObject<N>` with its NUL-terminated C-style buffer.
    String {
        char_count: usize,
        bytes: Cow<'static, str>,
    },

    // ── External object with user-defined lifecycle (tag 254) ────────────────
    /// Replaces `LeanExternalObject { m_class, m_data }`.
    /// The `Arc<dyn LeanExternal>` owns the data; `Drop` is the finalizer.
    External(Arc<dyn LeanExternal>),

    // ── Tag 255 — never allocated, exists only in the tag space ─────────────
    Reserved,
}

// ─── Task state ───────────────────────────────────────────────────────────────

/// Lifecycle phase of a concurrent Lean task.
/// Replaces the raw `#[repr(u8)] enum LeanTaskState` in production.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub enum LeanTaskState {
    #[default]
    Waiting  = 0,
    Running  = 1,
    Finished = 2,
}

// ─── IO result ────────────────────────────────────────────────────────────────

/// Lean `IO α` result: error branch is always a `LeanRef` to an `IO.Error` ctor.
/// Replaces `LeanIoResultTag { Ok=0, Error=1 }` with Rust's built-in `Result`.
/// `LeanOptionTag` is dropped entirely — use `Option<LeanRef>` directly.
pub type LeanIoResult<T> = Result<T, LeanRef>;

// ─── Three-valued boolean ─────────────────────────────────────────────────────

/// Logic.lbool from Lean's kernel: False / Undef / True.
/// Replaces the raw `i32` values -1 / 0 / 1.
#[repr(i32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub enum LBool {
    False = -1,
    #[default]
    Undef = 0,
    True  = 1,
}

impl From<i32> for LBool {
    fn from(v: i32) -> Self {
        match v { -1 => Self::False, 1 => Self::True, _ => Self::Undef }
    }
}

impl From<LBool> for i32 {
    fn from(v: LBool) -> Self { v as i32 }
}

// ─── Olean version ────────────────────────────────────────────────────────────

/// `.olean` file format version tag.
/// Replaces `OLEAN_VERSION_V2: u8 = 2` / `OLEAN_VERSION_V3: u8 = 3` constants.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum OleanVersion { V2 = 2, V3 = 3 }

impl OleanVersion {
    pub fn from_u8(v: u8) -> Self {
        match v {
            2 => Self::V2,
            3 => Self::V3,
            other => panic!("unknown olean version: {other}"),
        }
    }
}

impl From<OleanVersion> for u8 {
    fn from(v: OleanVersion) -> u8 { v as u8 }
}

// ─── Definition safety ────────────────────────────────────────────────────────

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanDefinitionSafety { Unsafe = 0, Safe = 1, Partial = 2 }

// ─── Module init function types (safe — no `unsafe fn`) ──────────────────────
//
// Production has `pub type ObjInitFn = unsafe fn() -> *mut LeanObject` etc.
// Here we remove `unsafe` (LeanRef is Arc, not a raw pointer) and drop the C
// calling convention. EmitRust emits Rust-native init fns; no FFI needed.

pub type ObjInitFn   = fn() -> LeanRef;
pub type BoolInitFn  = fn() -> bool;
pub type U8InitFn    = fn() -> u8;
pub type U16InitFn   = fn() -> u16;
pub type U32InitFn   = fn() -> u32;
pub type U64InitFn   = fn() -> u64;
pub type UsizeInitFn = fn() -> usize;
pub type F32InitFn   = fn() -> f32;
pub type F64InitFn   = fn() -> f64;

// ─── Library / dynamic loading info ──────────────────────────────────────────

/// Bookkeeping record for a dynamically loaded Lean library.
/// Replaces `LibInfo { base_addr: usize, id: std::string::String }`.
#[derive(Clone, Debug)]
pub struct LibInfo {
    pub base_addr: usize,
    pub id: String,
}

// ─── Compile-time constants ───────────────────────────────────────────────────

pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16;
pub const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;
pub const LEAN_OBJECT_SIZE_DELTA: usize = 8;
pub const LEAN_MAX_CTOR_FIELDS: u32 = 256;
pub const LEAN_MAX_CTOR_SCALARS_SIZE: u32 = 1024;

// Olean file layout
pub const OLEAN_HEADER_SIZE: usize = 88;
pub const OLEAN_MARKER: &[u8; 5] = b"olean";
pub const OLEAN_FLAGS_GMP: u8 = 0b1;

// Bignum limb layout (matches GMP / num-bigint 64-bit limb size)
pub const LEAN_MP_LIMB_SIZE: usize = 8;
