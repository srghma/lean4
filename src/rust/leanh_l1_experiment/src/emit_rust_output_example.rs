//! Example of what EmitRust would generate with the new safe types.
//! Each example is labelled: STATIC (can be a `static`) or LAZY (needs LazyLock).

use std::borrow::Cow;
use std::sync::{Arc, LazyLock};
use tokio::sync::{Mutex, OnceCell};

use crate::datatypes::{
    AtomicOnceCellLock, AtomicOnceCellState, LeanFn, LeanNat, LeanObject, LeanOnceCell, LeanRef,
    OnceCellLock, OnceCellState, ScalarData,
};

// ─── STATIC: bare Nat literals ───────────────────────────────────────────────
pub static LEAN_NAT_ZERO: LeanObject = LeanObject::Nat(LeanNat::Small(0));
pub static LEAN_NAT_42: LeanObject = LeanObject::Nat(LeanNat::Small(42));

// ─── STATIC: string literal ──────────────────────────────────────────────────
pub static LEAN_STRING_HELLO: LeanObject = LeanObject::String {
    char_count: 5,
    bytes: Cow::Borrowed("hello"),
};

// ─── STATIC: unit constructor (no object refs, no scalars) ──────────────────
//  Bool.true / Bool.false / Unit.unit / Ordering.lt etc.
pub static LEAN_UNIT: LeanObject = LeanObject::Ctor {
    ctor_tag: 0,
    objs: Cow::Borrowed(&[]),
    scalars: Cow::Borrowed(&[]),
};
pub static LEAN_BOOL_FALSE: LeanObject = LeanObject::Ctor {
    ctor_tag: 0,
    objs: Cow::Borrowed(&[]),
    scalars: Cow::Borrowed(&[]),
};
pub static LEAN_BOOL_TRUE: LeanObject = LeanObject::Ctor {
    ctor_tag: 1,
    objs: Cow::Borrowed(&[]),
    scalars: Cow::Borrowed(&[]),
};

// ─── STATIC: ctor with a packed f64 scalar (e.g. Float literal) ─────────────
// `to_ne_bytes()` creates a temporary; name it as a const to get a 'static reference.
const PI_BYTES: [u8; 8] = std::f64::consts::PI.to_ne_bytes();
pub static LEAN_FLOAT_PI: LeanObject = LeanObject::Ctor {
    ctor_tag: 0,
    objs: Cow::Borrowed(&[]),
    scalars: Cow::Borrowed(&PI_BYTES),
};

// ─── STATIC: ByteArray / ScalarArray constants ───────────────────────────────
pub static LEAN_EMPTY_BYTE_ARRAY: LeanObject =
    LeanObject::ScalarArray(ScalarData::U8(Cow::Borrowed(b"")));
pub static LEAN_BYTES: LeanObject =
    LeanObject::ScalarArray(ScalarData::U8(Cow::Borrowed(b"hello\x00")));
pub static LEAN_FLOAT_ARRAY: LeanObject =
    LeanObject::ScalarArray(ScalarData::F64(Cow::Borrowed(&[1.0, 2.0, 3.0])));
pub static LEAN_UINT32_ARRAY: LeanObject =
    LeanObject::ScalarArray(ScalarData::U32(Cow::Borrowed(&[10, 20, 30])));

// ─── STATIC: tokio OnceCell / Mutex — both constructors ARE const ────────────
pub static LEAN_THUNK_UNINIT: LeanObject = LeanObject::Thunk {
    result: OnceCell::const_new(),
    closure: Mutex::const_new(None),
};
pub static LEAN_PROMISE_UNINIT: LeanObject = LeanObject::Promise {
    result: OnceCell::const_new(),
};

// ─── STATIC: module-level once-cell (for lazy module init) ───────────────────
pub static LEAN_ONCE: LeanOnceCell = LeanOnceCell {
    state: AtomicOnceCellState::new(OnceCellState::Uninitialized),
    lock: AtomicOnceCellLock::new(OnceCellLock::Unlocked),
};

// ─── STATIC: non-capturing closure — function pointer is const ───────────────
// EmitRust generates a top-level fn for the closure body, then wraps it.
fn lean_add_one(args: &[LeanRef]) -> LeanRef {
    // real impl would inspect args[0] and return Nat(n+1)
    Arc::clone(&args[0])
}
pub static LEAN_ADD_ONE: LeanObject = LeanObject::Closure {
    fun: LeanFn::Ptr(lean_add_one), // ← fn pointer, const ✓
    captured: Cow::Borrowed(&[]),
    arity: 1,
};

// ─── LAZY: ctor with object-ref fields — Arc is not const ────────────────────
// List.cons "hello" List.nil
pub static LEAN_LIST_NIL: LeanObject = LeanObject::Ctor {
    ctor_tag: 0,
    objs: Cow::Borrowed(&[]),
    scalars: Cow::Borrowed(&[]),
};

pub static LEAN_LIST_CONS: LazyLock<LeanObject> = LazyLock::new(|| {
    LeanObject::Ctor {
        ctor_tag: 1,
        objs: Cow::Owned(vec![
            Arc::new(LeanObject::String {
                char_count: 5,
                bytes: Cow::Borrowed("hello"),
            }),
            // reference to the static nil — needs a LeanRef, so we clone via Arc
            // (problem: LEAN_LIST_NIL is not Arc — see note below)
            Arc::new(LeanObject::Ctor {
                ctor_tag: 0,
                objs: Cow::Borrowed(&[]),
                scalars: Cow::Borrowed(&[]),
            }),
        ]),
        scalars: Cow::Owned(vec![]),
    }
});

// ─── LAZY: capturing closure ──────────────────────────────────────────────────
// fun x => x + captured_value
pub fn make_adder(n: u64) -> LeanObject {
    LeanObject::Closure {
        fun: LeanFn::Dyn(Arc::new(move |args: &[LeanRef]| {
            // real impl: args[0] + n
            Arc::clone(&args[0])
        })),
        captured: Cow::Owned(vec![Arc::new(LeanObject::Nat(LeanNat::Small(n)))]),
        arity: 1,
    }
}
