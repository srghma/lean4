// rc factors out — all variants share it
pub struct LeanObject {
    pub rc: i32,
    pub data: LeanObjectData,
}

pub enum LeanObjectData {
    // tags 0–243: constructor with N object fields + M scalar bytes
    Ctor {
        ctor_tag: u8,               // which constructor (was the tag value itself)
        objs: Vec<*mut LeanObject>, // was: other = num_objs, trailing pointer array
        scalars: Vec<u8>,           // was: cs_size = byte count, trailing scalar area
    },

    // tag 244
    Promise {
        result: *mut LeanTaskObject, // was: m_result: *mut LeanTaskObject
    },

    // tag 245
    Closure {
        fun: *mut c_void,            // was: m_fun
        arity: u16,                  // was: m_arity (total args the fn takes)
        num_fixed: u16,              // was: m_num_fixed (already-captured count)
        objs: Vec<*mut LeanObject>,  // was: other = num_fixed, trailing captured args
    },

    // tag 246
    Array {
        data: Vec<*mut LeanObject>,  // was: m_size + m_capacity + trailing m_data
    },

    // tag 247 — same memory layout as ScalarArray in C++, but semantically different
    StructArray {
        elem_size: u8,               // was: other = elem_size
        data: Vec<u8>,               // was: m_size + m_capacity + trailing bytes
    },

    // tag 248
    ScalarArray {
        elem_size: u8,               // was: other = elem_size
        data: Vec<u8>,               // was: m_size + m_capacity + trailing bytes
    },

    // tag 249
    String {
        char_count: usize,           // was: m_length (UTF-8 codepoint count)
        bytes: Vec<u8>,              // was: m_size + m_capacity + trailing m_data (NUL-terminated in C++)
    },

    // tag 250
    Mpz {
        value: mpz_t,                // was: m_value (GMP bignum)
    },

    // tag 251
    Thunk {
        value: AtomicPtr<LeanObject>,    // was: m_value
        closure: AtomicPtr<LeanObject>,  // was: m_closure
    },

    // tag 252
    Task {
        value: AtomicPtr<LeanObject>,    // was: m_value
        imp: *mut LeanTaskImp,           // was: m_imp
    },

    // tag 253
    Ref {
        value: *mut LeanObject,          // was: m_value
    },

    // tag 254
    External {
        class: *mut LeanExternalClass,   // was: m_class
        data: *mut c_void,               // was: m_data
    },

    // tag 255 — exists in the tag space but never allocated
    Reserved,
}

// EmitRust emits a static slice for the pointer array:
static LEAN_CTOR_2_OBJS: [*mut LeanObject; 2] = [ptr_a, ptr_b];

pub static LEAN_CTOR_2: LeanObject = LeanObject {
    rc: -1,
    data: LeanObjectData::Ctor {
        ctor_tag: 0,
        objs: std::borrow::Cow::Borrowed(&LEAN_CTOR_2_OBJS),
        scalars: std::borrow::Cow::Borrowed(&[]),
    },
};


-----------------




Plan: Replace Primitive Fields with Enums (Rust-First)

Context

Maximize type safety across the Rust runtime. No need to maintain C++ byte-for-byte layout parity — remove all repr(C) because they are not required (because we use or should use safe wrappers around cpp libs like uv and EmitRust will emit safe rust code)

LeanObject.tag: LeanObjectTag is already done. This plan covers the remaining fields.

---
New Cargo Dependency

Add atomic_enum = "0.3.0" to src/rust/leanh_l1/Cargo.toml.

The crate provides an #[atomic_enum] attribute macro that generates a typed AtomicXxx wrapper for C-style enums with full CAS/load/store/compare_exchange API — no unsafe
pointer casts needed.

---
Change 1 — LeanOnceCell → typed atomic enum fields

File: src/rust/leanh_l1/src/datatypes.rs

use atomic_enum::atomic_enum;

#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellState { Uninitialized = 0, Initialized = 1 }

#[atomic_enum]
#[derive(PartialEq)]
pub enum OnceCellLock { Unlocked = 0, Locked = 1 }

pub struct LeanOnceCell {
    pub state: AtomicOnceCellState,
    pub lock: AtomicOnceCellLock,
}

Remove repr(C) from LeanOnceCell.

File: src/rust/leanh_l1/src/runtime_once.rs

Replace magic 0/1 integer comparisons with typed enum variants:
fn lock_once_cell(lock: &AtomicOnceCellLock) {
    while lock.compare_exchange(
        OnceCellLock::Unlocked, OnceCellLock::Locked,
        Ordering::Acquire, Ordering::Relaxed,
    ).is_err() { std::thread::yield_now(); }
}
fn unlock_once_cell(lock: &AtomicOnceCellLock) {
    lock.store(OnceCellLock::Unlocked, Ordering::Release);
}
// In run_once:
if tok.state.load(Ordering::Acquire) != OnceCellState::Initialized {
    ...
    tok.state.store(OnceCellState::Initialized, Ordering::Release);
}

Emitted code impact: All gen_* crates that construct:
LeanOnceCell { state: AtomicI32::new(0), lock: AtomicI32::new(0) }
must change to: LeanOnceCell { state: AtomicOnceCellState::new(OnceCellState::Uninitialized), lock: AtomicOnceCellLock::new(OnceCellLock::Unlocked) }
Update the EmitRust generator (EmitRust.lean / gen_init crate) to emit the new form. All gen_* files are auto-generated and will be regenerated.

---
Change 2 — LeanObject.other: u8 → typed accessor methods

The other byte is multipurpose (num_objs for ctors, elem_size for sarray, 0 for everything else). Keep the stored field as u8 but add typed accessor methods kind of matching C++ names from origin-master-src/include/lean/lean.h:

File: src/rust/leanh_l1/src/datatypes.rs (in impl LeanObject)

pub fn lean_ptr_other__ctor_num_objs(&self) -> u8 {
    debug_assert!(matches!(self.tag, LeanObjectTag::Ctor(_)));
    self.other
}
pub fn lean_ptr_other__sarray_elem_size(&self) -> u8 {
    debug_assert!(matches!(self.tag, LeanObjectTag::ScalarArray));
    self.other
}

pub fn lean_ctor_num_objs(&self) -> u8 {
    debug_assert!(matches!(self.tag, LeanObjectTag::Ctor(_)));
    self.other
}

pub fn lean_sarray_elem_size(&self) -> u8 {
    debug_assert!(matches!(self.tag, LeanObjectTag::ScalarArray));
    self.other
}

Update all runtime call sites that do raw (*obj).other as usize to use these named methods.
Keep pub other: u8 visible for the gen_* emitted code that still sets it directly.

---
Change 3 — lean_util_lbool_name parameter → LBool enum

File: src/rust/runtime/src/base.rs

The C++ code uses magic values -1 / 0 / 1 (false / undef / true). Define a typed enum:

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LBool {
    False = -1,
    Undef = 0,
    True = 1,
}

pub fn lean_util_lbool_name(value: LBool) -> *const c_char {
    match value {
        LBool::False => c"l_false".as_ptr(),
        LBool::True  => c"l_true".as_ptr(),
        LBool::Undef => c"l_undef".as_ptr(),
    }
}

Call sites that pass raw i32 get a From<i32> impl that panics on unknown values (matching C++ behavior — C++ has no bounds check either).

---
Change 4 — OleanVersion enum

File: src/rust/runtime/src/runtime_expr_shared.rs

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum OleanVersion { V2, V3 }

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

Remove OLEAN_VERSION_V2 / OLEAN_VERSION_V3 constants.
Update library_module.rs (~line 481, 551) and runtime_compact_writer.rs (~lines 609, 652, 654) to call OleanVersion::from_u8(version_byte) and match on the enum.

---
Change 5 — Remove repr(C) from Rust-internal structs

With no C++ backward-compat requirement, strip repr(C) from ALL structs in leanh_l1/datatypes.rs and runtime/:

- LeanObject, LeanCtorObject, LeanClosureObject, LeanArrayObject, LeanStringObject, LeanScalarArray, LeanExternalObject, LeanMpzObject, LeanExternalClass
- LeanThunkObject, LeanRefObject, LeanTaskObject, LeanPromiseObject, LeanTaskImp
- LeanOnceCell (covered in Change 1)

Do this in a single commit after all other changes compile successfully.

---
Execution Order

1. Change 4 — OleanVersion (self-contained, no emitted-code impact) → build check
2. Change 3 — LBool (one call site) → build check
3. Change 1 — LeanOnceCell + add atomic_enum dep → update emitted initializers → build check
4. Change 2 — lean_ptr_other / lean_ctor_num_objs / lean_sarray_elem_size accessors → update all call sites → build check
5. Change 5 — strip all repr(C) → build check

---
Verification

After each change:
make -C build/release lean_runtime_rust -j$(nproc) 2>&1 | grep -i "^error" | head -20

Focused tests after all changes complete:
log="/tmp/lean4-test-$(date +%Y%m%d-%H%M%S).log"
CTEST_PARALLEL_LEVEL=$(nproc) make -C build/release test -j$(nproc) \
  ARGS='-R "tests/lake/examples/ffi|tests/lake/examples/reverse-ffi|misc_dir/plugin|compiler/strictAndOr|compiler/thunk" --timeout 240 --output-on-failure' \
  2>&1 | tee "$log" | grep -A5 -B20 -Ei 'fail(ed|ure)?'

---
Out of Scope (Follow-Up)

- Replace all C strings (*const c_char) with Rust &str / String — separate task after this lands.
