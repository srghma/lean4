use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_box::lean_box, lean_ctor_set::lean_ctor_set},
};

use crate::r#priv::sharecommon_data::ShareCommonState;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:15-30

pub(crate) unsafe fn sharecommon_state_pack(
    state: &mut ShareCommonState,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let pair_state = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair_state, 0, state.map);
    lean_ctor_set(pair_state, 1, state.set);
    state.map = lean_box(0);
    state.set = lean_box(0);

    let r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, pair_state);
    r
}
