use leanh_l1::{datatypes::LeanObject, emitted::lean_inc::lean_inc, runtime_apply::lean_apply_3};

use crate::r#priv::sharecommon_data::ShareCommonState;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:15-23

pub unsafe fn sharecommon_state_map_insert(
    state: &mut ShareCommonState,
    k: *mut LeanObject,
    v: *mut LeanObject,
) {
    lean_inc(state.map_insert);
    state.map = lean_apply_3(state.map_insert, state.map, k, v);
}
