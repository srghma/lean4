use leanh_l1::{datatypes::LeanObject, emitted::lean_inc::lean_inc, runtime_apply::lean_apply_2};

use crate::r#priv::sharecommon_data::ShareCommonState;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:15-24

pub unsafe fn sharecommon_state_map_find(
    state: &ShareCommonState,
    k: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(state.map_find);
    lean_inc(state.map);
    lean_inc(k);
    lean_apply_2(state.map_find, state.map, k)
}
