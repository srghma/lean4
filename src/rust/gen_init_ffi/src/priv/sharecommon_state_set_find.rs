use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_inc::lean_inc,
    runtime_apply::lean_apply_2,
};

use crate::r#priv::sharecommon_data::ShareCommonState;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:24-33

pub unsafe fn sharecommon_state_set_find(
    state: &ShareCommonState,
    o: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(state.set_find);
    lean_inc(state.set);
    lean_inc(o);
    lean_apply_2(state.set_find, state.set, o)
}
