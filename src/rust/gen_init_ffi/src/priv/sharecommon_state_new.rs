use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc},
};

use crate::r#priv::sharecommon_data::ShareCommonState;

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:15-35

pub unsafe fn sharecommon_state_new(tc: *mut LeanObject, s: *mut LeanObject) -> ShareCommonState {
    let map_find = lean_ctor_get(tc, 1);
    let map_insert = lean_ctor_get(tc, 2);
    let set_find = lean_ctor_get(tc, 3);
    let set_insert = lean_ctor_get(tc, 4);
    let map = lean_ctor_get(s, 0);
    lean_inc(map);
    let set = lean_ctor_get(s, 1);
    lean_inc(set);
    lean_dec(s);
    ShareCommonState {
        map_find,
        map_insert,
        set_find,
        set_insert,
        map,
        set,
    }
}
