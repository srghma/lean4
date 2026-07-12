use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_inc_n::lean_inc_n,
    },
};

use crate::r#priv::{
    sharecommon_data::ShareCommonFn,
    sharecommon_state_map_insert::sharecommon_state_map_insert,
    sharecommon_state_set_find::sharecommon_state_set_find,
    sharecommon_state_set_insert::sharecommon_state_set_insert,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:39-64

pub(crate) unsafe fn sharecommon_fn_save(
    this: &mut ShareCommonFn,
    a: *mut LeanObject,
    mut new_a: *mut LeanObject,
) {
    assert!(!this.todo.is_empty());
    assert_eq!(this.todo.last().copied(), Some(a));
    this.todo.pop();

    let opt_new_r = sharecommon_state_set_find(&this.state, new_a);
    if opt_new_r != lean_box(0) {
        lean_dec(new_a);
        new_a = lean_ctor_get(opt_new_r, 0);
        lean_inc(new_a);
        lean_dec(opt_new_r);
        lean_inc(a);
        sharecommon_state_map_insert(&mut this.state, a, new_a);
    } else {
        lean_inc(a);
        lean_inc_n(new_a, 3);
        sharecommon_state_set_insert(&mut this.state, new_a);
        sharecommon_state_map_insert(&mut this.state, a, new_a);
        sharecommon_state_map_insert(&mut this.state, new_a, new_a);
    }
}
