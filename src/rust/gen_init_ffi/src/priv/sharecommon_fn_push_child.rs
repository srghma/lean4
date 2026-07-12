use leanh_l1::{
    datatypes::{
        LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_RESERVED_TAG,
        LEAN_TASK_TAG, LEAN_THUNK_TAG, LeanObject,
    },
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec,
        lean_is_scalar::lean_is_scalar,
    },
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

use crate::r#priv::{
    sharecommon_data::ShareCommonFn, sharecommon_state_map_find::sharecommon_state_map_find,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:65-96

pub(crate) unsafe fn sharecommon_fn_push_child(
    this: &mut ShareCommonFn,
    a: *const LeanObject,
) -> bool {
    if lean_is_scalar(a) {
        this.children.push(a as *mut LeanObject);
        return true;
    }
    let tag = lean_ptr_tag(a);
    if tag == LEAN_RESERVED_TAG {
        panic!("unreachable");
    }
    if tag == LEAN_THUNK_TAG
        || tag == LEAN_TASK_TAG
        || tag == LEAN_REF_TAG
        || tag == LEAN_EXTERNAL_TAG
        || tag == LEAN_CLOSURE_TAG
        || tag == LEAN_PROMISE_TAG
    {
        this.children.push(a as *mut LeanObject);
        return true;
    }

    let o = sharecommon_state_map_find(&this.state, a as *mut LeanObject);
    if o != lean_box(0) {
        let r = lean_ctor_get(o, 0);
        this.children.push(r);
        lean_dec(o);
        return true;
    }

    this.todo.push(a as *mut LeanObject);
    false
}
