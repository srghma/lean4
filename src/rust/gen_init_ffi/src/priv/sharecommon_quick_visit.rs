use leanh_l1::{
    datatypes::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG,
        LEAN_REF_TAG, LEAN_RESERVED_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
        LEAN_THUNK_TAG, LeanObject,
    },
    emitted::{lean_inc::lean_inc, lean_is_scalar::lean_is_scalar},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

use crate::r#priv::{
    sharecommon_quick_data::RustShareCommonQuick,
    sharecommon_quick_visit_array::sharecommon_quick_visit_array,
    sharecommon_quick_visit_ctor::sharecommon_quick_visit_ctor,
    sharecommon_quick_visit_terminal::sharecommon_quick_visit_terminal,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:124-144

pub(crate) unsafe fn sharecommon_quick_visit(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar(a) {
        return a;
    }
    match lean_ptr_tag(a) {
        LEAN_CLOSURE_TAG | LEAN_THUNK_TAG | LEAN_TASK_TAG | LEAN_PROMISE_TAG | LEAN_REF_TAG
        | LEAN_EXTERNAL_TAG | LEAN_RESERVED_TAG => {
            lean_inc(a);
            a
        }
        LEAN_MPZ_TAG | LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG => {
            sharecommon_quick_visit_terminal(this, a)
        }
        LEAN_ARRAY_TAG => sharecommon_quick_visit_array(this, a),
        _ => sharecommon_quick_visit_ctor(this, a),
    }
}
