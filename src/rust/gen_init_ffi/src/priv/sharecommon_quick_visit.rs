use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::{lean_inc::lean_inc, lean_is_scalar::lean_is_scalar},
    emitted::lean_object_tag::lean_object_tag,
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
    match lean_object_tag(a) {
        LeanObjectTag::Closure
        | LeanObjectTag::Thunk
        | LeanObjectTag::Task
        | LeanObjectTag::Promise
        | LeanObjectTag::Ref
        | LeanObjectTag::External
        | LeanObjectTag::Reserved => {
            lean_inc(a);
            a
        }
        LeanObjectTag::Mpz | LeanObjectTag::ScalarArray | LeanObjectTag::String => {
            sharecommon_quick_visit_terminal(this, a)
        }
        LeanObjectTag::Array => sharecommon_quick_visit_array(this, a),
        LeanObjectTag::Ctor(_) | LeanObjectTag::StructArray => sharecommon_quick_visit_ctor(this, a),
        tag => panic!("unexpected LeanObjectTag in sharecommon_quick_visit: {tag:?}"),
    }
}
