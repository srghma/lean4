use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag},
    emitted::{
        lean_box::lean_box, lean_ctor_get::lean_ctor_get, lean_dec::lean_dec,
        lean_is_scalar::lean_is_scalar,
    },
    emitted::lean_object_tag::lean_object_tag,
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
    match lean_object_tag(a) {
        LeanObjectTag::Reserved => panic!("unreachable"),
        LeanObjectTag::Thunk
        | LeanObjectTag::Task
        | LeanObjectTag::Ref
        | LeanObjectTag::External
        | LeanObjectTag::Closure
        | LeanObjectTag::Promise => {
            this.children.push(a as *mut LeanObject);
            return true;
        }
        LeanObjectTag::Ctor(_) | LeanObjectTag::StructArray => {}
        tag => panic!("unexpected LeanObjectTag in sharecommon_fn_push_child: {tag:?}"),
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
