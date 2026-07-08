use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set},
};

const OPTION_SOME_TAG: u32 = 1;
const OPTION_SOME_FIELDS: u32 = 1;
const OPTION_SOME_SCALAR_SIZE: u32 = 0;
pub(crate) unsafe fn mk_option_some(v: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(OPTION_SOME_TAG, OPTION_SOME_FIELDS, OPTION_SOME_SCALAR_SIZE);
    lean_ctor_set(obj, 0, v);
    obj
}
