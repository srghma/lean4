use crate::{
    datatypes::LeanObject,
    r#priv::{lean_ctor_num_objs::lean_ctor_num_objs, lean_ctor_obj_cptr::lean_ctor_obj_cptr},
};

// Mirrors origin-master-src/include/lean/lean.h:703-706 (`lean_ctor_set`).
#[inline]
pub unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
    *lean_ctor_obj_cptr(obj).add(idx as usize) = value;
}
