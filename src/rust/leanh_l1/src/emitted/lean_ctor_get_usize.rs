use crate::{
    datatypes::LeanObject,
    r#priv::{lean_ctor_num_objs::lean_ctor_num_objs, lean_ctor_obj_cptr::lean_ctor_obj_cptr},
};

// Mirrors origin-master-src/include/lean/lean.h:759-762 (`lean_ctor_get_usize`).
#[inline]
pub unsafe fn lean_ctor_get_usize(obj: *mut LeanObject, idx: u32) -> usize {
    debug_assert!((idx as usize) >= lean_ctor_num_objs(obj));
    *((lean_ctor_obj_cptr(obj).add(idx as usize)) as *const usize)
}
