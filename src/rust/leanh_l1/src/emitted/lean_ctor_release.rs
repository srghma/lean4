use crate::{
    datatypes::LeanObject,
    emitted::{lean_box::lean_box, lean_dec::lean_dec},
    r#priv::{lean_ctor_num_objs::lean_ctor_num_objs, lean_ctor_obj_cptr::lean_ctor_obj_cptr},
};

// Mirrors origin-master-src/include/lean/lean.h:713-722 (`lean_ctor_release`).
#[inline]
pub unsafe fn lean_ctor_release(obj: *mut LeanObject, idx: u32) {
    debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
    let objs = lean_ctor_obj_cptr(obj);
    let slot = objs.add(idx as usize);
    lean_dec(*slot);
    *slot = lean_box(0);
}
