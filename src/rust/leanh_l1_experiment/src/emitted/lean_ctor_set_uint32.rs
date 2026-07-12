use crate::{
    datatypes::LeanObject,
    r#priv::{lean_ctor_num_objs::lean_ctor_num_objs, lean_ctor_obj_cptr::lean_ctor_obj_cptr},
};

// Mirrors origin-master-src/include/lean/lean.h:774-777 (`lean_ctor_set_uint32`).
#[inline]
pub unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: u32, value: u32) {
    debug_assert!(
        (offset as usize) >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>()
    );
    *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset as usize)) as *mut u32) = value;
}
