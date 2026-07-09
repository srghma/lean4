use crate::{
    datatypes::LeanObject,
    r#priv::{lean_ctor_num_objs::lean_ctor_num_objs, lean_ctor_obj_cptr::lean_ctor_obj_cptr},
};

// Mirrors origin-master-src/include/lean/lean.h:744-747 (`lean_ctor_get_uint64`).
#[inline]
pub unsafe fn lean_ctor_get_uint64(obj: *const LeanObject, offset: u32) -> u64 {
    debug_assert!(
        (offset as usize) >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>()
    );
    *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset as usize)) as *const u64)
}
