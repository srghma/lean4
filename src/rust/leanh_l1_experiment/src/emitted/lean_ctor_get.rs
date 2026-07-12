use crate::{datatypes::LeanObject, r#priv::lean_ctor_num_objs::lean_ctor_num_objs};

#[inline]
pub unsafe fn lean_ctor_get(obj: *const LeanObject, idx: u32) -> *mut LeanObject {
    unsafe {
        debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
        (obj.add(1) as *const *mut LeanObject)
            .add(idx as usize)
            .read()
    }
}
