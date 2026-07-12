use crate::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_dec_ref::lean_dec_ref,
        lean_del_object::lean_del_object, lean_is_exclusive::lean_is_exclusive,
    },
    r#priv::lean_is_ref::lean_is_ref,
};

// Mirrors origin-master-src/include/lean/lean.h:691-700 (`lean_dec_ref_known`).
#[inline]
pub unsafe fn lean_dec_ref_known(obj: *const LeanObject, objs: u32) {
    debug_assert!(lean_is_ref(obj));
    if lean_is_exclusive(obj) {
        for i in 0..objs {
            lean_dec(lean_ctor_get(obj, i));
        }
        lean_del_object(obj as *mut LeanObject);
    } else {
        lean_dec_ref(obj);
    }
}
