use crate::{datatypes::LeanObject, r#priv::set_next::set_next};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn push_back(todo: &mut *mut LeanObject, obj: *mut LeanObject) {
    unsafe {
        set_next(obj, *todo);
        *todo = obj;
    }
}
