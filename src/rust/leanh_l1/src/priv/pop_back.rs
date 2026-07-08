use crate::{datatypes::LeanObject, r#priv::get_next::get_next};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject {
    unsafe {
        let result = *todo;
        *todo = get_next(result);
        result
    }
}
