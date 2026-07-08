use std::sync::atomic::{AtomicI32, Ordering};

use crate::{
    datatypes::LeanObject, lean_is_scalar::lean_is_scalar_bool, r#priv::push_back::push_back,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn dec_for_del(o: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        if lean_is_scalar_bool(o) {
            return;
        }
        if (*o).rc > 1 {
            (*o).rc -= 1;
        } else if (*o).rc == 1 {
            push_back(todo, o);
        } else if (*o).rc == 0 {
        } else {
            let rc = core::ptr::addr_of_mut!((*o).rc).cast::<AtomicI32>();
            if (*rc).fetch_add(1, Ordering::AcqRel) == -1 {
                push_back(todo, o);
            }
        }
    }
}
