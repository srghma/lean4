// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:614-644

use std::{
    ptr,
    sync::atomic::{AtomicI32, Ordering},
};

use crate::{
    datatypes::LeanObject,
    emitted::lean_is_scalar::lean_is_scalar,
    r#priv::{lean_del_core::lean_del_core, pop_back::pop_back},
};

// NOT IN EmitRust; here because it is used in `lean_apply_m`, `lean_ctor_release`, `lean_dec`, `lean_dec_ref`, and 1 more EmitRust functions.
pub unsafe fn lean_dec_ref_cold(mut o: *mut LeanObject) {
    if lean_is_scalar(o) {
        return;
    }
    if (*o).rc == 1 || {
        let rc = core::ptr::addr_of_mut!((*o).rc).cast::<AtomicI32>();
        (*rc).fetch_add(1, Ordering::AcqRel) == -1
    } {
        let mut todo = ptr::null_mut();
        loop {
            lean_del_core(o, &mut todo);
            if todo.is_null() {
                return;
            }
            o = pop_back(&mut todo);
        }
    }
}
