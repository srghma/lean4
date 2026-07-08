// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:276-281

use crate::datatypes::{LeanArrayObject, LeanObject};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject<0>;
    unsafe {
        core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * (*array).m_capacity
    }
}
