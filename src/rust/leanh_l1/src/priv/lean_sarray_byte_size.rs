// appended by move_rust_fn_to_leanh_l1.ts from ../lean4-rust/src/rust/lean_runtime/src/runtime_object_rc.rs:282-287

use crate::{
    datatypes::{LeanObject, LeanScalarArray},
    r#priv::{
        lean_sarray_capacity::lean_sarray_capacity, lean_sarray_elem_size::lean_sarray_elem_size,
    },
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_sarray_byte_size(obj: *const LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanScalarArray<0>>()
            + lean_sarray_elem_size(obj) * lean_sarray_capacity(obj)
    }
}
