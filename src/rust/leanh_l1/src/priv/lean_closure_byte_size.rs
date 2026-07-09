use crate::{
    datatypes::{LeanClosureObject, LeanObject},
    r#priv::lean_closure_num_fixed::lean_closure_num_fixed,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_byte_size(obj: *const LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanClosureObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(obj)
    }
}
