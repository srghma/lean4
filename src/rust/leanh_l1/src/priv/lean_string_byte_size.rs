use crate::{
    datatypes::{LeanObject, LeanStringObject},
    r#priv::lean_string_capacity::lean_string_capacity,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_string_byte_size(obj: *const LeanObject) -> usize {
    unsafe { core::mem::size_of::<LeanStringObject<0>>() + lean_string_capacity(obj) }
}
