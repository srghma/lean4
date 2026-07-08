use crate::datatypes::{LeanObject, LeanStringObject};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject<0>;
    unsafe { core::mem::size_of::<LeanStringObject<0>>() + (*string).m_capacity }
}
