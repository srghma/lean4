use leanh_l1::{
    datatypes::{LeanObject, LeanStringObject},
    r#priv::lean_string_size::lean_string_size,
};

#[inline]
pub unsafe fn lean_string_data_byte_size(obj: *const LeanObject) -> usize {
    unsafe { core::mem::size_of::<LeanStringObject<0>>() + lean_string_size(obj) }
}
