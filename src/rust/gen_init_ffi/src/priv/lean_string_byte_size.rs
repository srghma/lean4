use leanh_l1::{
    datatypes::{LeanObject, LeanStringObject},
    r#priv::lean_to_string::lean_to_string,
};

#[inline]
pub unsafe fn lean_string_byte_size(obj: *const LeanObject) -> usize {
    let obj = lean_to_string(obj);
    core::mem::size_of::<LeanStringObject<0>>() + unsafe { (*obj).m_capacity }
}
