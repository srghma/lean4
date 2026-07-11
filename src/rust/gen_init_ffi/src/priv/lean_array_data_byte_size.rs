use leanh_l1::{
    datatypes::{LeanArrayObject, LeanObject},
    r#priv::lean_array_size::lean_array_size,
};

#[inline]
pub unsafe fn lean_array_data_byte_size(obj: *const LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * lean_array_size(obj)
    }
}
