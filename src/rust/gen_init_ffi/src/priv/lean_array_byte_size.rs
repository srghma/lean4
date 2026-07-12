use leanh_l1::{
    datatypes::{LeanArrayObject, LeanObject},
    r#priv::lean_to_array::lean_to_array,
};

#[inline]
pub unsafe fn lean_array_byte_size(obj: *const LeanObject) -> usize {
    let obj = lean_to_array(obj);
    core::mem::size_of::<LeanArrayObject<0>>()
        + core::mem::size_of::<*mut LeanObject>() * unsafe { (*obj).m_capacity }
}
