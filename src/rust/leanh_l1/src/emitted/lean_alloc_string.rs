// from runtime_object_string

use crate::{
    datatypes::{LeanObject, LeanObjectTag, LeanStringObject},
    r#priv::lean_alloc_object::lean_alloc_object,
};

#[inline]
pub unsafe fn lean_alloc_string(size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanStringObject<0>>()
        .checked_add(capacity)
        .expect("string allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanStringObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LeanObjectTag::String.as_u8();
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    (*obj).m_length = len;
    obj as *mut LeanObject
}
