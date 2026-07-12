use leanh_l1::{
    datatypes::{LeanArrayObject, LeanObject, LeanObjectTag},
    r#priv::lean_alloc_object::lean_alloc_object,
};

pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanArrayObject<0>>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array allocation overflow"),
        )
        .expect("array allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LeanObjectTag::Array.as_u8();
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    obj as *mut LeanObject
}
