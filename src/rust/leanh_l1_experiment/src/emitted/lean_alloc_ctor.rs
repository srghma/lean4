use crate::{
    datatypes::{LEAN_MAX_CTOR_FIELDS, LEAN_MAX_CTOR_SCALARS_SIZE, LeanCtorObject, LeanObject},
    r#priv::lean_alloc_ctor_memory::lean_alloc_ctor_memory,
};

#[inline]
pub unsafe fn lean_alloc_ctor<T: Into<crate::datatypes::LeanObjectTag>>(
    tag: T,
    num_objs: u32,
    scalar_size: u32,
) -> *mut LeanObject {
    unsafe {
        let tag = tag.into();
        debug_assert!(matches!(
            tag,
            crate::datatypes::LeanObjectTag::Ctor(_)
        ));
        debug_assert!(num_objs < LEAN_MAX_CTOR_FIELDS);
        debug_assert!(scalar_size < LEAN_MAX_CTOR_SCALARS_SIZE);
        let byte_size = core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * num_objs as usize
            + scalar_size as usize;
        let obj = lean_alloc_ctor_memory(byte_size) as *mut LeanCtorObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.other = num_objs as u8;
        (*obj).m_header.set_tag(tag);
        obj as *mut LeanObject
    }
}
