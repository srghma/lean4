use leanh_l1::{
    datatypes::{LeanExternalClass, LeanExternalObject, LeanObject, LeanObjectTag},
    r#priv::lean_alloc_small_object::lean_alloc_small_object,
};
use std::ffi::c_void;

pub unsafe fn lean_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let obj = lean_alloc_small_object(core::mem::size_of::<LeanExternalObject>())
        as *mut LeanExternalObject;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.set_tag(LeanObjectTag::External);
    (*obj).m_class = class;
    (*obj).m_data = data;
    obj as *mut LeanObject
}
