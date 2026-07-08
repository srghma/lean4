use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

use crate::{
    datatypes::{
        LEAN_EXTERNAL_TAG, LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc,
        LeanExternalObject, LeanObject, LeanStringObject, Size,
    },
    not_in_emit_rust::lean_alloc_small_object,
};

static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());
unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

pub unsafe fn lean_register_external_class(
    finalize: Option<LeanExternalFinalizeProc>,
    foreach: Option<LeanExternalForeachProc>,
) -> *mut LeanExternalClass {
    let class = Box::into_raw(Box::new(LeanExternalClass {
        m_finalize: finalize.unwrap_or(lean_external_noop_finalize),
        m_foreach: foreach.unwrap_or(lean_external_noop_foreach),
    }));
    EXTERNAL_CLASSES.lock().unwrap().push(class as usize);
    class
}

pub unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let obj = lean_alloc_small_object(core::mem::size_of::<LeanExternalObject>())
        as *mut LeanExternalObject;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_EXTERNAL_TAG;
    (*obj).m_class = class;
    (*obj).m_data = data;
    obj as *mut LeanObject
}
