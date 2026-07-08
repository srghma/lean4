use core::ffi::c_void;

use leanh_l1::datatypes::{
    LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc, LeanObject,
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
