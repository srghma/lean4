use std::ffi::CStr;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_box::lean_box, lean_is_scalar::lean_is_scalar, lean_mk_string::lean_mk_string},
    r#priv::{lean_is_shared::lean_is_shared, lean_string_cstr::lean_string_cstr},
    runtime_apply::lean_apply_1,
};

use crate::r#priv::io_eprintln::io_eprintln;
// Generated stub file for Lean FFI imports
// Source: src/Init/Util.lean

pub unsafe fn lean_dbg_trace(msg: *mut LeanObject, action: *mut LeanObject) -> *mut LeanObject {
    io_eprintln(msg);
    lean_apply_1(action, lean_box(0))
}

pub unsafe fn lean_dbg_trace_if_shared(
    msg: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    if !lean_is_scalar(value) && lean_is_shared(value) {
        let suffix = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
        let text = std::ffi::CString::new(format!("shared RC {suffix}"))
            .expect("debug trace message has embedded NUL");
        io_eprintln(lean_mk_string(text.as_ptr()));
    }
    value
}

pub fn lean_dbg_stack_trace(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_dbg_stack_trace");
}

pub unsafe fn lean_dbg_sleep(ms: u32, action: *mut LeanObject) -> *mut LeanObject {
    std::thread::sleep(std::time::Duration::from_millis(ms as u64));
    lean_apply_1(action, lean_box(0))
}

pub fn lean_ptr_addr(obj: *mut LeanObject) -> usize {
    obj as usize
}

pub fn lean_is_exclusive_obj(_: *mut LeanObject) -> bool {
    todo!("Stub for lean_is_exclusive_obj");
}
