use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Util.lean

pub fn lean_dbg_trace(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_dbg_trace");
}

pub fn lean_dbg_trace_if_shared(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_dbg_trace_if_shared");
}

pub fn lean_dbg_stack_trace(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_dbg_stack_trace");
}

pub fn lean_dbg_sleep(_: u32, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_dbg_sleep");
}

pub fn lean_ptr_addr(obj: *mut LeanObject) -> usize {
    obj as usize
}

pub fn lean_is_exclusive_obj(_: *mut LeanObject) -> u8 {
    todo!("Stub for lean_is_exclusive_obj");
}
