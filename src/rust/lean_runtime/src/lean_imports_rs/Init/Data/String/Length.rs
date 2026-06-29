use crate::leanh::*;

// Generated stub file for Lean FFI imports
// Source: src/Init/Data/String/Length.lean

pub unsafe fn lean_string_length(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box((*(s as *mut LeanStringObject<0>)).m_length) }
}
