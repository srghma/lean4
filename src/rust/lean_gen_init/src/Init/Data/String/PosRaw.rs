use crate::leanh::*;

// Generated stub file for Lean FFI imports
// Source: src/Init/Data/String/PosRaw.lean

pub unsafe fn lean_string_get_byte_fast(s: *mut LeanObject, pos: *mut LeanObject) -> u8 {
    let pos = unsafe { lean_unbox(pos) };
    unsafe {
        (*(s as *mut LeanStringObject<0>))
            .m_data
            .as_ptr()
            .add(pos)
            .read()
    }
}
