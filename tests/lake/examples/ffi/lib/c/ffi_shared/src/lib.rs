use core::ffi::{c_char, c_void};

type LeanObj = *mut c_void;

extern "C" {
    fn lean_mk_string(s: *const c_char) -> LeanObj;
    // lean_alloc_object is LEAN_EXPORT (not static inline) so it's a real symbol
    fn lean_alloc_object(sz: usize) -> LeanObj;
}

// lean_object header layout (see lean/lean.h lean_object struct):
//   offset 0: m_rc     : i32  (4 bytes)
//   offset 4: m_cs_sz  : u16  (2 bytes)
//   offset 6: m_other  : u8   (1 byte)
//   offset 7: m_tag    : u8   (1 byte)
// total header: 8 bytes, then object fields follow
const LEAN_OBJ_HEADER_SIZE: usize = 8;

// Mirrors lean_io_result_mk_ok from lean/lean.h (which is static inline, so not a real symbol).
// Constructs Except.ok (tag=0, 1 object field, 0 scalar bytes).
unsafe fn lean_io_result_mk_ok(a: LeanObj) -> LeanObj {
    let o = lean_alloc_object(LEAN_OBJ_HEADER_SIZE + core::mem::size_of::<LeanObj>());
    *(o as *mut i32) = 1;                            // m_rc = 1
    *((o as *mut u8).add(4) as *mut u16) = 0;        // m_cs_sz = 0
    *((o as *mut u8).add(6)) = 1u8;                  // m_other = num_objs = 1
    *((o as *mut u8).add(7)) = 0u8;                  // m_tag = 0 (Except.ok)
    *((o as *mut u8).add(LEAN_OBJ_HEADER_SIZE) as *mut LeanObj) = a;
    o
}

#[no_mangle]
pub unsafe extern "C" fn my_lean_fun() -> LeanObj {
    let result = lean_mk_string(b"hi\0".as_ptr().cast());
    lean_io_result_mk_ok(result)
}
