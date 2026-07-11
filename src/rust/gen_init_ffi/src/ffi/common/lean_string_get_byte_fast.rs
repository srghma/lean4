// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:107-116
// source: Init/Data/String/PosRaw.rs:6-15
// exact-text variant: yes

use leanh_l1::{
    datatypes::{LeanObject, LeanStringObject},
    emitted::lean_unbox::lean_unbox,
};

// TODO: does it match
//
// static inline uint8_t lean_string_get_byte_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
//   char const * str = lean_string_cstr(s);
//   size_t idx = lean_unbox(i);
//   return str[idx];
// }
//
// ??
//
// use lean_string_cstr

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
