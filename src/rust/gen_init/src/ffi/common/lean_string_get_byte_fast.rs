// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:107-116
// source: Init/Data/String/PosRaw.rs:6-15
// exact-text variant: yes

use runtime::leanh_extra::*;
use runtime::leanh_extra as leanh;

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
