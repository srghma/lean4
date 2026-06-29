// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:30-45
// exact-text variant: no

use crate::leanh::*;
use crate::leanh;

pub unsafe fn lean_string_utf8_extract(
    s: *mut LeanObject,
    begin: *mut LeanObject,
    end: *mut LeanObject,
) -> *mut LeanObject {
    let begin = unsafe { lean_unbox(begin) };
    let end = unsafe { lean_unbox(end) };
    let len = end.saturating_sub(begin);
    unsafe {
        let data = (*(s as *mut LeanStringObject<0>))
            .m_data
            .as_ptr()
            .add(begin);
        lean_mk_string_unchecked(data.cast(), len, len)
    }
}
