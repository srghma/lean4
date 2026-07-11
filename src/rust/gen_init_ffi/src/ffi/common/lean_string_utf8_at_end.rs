// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:88-92
// source: Init/Data/String/Bootstrap.rs:73-77
// exact-text variant: yes

use leanh_l1::{
    datatypes::{LeanObject, LeanStringObject},
    emitted::{lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
};

pub unsafe fn lean_string_utf8_at_end(s: *mut LeanObject, pos: *mut LeanObject) -> bool {
    !lean_is_scalar(pos)
        || lean_unbox(pos) >= (*(s as *mut LeanStringObject<0>)).m_size.saturating_sub(1)
}
