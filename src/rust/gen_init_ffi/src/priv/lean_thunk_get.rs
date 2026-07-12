use std::sync::atomic::Ordering;

use leanh_l1::datatypes::{LeanObject, LeanThunkObject};

use crate::r#priv::lean_thunk_get_core::lean_thunk_get_core;

#[inline]
pub unsafe fn lean_thunk_get(thunk: *mut LeanObject) -> *mut LeanObject {
    let value = (*(thunk as *mut LeanThunkObject))
        .m_value
        .load(Ordering::Acquire);
    if !value.is_null() {
        return value;
    }
    lean_thunk_get_core(thunk)
}
