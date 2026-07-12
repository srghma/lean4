use crate::{datatypes::LeanObject, r#priv::lean_is_st::lean_is_st};

#[inline]
pub unsafe fn lean_is_shared(obj: *const LeanObject) -> bool {
    // TODO: use likely
    if lean_is_st(obj) {
        (*obj).rc > 1
    } else {
        false
    }
}
