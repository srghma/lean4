use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_is_exclusive(obj: *const LeanObject) -> bool {
    // This was slower
    // !lean_is_scalar(obj) && (*obj).rc == 1

    // if ::std::intrinsics::likely(lean_is_st(obj)) {
    unsafe { (*obj).rc == 1 }
    // } else {
    //     false
    // }
}
