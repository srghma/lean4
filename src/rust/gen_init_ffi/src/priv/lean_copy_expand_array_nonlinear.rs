use leanh_l1::datatypes::LeanObject;

use crate::r#priv::lean_copy_expand_array::lean_copy_expand_array;

#[inline(never)]
pub unsafe fn lean_copy_expand_array_nonlinear(
    a: *mut LeanObject,
    expand: bool,
) -> *mut LeanObject {
    lean_copy_expand_array(a, expand)
}
