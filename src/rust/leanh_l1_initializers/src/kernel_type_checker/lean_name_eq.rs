use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get::lean_ctor_get, lean_is_scalar::lean_is_scalar},
    r#priv::lean_ptr_tag::lean_ptr_tag,
};

use crate::{
    kernel_type_checker::lean_nat_eq::lean_nat_eq,
    runtime_object_name::{lean_name_hash_ptr::lean_name_hash_ptr, lean_string_eq::lean_string_eq},
};

#[inline(always)]
pub(crate) unsafe fn lean_name_eq(mut n1: *const LeanObject, mut n2: *const LeanObject) -> bool {
    if n1 == n2 {
        return true;
    }
    // If one is scalar (anonymous) and the other isn't, they differ.
    if lean_is_scalar(n1) != lean_is_scalar(n2) {
        return false;
    }
    // Both scalar but n1 != n2: can't happen for valid Names (anonymous = unique lean_box(0)).
    if lean_is_scalar(n1) {
        return false;
    }
    // Both non-scalar: fast-reject by cached hash.
    if lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2) {
        return false;
    }
    loop {
        debug_assert!(!lean_is_scalar(n1));
        debug_assert!(!lean_is_scalar(n2));
        if lean_ptr_tag(n1) != lean_ptr_tag(n2) {
            return false;
        }
        if lean_ptr_tag(n1) == 1 {
            // Name.str: field 1 is the string component
            if !lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
                return false;
            }
        } else {
            // Name.num: field 1 is the nat component
            if !lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
                return false;
            }
        }
        // Advance to prefix (field 0)
        n1 = lean_ctor_get(n1, 0);
        n2 = lean_ctor_get(n2, 0);
        if n1 == n2 {
            return true;
        }
        if lean_is_scalar(n1) != lean_is_scalar(n2) {
            return false;
        }
        // If both anonymous (scalar) but not equal — shouldn't happen for valid Names.
        if lean_is_scalar(n1) {
            return false;
        }
    }
}
