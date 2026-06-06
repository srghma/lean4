
#![allow(non_camel_case_types, non_snake_case)]
use crate::LeanObject;
type b_lean_obj_arg = *mut LeanObject;


#[no_mangle]
pub unsafe extern "C" fn lean_int_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_sub(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_sub(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_mul(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_mul(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_div(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_div(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_mod(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_mod(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_ediv(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_ediv(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_ediv(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_emod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_emod(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_emod(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_div_exact(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    if crate::lean_is_scalar(a1) && crate::lean_is_scalar(a2) {
        // simplified logic for scalar ints - we delegate to big_int implementation for now for correctness
        crate::runtime_object_nat_int_impl::lean_int_big_div_exact(a1, a2)
    } else {
        crate::runtime_object_nat_int_impl::lean_int_big_div_exact(a1, a2)
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_div_exact(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    crate::runtime_object_nat_int_impl::lean_nat_big_div_exact(a1, a2)
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_land(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    crate::runtime_object_nat_int_impl::lean_nat_big_land(a1, a2)
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_lor(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    crate::runtime_object_nat_int_impl::lean_nat_big_lor(a1, a2)
}

#[no_mangle]
pub unsafe extern "C" fn lean_nat_lxor(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> *mut LeanObject {
    crate::runtime_object_nat_int_impl::lean_nat_big_xor(a1, a2)
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_dec_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> u8 {
    crate::runtime_object_nat_int_impl::lean_int_big_eq(a1, a2) as u8
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_dec_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> u8 {
    crate::runtime_object_nat_int_impl::lean_int_big_le(a1, a2) as u8
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_dec_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> u8 {
    crate::runtime_object_nat_int_impl::lean_int_big_lt(a1, a2) as u8
}

#[no_mangle]
pub unsafe extern "C" fn lean_int_dec_nonneg(a1: b_lean_obj_arg) -> u8 {
    crate::runtime_object_nat_int_impl::lean_int_big_nonneg(a1) as u8
}
#[no_mangle]
pub unsafe extern "C" fn lean_nat_pred(a1: b_lean_obj_arg) -> *mut LeanObject {
    crate::runtime_object_nat_int_impl::lean_nat_big_sub(a1, crate::lean_box(1))
}

#[no_mangle]
pub unsafe extern "C" fn lean_int8_of_nat(a: b_lean_obj_arg) -> i8 {
    if crate::lean_is_scalar(a) { crate::lean_unbox(a) as i8 } else { crate::runtime_object_nat_int_impl::lean_int8_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int8_of_int(a: b_lean_obj_arg) -> i8 {
    if crate::lean_is_scalar(a) { (crate::lean_unbox(a) as i32 as i64) as i8 } else { crate::runtime_object_nat_int_impl::lean_int8_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int8_to_int(a: i8) -> *mut LeanObject {
    crate::lean_int64_to_int_export(a as i64)
}

#[no_mangle]
pub unsafe extern "C" fn lean_int16_of_nat(a: b_lean_obj_arg) -> i16 {
    if crate::lean_is_scalar(a) { crate::lean_unbox(a) as i16 } else { crate::runtime_object_nat_int_impl::lean_int16_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int16_of_int(a: b_lean_obj_arg) -> i16 {
    if crate::lean_is_scalar(a) { (crate::lean_unbox(a) as i32 as i64) as i16 } else { crate::runtime_object_nat_int_impl::lean_int16_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int16_to_int(a: i16) -> *mut LeanObject {
    crate::lean_int64_to_int_export(a as i64)
}

#[no_mangle]
pub unsafe extern "C" fn lean_int32_of_nat(a: b_lean_obj_arg) -> i32 {
    if crate::lean_is_scalar(a) { crate::lean_unbox(a) as i32 } else { crate::runtime_object_nat_int_impl::lean_int32_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int32_of_int(a: b_lean_obj_arg) -> i32 {
    if crate::lean_is_scalar(a) { (crate::lean_unbox(a) as i32 as i64) as i32 } else { crate::runtime_object_nat_int_impl::lean_int32_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int32_to_int(a: i32) -> *mut LeanObject {
    crate::lean_int64_to_int_export(a as i64)
}

#[no_mangle]
pub unsafe extern "C" fn lean_int64_of_nat(a: b_lean_obj_arg) -> i64 {
    if crate::lean_is_scalar(a) { crate::lean_unbox(a) as i64 } else { crate::runtime_object_nat_int_impl::lean_int64_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_int64_of_int(a: b_lean_obj_arg) -> i64 {
    if crate::lean_is_scalar(a) { (crate::lean_unbox(a) as i32 as i64) as i64 } else { crate::runtime_object_nat_int_impl::lean_int64_of_big_int(a) }
}


#[no_mangle]
pub unsafe extern "C" fn lean_isize_of_nat(a: b_lean_obj_arg) -> isize {
    if crate::lean_is_scalar(a) { crate::lean_unbox(a) as isize } else { crate::runtime_object_nat_int_impl::lean_isize_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_isize_of_int(a: b_lean_obj_arg) -> isize {
    if crate::lean_is_scalar(a) { (crate::lean_unbox(a) as i32 as i64) as isize } else { crate::runtime_object_nat_int_impl::lean_isize_of_big_int(a) }
}
#[no_mangle]
pub unsafe extern "C" fn lean_isize_to_int(a: isize) -> *mut LeanObject {
    crate::lean_int64_to_int_export(a as i64)
}

#[no_mangle]
pub unsafe extern "C" fn lean_int64_to_int_sint(a: i64) -> *mut LeanObject {
    crate::lean_int64_to_int_export(a)
}
