use core::ffi::c_char;

use crate::{datatypes::LeanObject, runtime_mpz::uninit_mpzt, runtime_object_nat_int::mpz_to_nat};
use gmp_mpfr_sys::gmp::mpz_init_set_str;

// Mirrors origin-master-src/runtime/object.cpp:1352-1361 (`mpz_to_nat` + `lean_cstr_to_nat`).
pub unsafe fn lean_cstr_to_nat(n: *const c_char) -> *mut LeanObject {
    let mut m = uninit_mpzt();
    mpz_init_set_str(&mut m, n, 10);
    mpz_to_nat(&mut m)
}
