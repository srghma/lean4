use crate::{
    datatypes::{LEAN_MAX_SMALL_NAT, LeanObject},
    emitted::lean_box::lean_box,
    runtime_mpz::uninit_mpzt,
    runtime_object_nat_int::mpz_to_nat_core,
};

// Mirrors origin-master-src/runtime/object.cpp:1363-1369 (`lean_big_usize_to_nat`).
// Reuses the shared mpz-to-Nat conversion path from lean_cstr_to_nat.
pub unsafe fn lean_big_usize_to_nat(n: usize) -> *mut LeanObject {
    if n <= LEAN_MAX_SMALL_NAT {
        return lean_box(n);
    }
    let mut m = uninit_mpzt();
    gmp_mpfr_sys::gmp::mpz_init_set_ui(&mut m, n as core::ffi::c_ulong);
    mpz_to_nat_core(&mut m)
}
