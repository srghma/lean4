// Lean compiler output
// Module: Init.Data.Nat.Coprime
// Imports: Init.Data.Nat.Gcd Init.Data.Nat.Dvd
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Nat::Gcd::{
    initialize_Init_Data_Nat_Gcd, runtime_initialize_Init_Data_Nat_Gcd,
};
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_eq;
pub unsafe fn l_Nat_instDecidableCoprime(
    mut v_m_10_: *mut crate::leanh::LeanObject,
    mut v_n_11_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_12_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_13_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14_: u8 = 0;
    v___x_12_ = lean_nat_gcd(v_m_10_, v_n_11_);
    v___x_13_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
    crate::leanh::lean_dec(v___x_12_);
    return v___x_14_;
}
pub unsafe fn l_Nat_instDecidableCoprime___boxed(
    mut v_m_15_: *mut crate::leanh::LeanObject,
    mut v_n_16_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_17_: u8 = 0;
    let mut v_r_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_17_ = l_Nat_instDecidableCoprime(v_m_15_, v_n_16_);
    crate::leanh::lean_dec(v_n_16_);
    crate::leanh::lean_dec(v_m_15_);
    v_r_18_ = crate::leanh::lean_box((v_res_17_) as usize);
    return v_r_18_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Coprime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Coprime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Coprime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Coprime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Coprime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Coprime(builtin);
}
