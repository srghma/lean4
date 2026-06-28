// Lean compiler output
// Module: Init.Data.Nat.Gcd
// Imports: Init.NotationExtra Init.Data.Nat.Div.Basic Init.Data.Nat.Dvd Init.RCases Init.WFTactics
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_div};
pub unsafe fn l_Nat_gcd___boxed(
    mut v_m_31_: *mut crate::leanh::LeanObject,
    mut v_n_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_33_ = lean_nat_gcd(v_m_31_, v_n_32_);
    crate::leanh::lean_dec(v_n_32_);
    crate::leanh::lean_dec(v_m_31_);
    return v_res_33_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___redArg(
    mut v_k_34_: *mut crate::leanh::LeanObject,
    mut v_m_35_: *mut crate::leanh::LeanObject,
    mut v_n_36_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_39_: u8 = 0;
    v___x_37_ = lean_nat_gcd(v_k_34_, v_m_35_);
    v___x_38_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_39_ = lean_nat_dec_eq(v___x_37_, v___x_38_);
    if v___x_39_ == 0 {
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_n_36_);
        v___x_40_ = lean_nat_div(v_k_34_, v___x_37_);
        v___x_41_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_41_, 0, v___x_37_);
        crate::leanh::lean_ctor_set(v___x_41_, 1, v___x_40_);
        return v___x_41_;
    } else {
        let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_37_);
        v___x_42_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_42_, 0, v___x_38_);
        crate::leanh::lean_ctor_set(v___x_42_, 1, v_n_36_);
        return v___x_42_;
    }
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___redArg___boxed(
    mut v_k_43_: *mut crate::leanh::LeanObject,
    mut v_m_44_: *mut crate::leanh::LeanObject,
    mut v_n_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_43_, v_m_44_, v_n_45_);
    crate::leanh::lean_dec(v_m_44_);
    crate::leanh::lean_dec(v_k_43_);
    return v_res_46_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd(
    mut v_k_47_: *mut crate::leanh::LeanObject,
    mut v_m_48_: *mut crate::leanh::LeanObject,
    mut v_n_49_: *mut crate::leanh::LeanObject,
    mut v_h_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_47_, v_m_48_, v_n_49_);
    return v___x_51_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___boxed(
    mut v_k_52_: *mut crate::leanh::LeanObject,
    mut v_m_53_: *mut crate::leanh::LeanObject,
    mut v_n_54_: *mut crate::leanh::LeanObject,
    mut v_h_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Nat_dvdProdDvdOfDvdProd(v_k_52_, v_m_53_, v_n_54_, v_h_55_);
    crate::leanh::lean_dec(v_m_53_);
    crate::leanh::lean_dec(v_k_52_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Gcd(builtin);
}
