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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_div};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Nat_gcd___boxed(
    mut v_m_31_: *mut LeanObject,
    mut v_n_32_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_33_: *mut LeanObject = core::ptr::null_mut();
    v_res_33_ = lean_nat_gcd(v_m_31_, v_n_32_);
    lean_dec(v_n_32_);
    lean_dec(v_m_31_);
    return v_res_33_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___redArg(
    mut v_k_34_: *mut LeanObject,
    mut v_m_35_: *mut LeanObject,
    mut v_n_36_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_39_: u8 = 0;
    v___x_37_ = lean_nat_gcd(v_k_34_, v_m_35_);
    v___x_38_ = lean_unsigned_to_nat(0);
    v___x_39_ = lean_nat_dec_eq(v___x_37_, v___x_38_);
    if v___x_39_ == 0 {
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_n_36_);
        v___x_40_ = lean_nat_div(v_k_34_, v___x_37_);
        v___x_41_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_41_, 0, v___x_37_);
        lean_ctor_set(v___x_41_, 1, v___x_40_);
        return v___x_41_;
    } else {
        let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_37_);
        v___x_42_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_42_, 0, v___x_38_);
        lean_ctor_set(v___x_42_, 1, v_n_36_);
        return v___x_42_;
    }
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___redArg___boxed(
    mut v_k_43_: *mut LeanObject,
    mut v_m_44_: *mut LeanObject,
    mut v_n_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_46_: *mut LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_43_, v_m_44_, v_n_45_);
    lean_dec(v_m_44_);
    lean_dec(v_k_43_);
    return v_res_46_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd(
    mut v_k_47_: *mut LeanObject,
    mut v_m_48_: *mut LeanObject,
    mut v_n_49_: *mut LeanObject,
    mut v_h_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v_k_47_, v_m_48_, v_n_49_);
    return v___x_51_;
}
pub unsafe fn l_Nat_dvdProdDvdOfDvdProd___boxed(
    mut v_k_52_: *mut LeanObject,
    mut v_m_53_: *mut LeanObject,
    mut v_n_54_: *mut LeanObject,
    mut v_h_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Nat_dvdProdDvdOfDvdProd(v_k_52_, v_m_53_, v_n_54_, v_h_55_);
    lean_dec(v_m_53_);
    lean_dec(v_k_52_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_Gcd(builtin);
}
