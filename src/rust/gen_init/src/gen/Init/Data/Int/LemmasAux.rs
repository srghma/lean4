// Lean compiler output
// Module: Init.Data.Int.LemmasAux
// Imports: Init.Data.Int.Lemmas Init.ByCases Init.Data.Int.Pow Init.Omega
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
static mut l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_35_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_36_ = lean_nat_to_int(v_natZero_35_);
    return v_intZero_36_;
}
pub unsafe fn l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg(
    mut v_x_37_: *mut crate::leanh::LeanObject,
    mut v_h__1_38_: *mut crate::leanh::LeanObject,
    mut v_h__2_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_41_: u8 = 0;
    v_intZero_40_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_41_ = lean_int_dec_lt(v_x_37_, v_intZero_40_);
    if v_isNeg_41_ == 0 {
        let mut v_a_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_39_);
        v_a_42_ = lean_nat_abs(v_x_37_);
        v___x_43_ = crate::leanh::lean_apply_1(v_h__1_38_, v_a_42_);
        return v___x_43_;
    } else {
        let mut v_abs_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_38_);
        v_abs_44_ = lean_nat_abs(v_x_37_);
        v_one_45_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_46_ = lean_nat_sub(v_abs_44_, v_one_45_);
        crate::leanh::lean_dec(v_abs_44_);
        v___x_47_ = crate::leanh::lean_apply_1(v_h__2_39_, v_a_46_);
        return v___x_47_;
    }
}
pub unsafe fn l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___boxed(
    mut v_x_48_: *mut crate::leanh::LeanObject,
    mut v_h__1_49_: *mut crate::leanh::LeanObject,
    mut v_h__2_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_51_ = l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg(
        v_x_48_, v_h__1_49_, v_h__2_50_,
    );
    crate::leanh::lean_dec(v_x_48_);
    return v_res_51_;
}
pub unsafe fn l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter(
    mut v_motive_52_: *mut crate::leanh::LeanObject,
    mut v_x_53_: *mut crate::leanh::LeanObject,
    mut v_h__1_54_: *mut crate::leanh::LeanObject,
    mut v_h__2_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_57_: u8 = 0;
    v_intZero_56_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_57_ = lean_int_dec_lt(v_x_53_, v_intZero_56_);
    if v_isNeg_57_ == 0 {
        let mut v_a_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_55_);
        v_a_58_ = lean_nat_abs(v_x_53_);
        v___x_59_ = crate::leanh::lean_apply_1(v_h__1_54_, v_a_58_);
        return v___x_59_;
    } else {
        let mut v_abs_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_54_);
        v_abs_60_ = lean_nat_abs(v_x_53_);
        v_one_61_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_62_ = lean_nat_sub(v_abs_60_, v_one_61_);
        crate::leanh::lean_dec(v_abs_60_);
        v___x_63_ = crate::leanh::lean_apply_1(v_h__2_55_, v_a_62_);
        return v___x_63_;
    }
}
pub unsafe fn l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter___boxed(
    mut v_motive_64_: *mut crate::leanh::LeanObject,
    mut v_x_65_: *mut crate::leanh::LeanObject,
    mut v_h__1_66_: *mut crate::leanh::LeanObject,
    mut v_h__2_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_68_ = l___private_Init_Data_Int_LemmasAux_0__Int_toNat_match__1_splitter(
        v_motive_64_,
        v_x_65_,
        v_h__1_66_,
        v_h__2_67_,
    );
    crate::leanh::lean_dec(v_x_65_);
    return v_res_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_LemmasAux(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_LemmasAux(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_LemmasAux(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_LemmasAux(builtin);
}
