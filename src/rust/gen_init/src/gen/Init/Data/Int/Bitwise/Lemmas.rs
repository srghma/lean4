// Lean compiler output
// Module: Init.Data.Int.Bitwise.Lemmas
// Imports: Init.Data.Int.Bitwise.Basic Init.Data.Int.Bitwise.Basic Init.Data.Int.DivMod.Basic Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Bitwise.Lemmas Init.Data.Nat.Lemmas Init.Omega Init.RCases
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Bitwise::Basic::{
    initialize_Init_Data_Int_Bitwise_Basic, runtime_initialize_Init_Data_Int_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Lemmas::{
    initialize_Init_Data_Nat_Bitwise_Lemmas, runtime_initialize_Init_Data_Nat_Bitwise_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
static mut l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_39_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_40_ = lean_nat_to_int(v_natZero_39_);
    return v_intZero_40_;
}
pub unsafe fn l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(
    mut v_x_41_: *mut crate::leanh::LeanObject,
    mut v_x_42_: *mut crate::leanh::LeanObject,
    mut v_h__1_43_: *mut crate::leanh::LeanObject,
    mut v_h__2_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_46_: u8 = 0;
    v_intZero_45_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0);
    v_isNeg_46_ = lean_int_dec_lt(v_x_41_, v_intZero_45_);
    if v_isNeg_46_ == 0 {
        let mut v_a_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_44_);
        v_a_47_ = lean_nat_abs(v_x_41_);
        v___x_48_ = crate::leanh::lean_apply_2(v_h__1_43_, v_a_47_, v_x_42_);
        return v___x_48_;
    } else {
        let mut v_abs_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_43_);
        v_abs_49_ = lean_nat_abs(v_x_41_);
        v_one_50_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_51_ = lean_nat_sub(v_abs_49_, v_one_50_);
        crate::leanh::lean_dec(v_abs_49_);
        v___x_52_ = crate::leanh::lean_apply_2(v_h__2_44_, v_a_51_, v_x_42_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___boxed(
    mut v_x_53_: *mut crate::leanh::LeanObject,
    mut v_x_54_: *mut crate::leanh::LeanObject,
    mut v_h__1_55_: *mut crate::leanh::LeanObject,
    mut v_h__2_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ =
        l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(
            v_x_53_, v_x_54_, v_h__1_55_, v_h__2_56_,
        );
    crate::leanh::lean_dec(v_x_53_);
    return v_res_57_;
}
pub unsafe fn l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(
    mut v_motive_58_: *mut crate::leanh::LeanObject,
    mut v_x_59_: *mut crate::leanh::LeanObject,
    mut v_x_60_: *mut crate::leanh::LeanObject,
    mut v_h__1_61_: *mut crate::leanh::LeanObject,
    mut v_h__2_62_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_64_: u8 = 0;
    v_intZero_63_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0);
    v_isNeg_64_ = lean_int_dec_lt(v_x_59_, v_intZero_63_);
    if v_isNeg_64_ == 0 {
        let mut v_a_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_62_);
        v_a_65_ = lean_nat_abs(v_x_59_);
        v___x_66_ = crate::leanh::lean_apply_2(v_h__1_61_, v_a_65_, v_x_60_);
        return v___x_66_;
    } else {
        let mut v_abs_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_61_);
        v_abs_67_ = lean_nat_abs(v_x_59_);
        v_one_68_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_69_ = lean_nat_sub(v_abs_67_, v_one_68_);
        crate::leanh::lean_dec(v_abs_67_);
        v___x_70_ = crate::leanh::lean_apply_2(v_h__2_62_, v_a_69_, v_x_60_);
        return v___x_70_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___boxed(
    mut v_motive_71_: *mut crate::leanh::LeanObject,
    mut v_x_72_: *mut crate::leanh::LeanObject,
    mut v_x_73_: *mut crate::leanh::LeanObject,
    mut v_h__1_74_: *mut crate::leanh::LeanObject,
    mut v_h__2_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(
        v_motive_71_,
        v_x_72_,
        v_x_73_,
        v_h__1_74_,
        v_h__2_75_,
    );
    crate::leanh::lean_dec(v_x_72_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Bitwise_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Bitwise_Lemmas(
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
pub unsafe fn initialize_Init_Data_Int_Bitwise_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
}
