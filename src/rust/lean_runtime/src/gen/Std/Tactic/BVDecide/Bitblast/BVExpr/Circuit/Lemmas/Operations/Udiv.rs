// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Sub Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.ZeroExtend Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Eq Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Ult Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.GetLsbD Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv Std.Tactic.BVDecide.Normalize.BitVec Init.ByCases Init.Data.Nat.Linear
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Sub::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Sub, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Sub};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::ZeroExtend::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ZeroExtend, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ZeroExtend};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Eq::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Eq, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Eq};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Ult::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Ult, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Ult};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::GetLsbD::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_GetLsbD, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_GetLsbD};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Udiv::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv};
use crate::r#gen::Std::Tactic::BVDecide::Normalize::BitVec::{initialize_Std_Tactic_BVDecide_Normalize_BitVec, runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Nat::Linear::{initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(
    mut v_curr_31_: *mut crate::leanh::LeanObject,
    mut v_h__1_32_: *mut crate::leanh::LeanObject,
    mut v_h__2_33_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_35_: u8 = 0;
    v_zero_34_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_35_ = lean_nat_dec_eq(v_curr_31_, v_zero_34_);
    if v_isZero_35_ == 1 {
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_33_);
        v___x_36_ = crate::leanh::lean_box(0);
        v___x_37_ = crate::leanh::lean_apply_1(v_h__1_32_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_one_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_32_);
        v_one_38_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_39_ = lean_nat_sub(v_curr_31_, v_one_38_);
        v___x_40_ = crate::leanh::lean_apply_1(v_h__2_33_, v_n_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(
    mut v_curr_41_: *mut crate::leanh::LeanObject,
    mut v_h__1_42_: *mut crate::leanh::LeanObject,
    mut v_h__2_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_41_, v_h__1_42_, v_h__2_43_);
    crate::leanh::lean_dec(v_curr_41_);
    return v_res_44_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(
    mut v_motive_45_: *mut crate::leanh::LeanObject,
    mut v_curr_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_50_: u8 = 0;
    v_zero_49_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_50_ = lean_nat_dec_eq(v_curr_46_, v_zero_49_);
    if v_isZero_50_ == 1 {
        let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v___x_51_ = crate::leanh::lean_box(0);
        v___x_52_ = crate::leanh::lean_apply_1(v_h__1_47_, v___x_51_);
        return v___x_52_;
    } else {
        let mut v_one_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v_one_53_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_54_ = lean_nat_sub(v_curr_46_, v_one_53_);
        v___x_55_ = crate::leanh::lean_apply_1(v_h__2_48_, v_n_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(
    mut v_motive_56_: *mut crate::leanh::LeanObject,
    mut v_curr_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
    mut v_h__2_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_56_, v_curr_57_, v_h__1_58_, v_h__2_59_);
    crate::leanh::lean_dec(v_curr_57_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Sub(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ZeroExtend(
            builtin,
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Eq(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Ult(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_GetLsbD(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Sub(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_ZeroExtend(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Eq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Ult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_GetLsbD(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(builtin);
}
