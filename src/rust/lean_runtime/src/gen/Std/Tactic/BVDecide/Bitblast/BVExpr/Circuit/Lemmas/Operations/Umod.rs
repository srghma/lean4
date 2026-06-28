// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Umod
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Udiv::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Umod::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Operations::Udiv::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(
    mut v_curr_31_: *mut LeanObject,
    mut v_h__1_32_: *mut LeanObject,
    mut v_h__2_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_35_: u8 = 0;
    v_zero_34_ = lean_unsigned_to_nat(0);
    v_isZero_35_ = lean_nat_dec_eq(v_curr_31_, v_zero_34_);
    if v_isZero_35_ == 1 {
        let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_33_);
        v___x_36_ = lean_box(0);
        v___x_37_ = lean_apply_1(v_h__1_32_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_one_38_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_39_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_32_);
        v_one_38_ = lean_unsigned_to_nat(1);
        v_n_39_ = lean_nat_sub(v_curr_31_, v_one_38_);
        v___x_40_ = lean_apply_1(v_h__2_33_, v_n_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(
    mut v_curr_41_: *mut LeanObject,
    mut v_h__1_42_: *mut LeanObject,
    mut v_h__2_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_44_: *mut LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_41_, v_h__1_42_, v_h__2_43_);
    lean_dec(v_curr_41_);
    return v_res_44_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(
    mut v_motive_45_: *mut LeanObject,
    mut v_curr_46_: *mut LeanObject,
    mut v_h__1_47_: *mut LeanObject,
    mut v_h__2_48_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_49_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_50_: u8 = 0;
    v_zero_49_ = lean_unsigned_to_nat(0);
    v_isZero_50_ = lean_nat_dec_eq(v_curr_46_, v_zero_49_);
    if v_isZero_50_ == 1 {
        let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_48_);
        v___x_51_ = lean_box(0);
        v___x_52_ = lean_apply_1(v_h__1_47_, v___x_51_);
        return v___x_52_;
    } else {
        let mut v_one_53_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_54_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_47_);
        v_one_53_ = lean_unsigned_to_nat(1);
        v_n_54_ = lean_nat_sub(v_curr_46_, v_one_53_);
        v___x_55_ = lean_apply_1(v_h__2_48_, v_n_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(
    mut v_motive_56_: *mut LeanObject,
    mut v_curr_57_: *mut LeanObject,
    mut v_h__1_58_: *mut LeanObject,
    mut v_h__2_59_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_60_: *mut LeanObject = core::ptr::null_mut();
    v_res_60_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_56_, v_curr_57_, v_h__1_58_, v_h__2_59_);
    lean_dec(v_curr_57_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Udiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Umod(builtin);
}
