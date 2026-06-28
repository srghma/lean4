// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Add
// Imports: Init.Data.BitVec.Bitblast Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Init.Omega
use crate::r#gen::Init::Data::BitVec::Bitblast::{
    initialize_Init_Data_BitVec_Bitblast, runtime_initialize_Init_Data_BitVec_Bitblast,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_3, lean_box, lean_ctor_get, lean_dec_ref,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(
    mut v_val_26_: *mut LeanObject,
    mut v_h__1_27_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_28_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_28_ = lean_ctor_get(v_val_26_, 0);
    lean_inc_ref(v_lhs_28_);
    v_rhs_29_ = lean_ctor_get(v_val_26_, 1);
    lean_inc_ref(v_rhs_29_);
    v_cin_30_ = lean_ctor_get(v_val_26_, 2);
    lean_inc_ref(v_cin_30_);
    lean_dec_ref(v_val_26_);
    v___x_31_ = lean_apply_3(v_h__1_27_, v_lhs_28_, v_rhs_29_, v_cin_30_);
    return v___x_31_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(
    mut v_00_u03b1_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_inst_34_: *mut LeanObject,
    mut v_aig1_35_: *mut LeanObject,
    mut v_motive_36_: *mut LeanObject,
    mut v_val_37_: *mut LeanObject,
    mut v_h__1_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_39_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_39_ = lean_ctor_get(v_val_37_, 0);
    lean_inc_ref(v_lhs_39_);
    v_rhs_40_ = lean_ctor_get(v_val_37_, 1);
    lean_inc_ref(v_rhs_40_);
    v_cin_41_ = lean_ctor_get(v_val_37_, 2);
    lean_inc_ref(v_cin_41_);
    lean_dec_ref(v_val_37_);
    v___x_42_ = lean_apply_3(v_h__1_38_, v_lhs_39_, v_rhs_40_, v_cin_41_);
    return v___x_42_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(
    mut v_00_u03b1_43_: *mut LeanObject,
    mut v_inst_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
    mut v_aig1_46_: *mut LeanObject,
    mut v_motive_47_: *mut LeanObject,
    mut v_val_48_: *mut LeanObject,
    mut v_h__1_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_43_, v_inst_44_, v_inst_45_, v_aig1_46_, v_motive_47_, v_val_48_, v_h__1_49_);
    lean_dec_ref(v_aig1_46_);
    lean_dec_ref(v_inst_45_);
    lean_dec_ref(v_inst_44_);
    return v_res_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(builtin);
}
