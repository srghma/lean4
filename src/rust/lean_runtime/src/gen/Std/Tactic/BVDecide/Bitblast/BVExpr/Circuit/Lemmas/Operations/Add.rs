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
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(
    mut v_val_26_: *mut crate::leanh::LeanObject,
    mut v_h__1_27_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_28_ = crate::leanh::lean_ctor_get(v_val_26_, 0);
    crate::leanh::lean_inc_ref(v_lhs_28_);
    v_rhs_29_ = crate::leanh::lean_ctor_get(v_val_26_, 1);
    crate::leanh::lean_inc_ref(v_rhs_29_);
    v_cin_30_ = crate::leanh::lean_ctor_get(v_val_26_, 2);
    crate::leanh::lean_inc_ref(v_cin_30_);
    crate::leanh::lean_dec_ref(v_val_26_);
    v___x_31_ = crate::leanh::lean_apply_3(v_h__1_27_, v_lhs_28_, v_rhs_29_, v_cin_30_);
    return v___x_31_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(
    mut v_00_u03b1_32_: *mut crate::leanh::LeanObject,
    mut v_inst_33_: *mut crate::leanh::LeanObject,
    mut v_inst_34_: *mut crate::leanh::LeanObject,
    mut v_aig1_35_: *mut crate::leanh::LeanObject,
    mut v_motive_36_: *mut crate::leanh::LeanObject,
    mut v_val_37_: *mut crate::leanh::LeanObject,
    mut v_h__1_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_39_ = crate::leanh::lean_ctor_get(v_val_37_, 0);
    crate::leanh::lean_inc_ref(v_lhs_39_);
    v_rhs_40_ = crate::leanh::lean_ctor_get(v_val_37_, 1);
    crate::leanh::lean_inc_ref(v_rhs_40_);
    v_cin_41_ = crate::leanh::lean_ctor_get(v_val_37_, 2);
    crate::leanh::lean_inc_ref(v_cin_41_);
    crate::leanh::lean_dec_ref(v_val_37_);
    v___x_42_ = crate::leanh::lean_apply_3(v_h__1_38_, v_lhs_39_, v_rhs_40_, v_cin_41_);
    return v___x_42_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(
    mut v_00_u03b1_43_: *mut crate::leanh::LeanObject,
    mut v_inst_44_: *mut crate::leanh::LeanObject,
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_aig1_46_: *mut crate::leanh::LeanObject,
    mut v_motive_47_: *mut crate::leanh::LeanObject,
    mut v_val_48_: *mut crate::leanh::LeanObject,
    mut v_h__1_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_43_, v_inst_44_, v_inst_45_, v_aig1_46_, v_motive_47_, v_val_48_, v_h__1_49_);
    crate::leanh::lean_dec_ref(v_aig1_46_);
    crate::leanh::lean_dec_ref(v_inst_45_);
    crate::leanh::lean_dec_ref(v_inst_44_);
    return v_res_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Add(builtin);
}
