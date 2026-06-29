// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
// Imports: Std.Sat.AIG.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::l_Nat_testBit;
use crate::r#gen::Init::Data::RArray::l_Lean_RArray_getImpl___redArg;
use crate::r#gen::Std::Sat::AIG::Basic::{
    initialize_Std_Sat_AIG_Basic, runtime_initialize_Std_Sat_AIG_Basic,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(
    mut v_assign_12_: *mut crate::leanh::LeanObject,
    mut v_bit_13_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_var_14_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_15_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18_: u8 = 0;
    v_var_14_ = crate::leanh::lean_ctor_get(v_bit_13_, 0);
    v_idx_15_ = crate::leanh::lean_ctor_get(v_bit_13_, 2);
    v___x_16_ = l_Lean_RArray_getImpl___redArg(v_assign_12_, v_var_14_);
    v_bv_17_ = crate::leanh::lean_ctor_get(v___x_16_, 1);
    crate::leanh::lean_inc(v_bv_17_);
    crate::leanh::lean_dec(v___x_16_);
    v___x_18_ = l_Nat_testBit(v_bv_17_, v_idx_15_);
    crate::leanh::lean_dec(v_bv_17_);
    return v___x_18_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment___boxed(
    mut v_assign_19_: *mut crate::leanh::LeanObject,
    mut v_bit_20_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_21_: u8 = 0;
    let mut v_r_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_21_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(v_assign_19_, v_bit_20_);
    crate::leanh::lean_dec_ref(v_bit_20_);
    crate::leanh::lean_dec_ref(v_assign_19_);
    v_r_22_ = crate::leanh::lean_box((v_res_21_) as usize);
    return v_r_22_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
}
