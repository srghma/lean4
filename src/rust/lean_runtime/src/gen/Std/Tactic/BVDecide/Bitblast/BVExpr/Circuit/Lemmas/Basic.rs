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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(
    mut v_assign_12_: *mut LeanObject,
    mut v_bit_13_: *mut LeanObject,
) -> u8 {
    let mut v_var_14_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_15_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_16_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bv_17_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_18_: u8 = 0;
    v_var_14_ = lean_ctor_get(v_bit_13_, 0);
    v_idx_15_ = lean_ctor_get(v_bit_13_, 2);
    v___x_16_ = l_Lean_RArray_getImpl___redArg(v_assign_12_, v_var_14_);
    v_bv_17_ = lean_ctor_get(v___x_16_, 1);
    lean_inc(v_bv_17_);
    lean_dec(v___x_16_);
    v___x_18_ = l_Nat_testBit(v_bv_17_, v_idx_15_);
    lean_dec(v_bv_17_);
    return v___x_18_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment___boxed(
    mut v_assign_19_: *mut LeanObject,
    mut v_bit_20_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_21_: u8 = 0;
    let mut v_r_22_: *mut LeanObject = core::ptr::null_mut();
    v_res_21_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_toAIGAssignment(v_assign_19_, v_bit_20_);
    lean_dec_ref(v_bit_20_);
    lean_dec_ref(v_assign_19_);
    v_r_22_ = lean_box((v_res_21_) as usize);
    return v_r_22_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Basic(builtin);
}
