// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Checker
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Convert Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
use crate::r#gen::Std::Sat::CNF::RelabelFin::l_Std_Sat_CNF_numLiterals;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CompactLRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
    l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CompactLRATCheckerSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Convert::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert,
    l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATChecker::l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATCheckerSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_check(
    mut v_lratProof_14_: *mut crate::leanh::LeanObject,
    mut v_cnf_15_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_internalFormula_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checkerResult_20_: u8 = 0;
    let mut v___x_21_: u8 = 0;
    let mut v___x_22_: u8 = 0;
    crate::leanh::lean_inc_ref(v_cnf_15_);
    v_internalFormula_16_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(v_cnf_15_);
    v___x_17_ = l_Std_Sat_CNF_numLiterals(v_cnf_15_);
    crate::leanh::lean_dec_ref(v_cnf_15_);
    v___x_18_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_19_ = lean_nat_add(v___x_17_, v___x_18_);
    crate::leanh::lean_dec(v___x_17_);
    v_checkerResult_20_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(
        v___x_19_,
        v_internalFormula_16_,
        v_lratProof_14_,
    );
    v___x_21_ = 0;
    v___x_22_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(v_checkerResult_20_, v___x_21_);
    return v___x_22_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_check___boxed(
    mut v_lratProof_23_: *mut crate::leanh::LeanObject,
    mut v_cnf_24_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_25_: u8 = 0;
    let mut v_r_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_25_ = l_Std_Tactic_BVDecide_LRAT_check(v_lratProof_23_, v_cnf_24_);
    crate::leanh::lean_dec_ref(v_lratProof_23_);
    v_r_26_ = crate::leanh::lean_box((v_res_25_) as usize);
    return v_r_26_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Checker(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Checker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
}
