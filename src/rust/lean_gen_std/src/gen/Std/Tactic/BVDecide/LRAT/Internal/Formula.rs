// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas Std.Tactic.BVDecide.LRAT.Internal.Formula.Class Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddResult Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Class::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Implementation::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Instance::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Lemmas::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RatAddResult::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RatAddSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RupAddResult::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RupAddSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
}
