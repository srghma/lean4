// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith
// Imports: Lean.Meta.Tactic.Grind.Arith.Util Lean.Meta.Tactic.Grind.Arith.Types Lean.Meta.Tactic.Grind.Arith.Main Lean.Meta.Tactic.Grind.Arith.CommRing Lean.Meta.Tactic.Grind.Arith.Linear Lean.Meta.Tactic.Grind.Arith.Cutsat Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.Tactic.Grind.Arith.Propagate Lean.Meta.Tactic.Grind.Arith.Model
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Main::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Main,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Model,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Propagate::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Propagate,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Simproc::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Simproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
}
