// Lean compiler output
// Module: Std.Tactic.BVDecide.Normalize
// Imports: Std.Tactic.BVDecide.Normalize.BitVec Std.Tactic.BVDecide.Normalize.Bool Std.Tactic.BVDecide.Normalize.Canonicalize Std.Tactic.BVDecide.Normalize.Equal Std.Tactic.BVDecide.Normalize.Prop
use crate::r#gen::Std::Tactic::BVDecide::Normalize::BitVec::{
    initialize_Std_Tactic_BVDecide_Normalize_BitVec,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec,
};
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Bool::{
    initialize_Std_Tactic_BVDecide_Normalize_Bool,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool,
};
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Canonicalize::{
    initialize_Std_Tactic_BVDecide_Normalize_Canonicalize,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Canonicalize,
};
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Equal::{
    initialize_Std_Tactic_BVDecide_Normalize_Equal,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Equal,
};
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Prop::{
    initialize_Std_Tactic_BVDecide_Normalize_Prop,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Canonicalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Equal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Normalize(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Normalize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_Canonicalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_Equal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_Prop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Normalize(builtin);
}
