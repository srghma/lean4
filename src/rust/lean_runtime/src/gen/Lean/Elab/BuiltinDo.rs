// Lean compiler output
// Module: Lean.Elab.BuiltinDo
// Imports: Lean.Elab.BuiltinDo.Basic Lean.Elab.BuiltinDo.Let Lean.Elab.BuiltinDo.Match Lean.Elab.BuiltinDo.MatchExpr Lean.Elab.BuiltinDo.If Lean.Elab.BuiltinDo.Jump Lean.Elab.BuiltinDo.Misc Lean.Elab.BuiltinDo.For Lean.Elab.BuiltinDo.TryCatch Lean.Elab.BuiltinDo.Repeat
use crate::r#gen::Lean::Elab::BuiltinDo::Basic::{
    initialize_Lean_Elab_BuiltinDo_Basic, runtime_initialize_Lean_Elab_BuiltinDo_Basic,
};
use crate::r#gen::Lean::Elab::BuiltinDo::For::{
    initialize_Lean_Elab_BuiltinDo_For, runtime_initialize_Lean_Elab_BuiltinDo_For,
};
use crate::r#gen::Lean::Elab::BuiltinDo::If::{
    initialize_Lean_Elab_BuiltinDo_If, runtime_initialize_Lean_Elab_BuiltinDo_If,
};
use crate::r#gen::Lean::Elab::BuiltinDo::Jump::{
    initialize_Lean_Elab_BuiltinDo_Jump, runtime_initialize_Lean_Elab_BuiltinDo_Jump,
};
use crate::r#gen::Lean::Elab::BuiltinDo::Let::{
    initialize_Lean_Elab_BuiltinDo_Let, runtime_initialize_Lean_Elab_BuiltinDo_Let,
};
use crate::r#gen::Lean::Elab::BuiltinDo::Match::{
    initialize_Lean_Elab_BuiltinDo_Match, runtime_initialize_Lean_Elab_BuiltinDo_Match,
};
use crate::r#gen::Lean::Elab::BuiltinDo::MatchExpr::{
    initialize_Lean_Elab_BuiltinDo_MatchExpr, runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr,
};
use crate::r#gen::Lean::Elab::BuiltinDo::Misc::{
    initialize_Lean_Elab_BuiltinDo_Misc, runtime_initialize_Lean_Elab_BuiltinDo_Misc,
};
use crate::r#gen::Lean::Elab::BuiltinDo::Repeat::{
    initialize_Lean_Elab_BuiltinDo_Repeat, runtime_initialize_Lean_Elab_BuiltinDo_Repeat,
};
use crate::r#gen::Lean::Elab::BuiltinDo::TryCatch::{
    initialize_Lean_Elab_BuiltinDo_TryCatch, runtime_initialize_Lean_Elab_BuiltinDo_TryCatch,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Jump(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Misc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Jump(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Misc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo(builtin);
}
