// Lean compiler output
// Module: Lean.Linter
// Imports: Lean.Linter.Util Lean.Linter.Builtin Lean.Linter.CheckUnivs Lean.Linter.ConstructorAsVariable Lean.Linter.DefProp Lean.Linter.Deprecated Lean.Linter.DocsOnAlt Lean.Linter.UnusedVariables Lean.Linter.MissingDocs Lean.Linter.Omit Lean.Linter.List Lean.Linter.Sets Lean.Linter.UnusedSimpArgs Lean.Linter.Coe Lean.Linter.GlobalAttributeIn Lean.Linter.EnvLinter Lean.Linter.PersistentLintLog Lean.Linter.Extra Lean.Linter.TacticTypeCheck
use crate::r#gen::Lean::Linter::Builtin::{
    initialize_Lean_Linter_Builtin, runtime_initialize_Lean_Linter_Builtin,
};
use crate::r#gen::Lean::Linter::CheckUnivs::{
    initialize_Lean_Linter_CheckUnivs, runtime_initialize_Lean_Linter_CheckUnivs,
};
use crate::r#gen::Lean::Linter::Coe::{
    initialize_Lean_Linter_Coe, runtime_initialize_Lean_Linter_Coe,
};
use crate::r#gen::Lean::Linter::ConstructorAsVariable::{
    initialize_Lean_Linter_ConstructorAsVariable,
    runtime_initialize_Lean_Linter_ConstructorAsVariable,
};
use crate::r#gen::Lean::Linter::DefProp::{
    initialize_Lean_Linter_DefProp, runtime_initialize_Lean_Linter_DefProp,
};
use crate::r#gen::Lean::Linter::Deprecated::{
    initialize_Lean_Linter_Deprecated, runtime_initialize_Lean_Linter_Deprecated,
};
use crate::r#gen::Lean::Linter::DocsOnAlt::{
    initialize_Lean_Linter_DocsOnAlt, runtime_initialize_Lean_Linter_DocsOnAlt,
};
use crate::r#gen::Lean::Linter::EnvLinter::{
    initialize_Lean_Linter_EnvLinter, runtime_initialize_Lean_Linter_EnvLinter,
};
use crate::r#gen::Lean::Linter::Extra::{
    initialize_Lean_Linter_Extra, runtime_initialize_Lean_Linter_Extra,
};
use crate::r#gen::Lean::Linter::GlobalAttributeIn::{
    initialize_Lean_Linter_GlobalAttributeIn, runtime_initialize_Lean_Linter_GlobalAttributeIn,
};
use crate::r#gen::Lean::Linter::List::{
    initialize_Lean_Linter_List, runtime_initialize_Lean_Linter_List,
};
use crate::r#gen::Lean::Linter::MissingDocs::{
    initialize_Lean_Linter_MissingDocs, runtime_initialize_Lean_Linter_MissingDocs,
};
use crate::r#gen::Lean::Linter::Omit::{
    initialize_Lean_Linter_Omit, runtime_initialize_Lean_Linter_Omit,
};
use crate::r#gen::Lean::Linter::PersistentLintLog::{
    initialize_Lean_Linter_PersistentLintLog, runtime_initialize_Lean_Linter_PersistentLintLog,
};
use crate::r#gen::Lean::Linter::Sets::{
    initialize_Lean_Linter_Sets, runtime_initialize_Lean_Linter_Sets,
};
use crate::r#gen::Lean::Linter::TacticTypeCheck::{
    initialize_Lean_Linter_TacticTypeCheck, runtime_initialize_Lean_Linter_TacticTypeCheck,
};
use crate::r#gen::Lean::Linter::UnusedSimpArgs::{
    initialize_Lean_Linter_UnusedSimpArgs, runtime_initialize_Lean_Linter_UnusedSimpArgs,
};
use crate::r#gen::Lean::Linter::UnusedVariables::{
    initialize_Lean_Linter_UnusedVariables, runtime_initialize_Lean_Linter_UnusedVariables,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Builtin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_CheckUnivs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_DefProp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_DocsOnAlt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_UnusedVariables(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Omit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Sets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_GlobalAttributeIn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_TacticTypeCheck(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Builtin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_CheckUnivs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_ConstructorAsVariable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_DefProp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_DocsOnAlt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_UnusedVariables(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_MissingDocs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Omit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Sets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_UnusedSimpArgs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_GlobalAttributeIn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_EnvLinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_PersistentLintLog(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_TacticTypeCheck(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter(builtin);
}