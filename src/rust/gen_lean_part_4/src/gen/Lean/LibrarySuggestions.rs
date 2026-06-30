// Lean compiler output
// Module: Lean.LibrarySuggestions
// Imports: Lean.LibrarySuggestions.Basic Lean.LibrarySuggestions.SymbolFrequency Lean.LibrarySuggestions.MePo Lean.LibrarySuggestions.SineQuaNon Lean.LibrarySuggestions.Default
use crate::r#gen::Lean::LibrarySuggestions::Basic::{
    initialize_Lean_LibrarySuggestions_Basic, runtime_initialize_Lean_LibrarySuggestions_Basic,
};
use crate::r#gen::Lean::LibrarySuggestions::Default::{
    initialize_Lean_LibrarySuggestions_Default, runtime_initialize_Lean_LibrarySuggestions_Default,
};
use crate::r#gen::Lean::LibrarySuggestions::MePo::{
    initialize_Lean_LibrarySuggestions_MePo, runtime_initialize_Lean_LibrarySuggestions_MePo,
};
use crate::r#gen::Lean::LibrarySuggestions::SineQuaNon::{
    initialize_Lean_LibrarySuggestions_SineQuaNon,
    runtime_initialize_Lean_LibrarySuggestions_SineQuaNon,
};
use crate::r#gen::Lean::LibrarySuggestions::SymbolFrequency::{
    initialize_Lean_LibrarySuggestions_SymbolFrequency,
    runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LibrarySuggestions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_MePo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_Default(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LibrarySuggestions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_LibrarySuggestions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_LibrarySuggestions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_MePo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_Default(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LibrarySuggestions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_LibrarySuggestions(builtin);
}