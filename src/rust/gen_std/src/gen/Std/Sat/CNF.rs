// Lean compiler output
// Module: Std.Sat.CNF
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.Literal Std.Sat.CNF.Relabel Std.Sat.CNF.RelabelFin Std.Sat.CNF.Dimacs
use crate::r#gen::Std::Sat::CNF::Basic::{
    initialize_Std_Sat_CNF_Basic, runtime_initialize_Std_Sat_CNF_Basic,
};
use crate::r#gen::Std::Sat::CNF::Dimacs::{
    initialize_Std_Sat_CNF_Dimacs, runtime_initialize_Std_Sat_CNF_Dimacs,
};
use crate::r#gen::Std::Sat::CNF::Literal::{
    initialize_Std_Sat_CNF_Literal, runtime_initialize_Std_Sat_CNF_Literal,
};
use crate::r#gen::Std::Sat::CNF::Relabel::{
    initialize_Std_Sat_CNF_Relabel, runtime_initialize_Std_Sat_CNF_Relabel,
};
use crate::r#gen::Std::Sat::CNF::RelabelFin::{
    initialize_Std_Sat_CNF_RelabelFin, runtime_initialize_Std_Sat_CNF_RelabelFin,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Literal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Dimacs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_CNF(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_Literal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_Relabel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_RelabelFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_Dimacs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_CNF(builtin);
}