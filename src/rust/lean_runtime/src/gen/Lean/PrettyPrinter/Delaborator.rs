// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator
// Imports: Lean.PrettyPrinter.Delaborator.Options Lean.PrettyPrinter.Delaborator.SubExpr Lean.PrettyPrinter.Delaborator.TopDownAnalyze Lean.PrettyPrinter.Delaborator.Basic Lean.PrettyPrinter.Delaborator.Builtins
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    initialize_Lean_PrettyPrinter_Delaborator_Basic,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Builtins::{
    initialize_Lean_PrettyPrinter_Delaborator_Builtins,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Builtins,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::{
    initialize_Lean_PrettyPrinter_Delaborator_Options,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Options,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::SubExpr::{
    initialize_Lean_PrettyPrinter_Delaborator_SubExpr,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::TopDownAnalyze::{
    initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Builtins(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator_Builtins(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator(builtin);
}
