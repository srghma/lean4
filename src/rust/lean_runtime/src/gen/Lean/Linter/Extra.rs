// Lean compiler output
// Module: Lean.Linter.Extra
// Imports: Lean.Linter.Extra.DupNamespace Lean.Linter.Extra.UnnecessarySeqFocus Lean.Linter.Extra.UnreachableTactic Lean.Linter.Extra.UnusedDecidableInType
use crate::r#gen::Lean::Linter::Extra::DupNamespace::{
    initialize_Lean_Linter_Extra_DupNamespace, runtime_initialize_Lean_Linter_Extra_DupNamespace,
};
use crate::r#gen::Lean::Linter::Extra::UnnecessarySeqFocus::{
    initialize_Lean_Linter_Extra_UnnecessarySeqFocus,
    runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus,
};
use crate::r#gen::Lean::Linter::Extra::UnreachableTactic::{
    initialize_Lean_Linter_Extra_UnreachableTactic,
    runtime_initialize_Lean_Linter_Extra_UnreachableTactic,
};
use crate::r#gen::Lean::Linter::Extra::UnusedDecidableInType::{
    initialize_Lean_Linter_Extra_UnusedDecidableInType,
    runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Extra_DupNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Extra_DupNamespace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Extra(builtin);
}
