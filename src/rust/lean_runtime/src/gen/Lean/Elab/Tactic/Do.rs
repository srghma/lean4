// Lean compiler output
// Module: Lean.Elab.Tactic.Do
// Imports: Lean.Elab.Tactic.Do.ProofMode Lean.Elab.Tactic.Do.Syntax Lean.Elab.Tactic.Do.Attr Lean.Elab.Tactic.Do.LetElim Lean.Elab.Tactic.Do.Spec Lean.Elab.Tactic.Do.VCGen Lean.Elab.Tactic.Do.Internal
use crate::r#gen::Lean::Elab::Tactic::Do::Attr::{
    initialize_Lean_Elab_Tactic_Do_Attr, runtime_initialize_Lean_Elab_Tactic_Do_Attr,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::{
    initialize_Lean_Elab_Tactic_Do_Internal, runtime_initialize_Lean_Elab_Tactic_Do_Internal,
};
use crate::r#gen::Lean::Elab::Tactic::Do::LetElim::{
    initialize_Lean_Elab_Tactic_Do_LetElim, runtime_initialize_Lean_Elab_Tactic_Do_LetElim,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::{
    initialize_Lean_Elab_Tactic_Do_ProofMode, runtime_initialize_Lean_Elab_Tactic_Do_ProofMode,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Spec::{
    initialize_Lean_Elab_Tactic_Do_Spec, runtime_initialize_Lean_Elab_Tactic_Do_Spec,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Syntax::{
    initialize_Lean_Elab_Tactic_Do_Syntax, runtime_initialize_Lean_Elab_Tactic_Do_Syntax,
};
use crate::r#gen::Lean::Elab::Tactic::Do::VCGen::{
    initialize_Lean_Elab_Tactic_Do_VCGen, runtime_initialize_Lean_Elab_Tactic_Do_VCGen,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Spec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Spec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_VCGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do(builtin);
}
