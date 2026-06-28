// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal Lean.Elab.Tactic.Do.ProofMode.Delab Lean.Elab.Tactic.Do.ProofMode.Basic Lean.Elab.Tactic.Do.ProofMode.Clear Lean.Elab.Tactic.Do.ProofMode.Intro Lean.Elab.Tactic.Do.ProofMode.Revert Lean.Elab.Tactic.Do.ProofMode.Exact Lean.Elab.Tactic.Do.ProofMode.Assumption Lean.Elab.Tactic.Do.ProofMode.Pure Lean.Elab.Tactic.Do.ProofMode.Frame Lean.Elab.Tactic.Do.ProofMode.LeftRight Lean.Elab.Tactic.Do.ProofMode.Constructor Lean.Elab.Tactic.Do.ProofMode.RenameI Lean.Elab.Tactic.Do.ProofMode.Specialize Lean.Elab.Tactic.Do.ProofMode.Cases Lean.Elab.Tactic.Do.ProofMode.Exfalso Lean.Elab.Tactic.Do.ProofMode.Have Lean.Elab.Tactic.Do.ProofMode.Refine
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Assumption::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Cases::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Cases,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Clear::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Clear,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Constructor::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Delab::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Delab,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Exact::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Exact,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Exfalso::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Frame::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Frame,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Have::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Have,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Intro::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Intro,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::LeftRight::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Pure::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Pure,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Refine::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Refine,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::RenameI::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Revert::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Revert,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Specialize::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Specialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode(builtin);
}
