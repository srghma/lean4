// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen
// Imports: Lean.Elab.Tactic.Do.Internal.VCGen.Reduce Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Util Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache Lean.Elab.Tactic.Do.Internal.VCGen.Entails Lean.Elab.Tactic.Do.Internal.VCGen.Solve Lean.Elab.Tactic.Do.Internal.VCGen.Driver Lean.Elab.Tactic.Do.Internal.VCGen.Frontend
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Driver::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Entails::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Frontend::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Reduce::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::RuleCache::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::RuleConstruction::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Solve::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::SpecDB::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Util::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen(builtin);
}
