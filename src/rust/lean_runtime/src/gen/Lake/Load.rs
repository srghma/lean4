// Lean compiler output
// Module: Lake.Load
// Imports: Lake.Load.Config Lake.Load.Lean Lake.Load.Lean.Elab Lake.Load.Lean.Eval Lake.Load.Manifest Lake.Load.Materialize Lake.Load.Package Lake.Load.Resolve Lake.Load.Toml Lake.Load.Workspace
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Load::Lean::Elab::{
    initialize_Lake_Load_Lean_Elab, runtime_initialize_Lake_Load_Lean_Elab,
};
use crate::r#gen::Lake::Load::Lean::Eval::{
    initialize_Lake_Load_Lean_Eval, runtime_initialize_Lake_Load_Lean_Eval,
};
use crate::r#gen::Lake::Load::Lean::{
    initialize_Lake_Load_Lean, runtime_initialize_Lake_Load_Lean,
};
use crate::r#gen::Lake::Load::Manifest::{
    initialize_Lake_Load_Manifest, runtime_initialize_Lake_Load_Manifest,
};
use crate::r#gen::Lake::Load::Materialize::{
    initialize_Lake_Load_Materialize, runtime_initialize_Lake_Load_Materialize,
};
use crate::r#gen::Lake::Load::Package::{
    initialize_Lake_Load_Package, runtime_initialize_Lake_Load_Package,
};
use crate::r#gen::Lake::Load::Resolve::{
    initialize_Lake_Load_Resolve, runtime_initialize_Lake_Load_Resolve,
};
use crate::r#gen::Lake::Load::Toml::{
    initialize_Lake_Load_Toml, runtime_initialize_Lake_Load_Toml,
};
use crate::r#gen::Lake::Load::Workspace::{
    initialize_Lake_Load_Workspace, runtime_initialize_Lake_Load_Workspace,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Materialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Resolve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Toml(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Lean(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Elab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Materialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Resolve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Toml(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Load(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Load(builtin);
}
