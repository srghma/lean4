// Lean compiler output
// Module: Lake.Config
// Imports: Lake.Config.Artifact Lake.Config.Cache Lake.Config.ConfigDecl Lake.Config.ConfigTarget Lake.Config.Context Lake.Config.Defaults Lake.Config.Dependency Lake.Config.Dynlib Lake.Config.Env Lake.Config.ExternLib Lake.Config.ExternLibConfig Lake.Config.FacetConfig Lake.Config.Glob Lake.Config.InputFile Lake.Config.InputFileConfig Lake.Config.InstallPath Lake.Config.Kinds Lake.Config.LakeConfig Lake.Config.Lang Lake.Config.LeanConfig Lake.Config.LeanExe Lake.Config.LeanExeConfig Lake.Config.LeanLib Lake.Config.LeanLibConfig Lake.Config.MetaClasses Lake.Config.Module Lake.Config.Monad Lake.Config.Opaque Lake.Config.OutFormat Lake.Config.Package Lake.Config.Pattern Lake.Config.Script Lake.Config.TargetConfig Lake.Config.Workspace Lake.Config.WorkspaceConfig
use crate::r#gen::Lake::Config::Artifact::{
    initialize_Lake_Config_Artifact, runtime_initialize_Lake_Config_Artifact,
};
use crate::r#gen::Lake::Config::Cache::{
    initialize_Lake_Config_Cache, runtime_initialize_Lake_Config_Cache,
};
use crate::r#gen::Lake::Config::ConfigDecl::{
    initialize_Lake_Config_ConfigDecl, runtime_initialize_Lake_Config_ConfigDecl,
};
use crate::r#gen::Lake::Config::ConfigTarget::{
    initialize_Lake_Config_ConfigTarget, runtime_initialize_Lake_Config_ConfigTarget,
};
use crate::r#gen::Lake::Config::Context::{
    initialize_Lake_Config_Context, runtime_initialize_Lake_Config_Context,
};
use crate::r#gen::Lake::Config::Defaults::{
    initialize_Lake_Config_Defaults, runtime_initialize_Lake_Config_Defaults,
};
use crate::r#gen::Lake::Config::Dependency::{
    initialize_Lake_Config_Dependency, runtime_initialize_Lake_Config_Dependency,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Config::ExternLib::{
    initialize_Lake_Config_ExternLib, runtime_initialize_Lake_Config_ExternLib,
};
use crate::r#gen::Lake::Config::ExternLibConfig::{
    initialize_Lake_Config_ExternLibConfig, runtime_initialize_Lake_Config_ExternLibConfig,
};
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Glob::{
    initialize_Lake_Config_Glob, runtime_initialize_Lake_Config_Glob,
};
use crate::r#gen::Lake::Config::InputFile::{
    initialize_Lake_Config_InputFile, runtime_initialize_Lake_Config_InputFile,
};
use crate::r#gen::Lake::Config::InputFileConfig::{
    initialize_Lake_Config_InputFileConfig, runtime_initialize_Lake_Config_InputFileConfig,
};
use crate::r#gen::Lake::Config::InstallPath::{
    initialize_Lake_Config_InstallPath, runtime_initialize_Lake_Config_InstallPath,
};
use crate::r#gen::Lake::Config::Kinds::{
    initialize_Lake_Config_Kinds, runtime_initialize_Lake_Config_Kinds,
};
use crate::r#gen::Lake::Config::LakeConfig::{
    initialize_Lake_Config_LakeConfig, runtime_initialize_Lake_Config_LakeConfig,
};
use crate::r#gen::Lake::Config::Lang::{
    initialize_Lake_Config_Lang, runtime_initialize_Lake_Config_Lang,
};
use crate::r#gen::Lake::Config::LeanConfig::{
    initialize_Lake_Config_LeanConfig, runtime_initialize_Lake_Config_LeanConfig,
};
use crate::r#gen::Lake::Config::LeanExe::{
    initialize_Lake_Config_LeanExe, runtime_initialize_Lake_Config_LeanExe,
};
use crate::r#gen::Lake::Config::LeanExeConfig::{
    initialize_Lake_Config_LeanExeConfig, runtime_initialize_Lake_Config_LeanExeConfig,
};
use crate::r#gen::Lake::Config::LeanLib::{
    initialize_Lake_Config_LeanLib, runtime_initialize_Lake_Config_LeanLib,
};
use crate::r#gen::Lake::Config::LeanLibConfig::{
    initialize_Lake_Config_LeanLibConfig, runtime_initialize_Lake_Config_LeanLibConfig,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lake::Config::Module::{
    initialize_Lake_Config_Module, runtime_initialize_Lake_Config_Module,
};
use crate::r#gen::Lake::Config::Monad::{
    initialize_Lake_Config_Monad, runtime_initialize_Lake_Config_Monad,
};
use crate::r#gen::Lake::Config::Opaque::{
    initialize_Lake_Config_Opaque, runtime_initialize_Lake_Config_Opaque,
};
use crate::r#gen::Lake::Config::OutFormat::{
    initialize_Lake_Config_OutFormat, runtime_initialize_Lake_Config_OutFormat,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Config::Pattern::{
    initialize_Lake_Config_Pattern, runtime_initialize_Lake_Config_Pattern,
};
use crate::r#gen::Lake::Config::Script::{
    initialize_Lake_Config_Script, runtime_initialize_Lake_Config_Script,
};
use crate::r#gen::Lake::Config::TargetConfig::{
    initialize_Lake_Config_TargetConfig, runtime_initialize_Lake_Config_TargetConfig,
};
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::Config::WorkspaceConfig::{
    initialize_Lake_Config_WorkspaceConfig, runtime_initialize_Lake_Config_WorkspaceConfig,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dependency(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Glob(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InstallPath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Lang(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_OutFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_TargetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_WorkspaceConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ConfigDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ConfigTarget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dependency(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Glob(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InstallPath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Kinds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Lang(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_OutFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Script(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_TargetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_WorkspaceConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config(builtin);
}
