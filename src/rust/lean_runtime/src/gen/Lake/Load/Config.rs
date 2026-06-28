// Lean compiler output
// Module: Lake.Load.Config
// Imports: Lake.Config.Env Lake.Config.Lang Lake.Config.LakeConfig Lake.Load.Manifest
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Config::LakeConfig::{
    initialize_Lake_Config_LakeConfig, runtime_initialize_Lake_Config_LakeConfig,
};
use crate::r#gen::Lake::Config::Lang::{
    initialize_Lake_Config_Lang, runtime_initialize_Lake_Config_Lang,
};
use crate::r#gen::Lake::Load::Manifest::{
    initialize_Lake_Load_Manifest, runtime_initialize_Lake_Load_Manifest,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_Lake_LoadConfig_configDir___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 110, 102, 105, 103, 0],
};
static mut l_Lake_LoadConfig_configDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoadConfig_configDir___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_LoadConfig_lakeDir(mut v_cfg_15_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkgDir_16_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut LeanObject = core::ptr::null_mut();
    v_pkgDir_16_ = lean_ctor_get(v_cfg_15_, 6);
    lean_inc_ref(v_pkgDir_16_);
    lean_dec_ref(v_cfg_15_);
    v___x_17_ = l_Lake_defaultLakeDir;
    v___x_18_ = l_Lake_joinRelative(v_pkgDir_16_, v___x_17_);
    return v___x_18_;
}
pub unsafe fn l_Lake_LoadConfig_configDir(mut v_cfg_20_: *mut LeanObject) -> *mut LeanObject {
    let mut v_wsDir_21_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgIdx_22_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_25_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_26_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
    v_wsDir_21_ = lean_ctor_get(v_cfg_20_, 2);
    lean_inc_ref(v_wsDir_21_);
    v_pkgIdx_22_ = lean_ctor_get(v_cfg_20_, 3);
    lean_inc(v_pkgIdx_22_);
    lean_dec_ref(v_cfg_20_);
    v___x_23_ = l_Lake_defaultLakeDir;
    v___x_24_ = l_Lake_joinRelative(v_wsDir_21_, v___x_23_);
    v___x_25_ = l_Lake_LoadConfig_configDir___closed__0;
    v___x_26_ = l_Lake_joinRelative(v___x_24_, v___x_25_);
    v___x_27_ = l_Nat_reprFast(v_pkgIdx_22_);
    v___x_28_ = l_Lake_joinRelative(v___x_26_, v___x_27_);
    return v___x_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Lang(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Lang(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LakeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Load_Config(builtin);
}
