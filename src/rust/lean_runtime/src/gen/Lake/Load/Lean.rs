// Lean compiler output
// Module: Lake.Load.Lean
// Imports: Lake.Config.Package Lake.Config.LakefileConfig Lake.Load.Config Lake.Load.Lean.Elab Lake.Load.Lean.Eval
use crate::r#gen::Lake::Config::LakefileConfig::{
    initialize_Lake_Config_LakefileConfig, runtime_initialize_Lake_Config_LakefileConfig,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Load::Lean::Elab::{
    initialize_Lake_Load_Lean_Elab, l_Lake_importConfigFile, runtime_initialize_Lake_Load_Lean_Elab,
};
use crate::r#gen::Lake::Load::Lean::Eval::{
    initialize_Lake_Load_Lean_Eval, l_Lake_LakefileConfig_loadFromEnv,
    runtime_initialize_Lake_Load_Lean_Eval,
};
pub unsafe fn l_Lake_loadLeanConfig(
    mut v_cfg_22_: *mut crate::leanh::LeanObject,
    mut v_a_23_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_34_: u8 = 0;
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_38_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_cfg_22_);
                v___x_25_ = l_Lake_importConfigFile(v_cfg_22_, v_a_23_);
                if crate::leanh::lean_obj_tag(v___x_25_) == 0 {
                    v_a_26_ = crate::leanh::lean_ctor_get(v___x_25_, 0);
                    crate::leanh::lean_inc(v_a_26_);
                    v_a_27_ = crate::leanh::lean_ctor_get(v___x_25_, 1);
                    crate::leanh::lean_inc(v_a_27_);
                    crate::leanh::lean_dec_ref_known(v___x_25_, 2);
                    v_leanOpts_28_ = crate::leanh::lean_ctor_get(v_cfg_22_, 13);
                    crate::leanh::lean_inc_ref(v_leanOpts_28_);
                    crate::leanh::lean_dec_ref(v_cfg_22_);
                    v___x_29_ = l_Lake_LakefileConfig_loadFromEnv(v_a_26_, v_leanOpts_28_, v_a_27_);
                    return v___x_29_;
                } else {
                    crate::leanh::lean_dec_ref(v_cfg_22_);
                    v_a_30_ = crate::leanh::lean_ctor_get(v___x_25_, 0);
                    v_a_31_ = crate::leanh::lean_ctor_get(v___x_25_, 1);
                    v_isSharedCheck_38_ = (!crate::leanh::lean_is_exclusive(v___x_25_)) as u8;
                    if v_isSharedCheck_38_ == 0 {
                        v___x_33_ = v___x_25_;
                        v_isShared_34_ = v_isSharedCheck_38_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_31_);
                        crate::leanh::lean_inc(v_a_30_);
                        crate::leanh::lean_dec(v___x_25_);
                        v___x_33_ = crate::leanh::lean_box(0);
                        v_isShared_34_ = v_isSharedCheck_38_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_34_ == 0 {
                    v___x_36_ = v___x_33_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_37_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_30_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_37_, 1, v_a_31_);
                    v___x_36_ = v_reuseFailAlloc_37_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_36_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_loadLeanConfig___boxed(
    mut v_cfg_39_: *mut crate::leanh::LeanObject,
    mut v_a_40_: *mut crate::leanh::LeanObject,
    mut v_a_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Lake_loadLeanConfig(v_cfg_39_, v_a_40_);
    return v_res_42_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Lean(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Lean(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Lean(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Eval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Lean(builtin);
}
