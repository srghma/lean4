// Lean compiler output
// Module: Lake.Config.InputFile
// Imports: Lake.Config.ConfigTarget
use crate::r#gen::Lake::Config::ConfigTarget::{
    initialize_Lake_Config_ConfigTarget, runtime_initialize_Lake_Config_ConfigTarget,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
pub unsafe fn l_Lake_InputFile_path(
    mut v_self_36_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_37_ = crate::leanh::lean_ctor_get(v_self_36_, 0);
    crate::leanh::lean_inc_ref(v_pkg_37_);
    v_config_38_ = crate::leanh::lean_ctor_get(v_self_36_, 2);
    crate::leanh::lean_inc(v_config_38_);
    crate::leanh::lean_dec_ref(v_self_36_);
    v_dir_39_ = crate::leanh::lean_ctor_get(v_pkg_37_, 4);
    crate::leanh::lean_inc_ref(v_dir_39_);
    crate::leanh::lean_dec_ref(v_pkg_37_);
    v_path_40_ = crate::leanh::lean_ctor_get(v_config_38_, 0);
    crate::leanh::lean_inc_ref(v_path_40_);
    crate::leanh::lean_dec(v_config_38_);
    v___x_41_ = l_Lake_joinRelative(v_dir_39_, v_path_40_);
    return v___x_41_;
}
pub unsafe fn l_Lake_InputFile_text(mut v_self_42_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_44_: u8 = 0;
    v_config_43_ = crate::leanh::lean_ctor_get(v_self_42_, 2);
    v_text_44_ = crate::leanh::lean_ctor_get_uint8(
        v_config_43_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    return v_text_44_;
}
pub unsafe fn l_Lake_InputFile_text___boxed(
    mut v_self_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Lake_InputFile_text(v_self_45_);
    crate::leanh::lean_dec_ref(v_self_45_);
    v_r_47_ = crate::leanh::lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Lake_InputDir_path(
    mut v_self_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_49_ = crate::leanh::lean_ctor_get(v_self_48_, 0);
    crate::leanh::lean_inc_ref(v_pkg_49_);
    v_config_50_ = crate::leanh::lean_ctor_get(v_self_48_, 2);
    crate::leanh::lean_inc(v_config_50_);
    crate::leanh::lean_dec_ref(v_self_48_);
    v_dir_51_ = crate::leanh::lean_ctor_get(v_pkg_49_, 4);
    crate::leanh::lean_inc_ref(v_dir_51_);
    crate::leanh::lean_dec_ref(v_pkg_49_);
    v_path_52_ = crate::leanh::lean_ctor_get(v_config_50_, 0);
    crate::leanh::lean_inc_ref(v_path_52_);
    crate::leanh::lean_dec(v_config_50_);
    v___x_53_ = l_Lake_joinRelative(v_dir_51_, v_path_52_);
    return v___x_53_;
}
pub unsafe fn l_Lake_InputDir_text(mut v_self_54_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_56_: u8 = 0;
    v_config_55_ = crate::leanh::lean_ctor_get(v_self_54_, 2);
    v_text_56_ = crate::leanh::lean_ctor_get_uint8(
        v_config_55_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    return v_text_56_;
}
pub unsafe fn l_Lake_InputDir_text___boxed(
    mut v_self_57_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_58_: u8 = 0;
    let mut v_r_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_58_ = l_Lake_InputDir_text(v_self_57_);
    crate::leanh::lean_dec_ref(v_self_57_);
    v_r_59_ = crate::leanh::lean_box((v_res_58_) as usize);
    return v_r_59_;
}
pub unsafe fn l_Lake_InputDir_filter(
    mut v_self_60_: *mut crate::leanh::LeanObject,
    mut v_a_61_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_filter_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_filter_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: u8 = 0;
    v_config_62_ = crate::leanh::lean_ctor_get(v_self_60_, 2);
    crate::leanh::lean_inc(v_config_62_);
    crate::leanh::lean_dec_ref(v_self_60_);
    v_filter_63_ = crate::leanh::lean_ctor_get(v_config_62_, 1);
    crate::leanh::lean_inc_ref(v_filter_63_);
    crate::leanh::lean_dec(v_config_62_);
    v_filter_64_ = crate::leanh::lean_ctor_get(v_filter_63_, 0);
    crate::leanh::lean_inc_ref(v_filter_64_);
    crate::leanh::lean_dec_ref(v_filter_63_);
    v___x_65_ = crate::leanh::lean_apply_1(v_filter_64_, v_a_61_);
    v___x_66_ = (crate::leanh::lean_unbox(v___x_65_) as u8);
    return v___x_66_;
}
pub unsafe fn l_Lake_InputDir_filter___boxed(
    mut v_self_67_: *mut crate::leanh::LeanObject,
    mut v_a_68_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_69_: u8 = 0;
    let mut v_r_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_69_ = l_Lake_InputDir_filter(v_self_67_, v_a_68_);
    v_r_70_ = crate::leanh::lean_box((v_res_69_) as usize);
    return v_r_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InputFile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InputFile(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_InputFile(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_ConfigTarget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_InputFile(builtin);
}
