// Lean compiler output
// Module: Lake.Config.InputFile
// Imports: Lake.Config.ConfigTarget
use crate::r#gen::Lake::Config::ConfigTarget::{
    initialize_Lake_Config_ConfigTarget, runtime_initialize_Lake_Config_ConfigTarget,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
pub unsafe fn l_Lake_InputFile_path(
    mut v_self_36_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_37_ = leanh::lean_ctor_get(v_self_36_, 0);
    leanh::lean_inc_ref(v_pkg_37_);
    v_config_38_ = leanh::lean_ctor_get(v_self_36_, 2);
    leanh::lean_inc(v_config_38_);
    leanh::lean_dec_ref(v_self_36_);
    v_dir_39_ = leanh::lean_ctor_get(v_pkg_37_, 4);
    leanh::lean_inc_ref(v_dir_39_);
    leanh::lean_dec_ref(v_pkg_37_);
    v_path_40_ = leanh::lean_ctor_get(v_config_38_, 0);
    leanh::lean_inc_ref(v_path_40_);
    leanh::lean_dec(v_config_38_);
    v___x_41_ = l_Lake_joinRelative(v_dir_39_, v_path_40_);
    return v___x_41_;
}
pub unsafe fn l_Lake_InputFile_text(mut v_self_42_: *mut leanh::LeanObject) -> u8 {
    let mut v_config_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_44_: u8 = 0;
    v_config_43_ = leanh::lean_ctor_get(v_self_42_, 2);
    v_text_44_ = leanh::lean_ctor_get_uint8(
        v_config_43_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    return v_text_44_;
}
pub unsafe fn l_Lake_InputFile_text___boxed(
    mut v_self_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_46_: u8 = 0;
    let mut v_r_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Lake_InputFile_text(v_self_45_);
    leanh::lean_dec_ref(v_self_45_);
    v_r_47_ = leanh::lean_box((v_res_46_) as usize);
    return v_r_47_;
}
pub unsafe fn l_Lake_InputDir_path(
    mut v_self_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_49_ = leanh::lean_ctor_get(v_self_48_, 0);
    leanh::lean_inc_ref(v_pkg_49_);
    v_config_50_ = leanh::lean_ctor_get(v_self_48_, 2);
    leanh::lean_inc(v_config_50_);
    leanh::lean_dec_ref(v_self_48_);
    v_dir_51_ = leanh::lean_ctor_get(v_pkg_49_, 4);
    leanh::lean_inc_ref(v_dir_51_);
    leanh::lean_dec_ref(v_pkg_49_);
    v_path_52_ = leanh::lean_ctor_get(v_config_50_, 0);
    leanh::lean_inc_ref(v_path_52_);
    leanh::lean_dec(v_config_50_);
    v___x_53_ = l_Lake_joinRelative(v_dir_51_, v_path_52_);
    return v___x_53_;
}
pub unsafe fn l_Lake_InputDir_text(mut v_self_54_: *mut leanh::LeanObject) -> u8 {
    let mut v_config_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_56_: u8 = 0;
    v_config_55_ = leanh::lean_ctor_get(v_self_54_, 2);
    v_text_56_ = leanh::lean_ctor_get_uint8(
        v_config_55_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    return v_text_56_;
}
pub unsafe fn l_Lake_InputDir_text___boxed(
    mut v_self_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_58_: u8 = 0;
    let mut v_r_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_58_ = l_Lake_InputDir_text(v_self_57_);
    leanh::lean_dec_ref(v_self_57_);
    v_r_59_ = leanh::lean_box((v_res_58_) as usize);
    return v_r_59_;
}
pub unsafe fn l_Lake_InputDir_filter(
    mut v_self_60_: *mut leanh::LeanObject,
    mut v_a_61_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_config_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filter_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filter_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_66_: u8 = 0;
    v_config_62_ = leanh::lean_ctor_get(v_self_60_, 2);
    leanh::lean_inc(v_config_62_);
    leanh::lean_dec_ref(v_self_60_);
    v_filter_63_ = leanh::lean_ctor_get(v_config_62_, 1);
    leanh::lean_inc_ref(v_filter_63_);
    leanh::lean_dec(v_config_62_);
    v_filter_64_ = leanh::lean_ctor_get(v_filter_63_, 0);
    leanh::lean_inc_ref(v_filter_64_);
    leanh::lean_dec_ref(v_filter_63_);
    v___x_65_ = leanh::lean_apply_1(v_filter_64_, v_a_61_);
    v___x_66_ = (leanh::lean_unbox(v___x_65_) as u8);
    return v___x_66_;
}
pub unsafe fn l_Lake_InputDir_filter___boxed(
    mut v_self_67_: *mut leanh::LeanObject,
    mut v_a_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_69_: u8 = 0;
    let mut v_r_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_69_ = l_Lake_InputDir_filter(v_self_67_, v_a_68_);
    v_r_70_ = leanh::lean_box((v_res_69_) as usize);
    return v_r_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InputFile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InputFile(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_InputFile(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_ConfigTarget(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_InputFile(builtin);
}