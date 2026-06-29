// Lean compiler output
// Module: Lake.Config.MetaClasses
// Imports: Lean.Data.NameMap.Basic
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
pub unsafe fn l_Lake_mkFieldDefault___redArg(
    mut v_field_69_: *mut crate::leanh::LeanObject,
    mut v_cfg_70_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mkDefault_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mkDefault_71_ = crate::leanh::lean_ctor_get(v_field_69_, 3);
    crate::leanh::lean_inc(v_mkDefault_71_);
    crate::leanh::lean_dec_ref(v_field_69_);
    v___x_72_ = crate::leanh::lean_apply_1(v_mkDefault_71_, v_cfg_70_);
    return v___x_72_;
}
pub unsafe fn l_Lake_mkFieldDefault(
    mut v_00_u03c3_73_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_74_: *mut crate::leanh::LeanObject,
    mut v_name_75_: *mut crate::leanh::LeanObject,
    mut v_field_76_: *mut crate::leanh::LeanObject,
    mut v_cfg_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mkDefault_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mkDefault_78_ = crate::leanh::lean_ctor_get(v_field_76_, 3);
    crate::leanh::lean_inc(v_mkDefault_78_);
    crate::leanh::lean_dec_ref(v_field_76_);
    v___x_79_ = crate::leanh::lean_apply_1(v_mkDefault_78_, v_cfg_77_);
    return v___x_79_;
}
pub unsafe fn l_Lake_mkFieldDefault___boxed(
    mut v_00_u03c3_80_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_81_: *mut crate::leanh::LeanObject,
    mut v_name_82_: *mut crate::leanh::LeanObject,
    mut v_field_83_: *mut crate::leanh::LeanObject,
    mut v_cfg_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_85_ = l_Lake_mkFieldDefault(
        v_00_u03c3_80_,
        v_00_u03b1_81_,
        v_name_82_,
        v_field_83_,
        v_cfg_84_,
    );
    crate::leanh::lean_dec(v_name_82_);
    return v_res_85_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__0(
    mut v_field_86_: *mut crate::leanh::LeanObject,
    mut v_parent_87_: *mut crate::leanh::LeanObject,
    mut v_s_88_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_89_ = crate::leanh::lean_ctor_get(v_field_86_, 0);
    crate::leanh::lean_inc(v_get_89_);
    crate::leanh::lean_dec_ref(v_field_86_);
    v_get_90_ = crate::leanh::lean_ctor_get(v_parent_87_, 0);
    crate::leanh::lean_inc(v_get_90_);
    crate::leanh::lean_dec_ref(v_parent_87_);
    v___x_91_ = crate::leanh::lean_apply_1(v_get_90_, v_s_88_);
    v___x_92_ = crate::leanh::lean_apply_1(v_get_89_, v___x_91_);
    return v___x_92_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__1(
    mut v_parent_93_: *mut crate::leanh::LeanObject,
    mut v_field_94_: *mut crate::leanh::LeanObject,
    mut v_a_95_: *mut crate::leanh::LeanObject,
    mut v___y_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modify_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modify_97_ = crate::leanh::lean_ctor_get(v_parent_93_, 2);
    crate::leanh::lean_inc(v_modify_97_);
    crate::leanh::lean_dec_ref(v_parent_93_);
    v_set_98_ = crate::leanh::lean_ctor_get(v_field_94_, 1);
    crate::leanh::lean_inc(v_set_98_);
    crate::leanh::lean_dec_ref(v_field_94_);
    v___x_99_ = crate::leanh::lean_apply_1(v_set_98_, v_a_95_);
    v___x_100_ = crate::leanh::lean_apply_2(v_modify_97_, v___x_99_, v___y_96_);
    return v___x_100_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__2(
    mut v_parent_101_: *mut crate::leanh::LeanObject,
    mut v_field_102_: *mut crate::leanh::LeanObject,
    mut v_f_103_: *mut crate::leanh::LeanObject,
    mut v___y_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modify_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modify_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modify_105_ = crate::leanh::lean_ctor_get(v_parent_101_, 2);
    crate::leanh::lean_inc(v_modify_105_);
    crate::leanh::lean_dec_ref(v_parent_101_);
    v_modify_106_ = crate::leanh::lean_ctor_get(v_field_102_, 2);
    crate::leanh::lean_inc(v_modify_106_);
    crate::leanh::lean_dec_ref(v_field_102_);
    v___x_107_ = crate::leanh::lean_apply_1(v_modify_106_, v_f_103_);
    v___x_108_ = crate::leanh::lean_apply_2(v_modify_105_, v___x_107_, v___y_104_);
    return v___x_108_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__3(
    mut v_field_109_: *mut crate::leanh::LeanObject,
    mut v_parent_110_: *mut crate::leanh::LeanObject,
    mut v_s_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mkDefault_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mkDefault_112_ = crate::leanh::lean_ctor_get(v_field_109_, 3);
    crate::leanh::lean_inc(v_mkDefault_112_);
    crate::leanh::lean_dec_ref(v_field_109_);
    v_get_113_ = crate::leanh::lean_ctor_get(v_parent_110_, 0);
    crate::leanh::lean_inc(v_get_113_);
    crate::leanh::lean_dec_ref(v_parent_110_);
    v___x_114_ = crate::leanh::lean_apply_1(v_get_113_, v_s_111_);
    v___x_115_ = crate::leanh::lean_apply_1(v_mkDefault_112_, v___x_114_);
    return v___x_115_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg(
    mut v_parent_116_: *mut crate::leanh::LeanObject,
    mut v_field_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_parent_116_, 3);
    crate::leanh::lean_inc_ref_n(v_field_117_, 3);
    v___f_118_ = crate::leanh::lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_118_, 0, v_field_117_);
    crate::leanh::lean_closure_set(v___f_118_, 1, v_parent_116_);
    v___f_119_ = crate::leanh::lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_119_, 0, v_parent_116_);
    crate::leanh::lean_closure_set(v___f_119_, 1, v_field_117_);
    v___f_120_ = crate::leanh::lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_120_, 0, v_parent_116_);
    crate::leanh::lean_closure_set(v___f_120_, 1, v_field_117_);
    v___f_121_ = crate::leanh::lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_121_, 0, v_field_117_);
    crate::leanh::lean_closure_set(v___f_121_, 1, v_parent_116_);
    v___x_122_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_122_, 0, v___f_118_);
    crate::leanh::lean_ctor_set(v___x_122_, 1, v___f_119_);
    crate::leanh::lean_ctor_set(v___x_122_, 2, v___f_120_);
    crate::leanh::lean_ctor_set(v___x_122_, 3, v___f_121_);
    return v___x_122_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent(
    mut v_00_u03c3_123_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_124_: *mut crate::leanh::LeanObject,
    mut v_name_125_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_126_: *mut crate::leanh::LeanObject,
    mut v_parent_127_: *mut crate::leanh::LeanObject,
    mut v_field_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = l_Lake_instConfigFieldOfConfigParent___redArg(v_parent_127_, v_field_128_);
    return v___x_129_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___boxed(
    mut v_00_u03c3_130_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_131_: *mut crate::leanh::LeanObject,
    mut v_name_132_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_133_: *mut crate::leanh::LeanObject,
    mut v_parent_134_: *mut crate::leanh::LeanObject,
    mut v_field_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Lake_instConfigFieldOfConfigParent(
        v_00_u03c3_130_,
        v_00_u03c1_131_,
        v_name_132_,
        v_00_u03b1_133_,
        v_parent_134_,
        v_field_135_,
    );
    crate::leanh::lean_dec(v_name_132_);
    return v_res_136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_MetaClasses(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_MetaClasses(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_MetaClasses(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_MetaClasses(builtin);
}
