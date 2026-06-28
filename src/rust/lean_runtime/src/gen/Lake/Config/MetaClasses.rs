// Lean compiler output
// Module: Lake.Config.MetaClasses
// Imports: Lean.Data.NameMap.Basic
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Lake_mkFieldDefault___redArg(
    mut v_field_69_: *mut LeanObject,
    mut v_cfg_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkDefault_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
    v_mkDefault_71_ = lean_ctor_get(v_field_69_, 3);
    lean_inc(v_mkDefault_71_);
    lean_dec_ref(v_field_69_);
    v___x_72_ = lean_apply_1(v_mkDefault_71_, v_cfg_70_);
    return v___x_72_;
}
pub unsafe fn l_Lake_mkFieldDefault(
    mut v_00_u03c3_73_: *mut LeanObject,
    mut v_00_u03b1_74_: *mut LeanObject,
    mut v_name_75_: *mut LeanObject,
    mut v_field_76_: *mut LeanObject,
    mut v_cfg_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkDefault_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v_mkDefault_78_ = lean_ctor_get(v_field_76_, 3);
    lean_inc(v_mkDefault_78_);
    lean_dec_ref(v_field_76_);
    v___x_79_ = lean_apply_1(v_mkDefault_78_, v_cfg_77_);
    return v___x_79_;
}
pub unsafe fn l_Lake_mkFieldDefault___boxed(
    mut v_00_u03c3_80_: *mut LeanObject,
    mut v_00_u03b1_81_: *mut LeanObject,
    mut v_name_82_: *mut LeanObject,
    mut v_field_83_: *mut LeanObject,
    mut v_cfg_84_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_85_: *mut LeanObject = core::ptr::null_mut();
    v_res_85_ = l_Lake_mkFieldDefault(
        v_00_u03c3_80_,
        v_00_u03b1_81_,
        v_name_82_,
        v_field_83_,
        v_cfg_84_,
    );
    lean_dec(v_name_82_);
    return v_res_85_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__0(
    mut v_field_86_: *mut LeanObject,
    mut v_parent_87_: *mut LeanObject,
    mut v_s_88_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
    v_get_89_ = lean_ctor_get(v_field_86_, 0);
    lean_inc(v_get_89_);
    lean_dec_ref(v_field_86_);
    v_get_90_ = lean_ctor_get(v_parent_87_, 0);
    lean_inc(v_get_90_);
    lean_dec_ref(v_parent_87_);
    v___x_91_ = lean_apply_1(v_get_90_, v_s_88_);
    v___x_92_ = lean_apply_1(v_get_89_, v___x_91_);
    return v___x_92_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__1(
    mut v_parent_93_: *mut LeanObject,
    mut v_field_94_: *mut LeanObject,
    mut v_a_95_: *mut LeanObject,
    mut v___y_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modify_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    v_modify_97_ = lean_ctor_get(v_parent_93_, 2);
    lean_inc(v_modify_97_);
    lean_dec_ref(v_parent_93_);
    v_set_98_ = lean_ctor_get(v_field_94_, 1);
    lean_inc(v_set_98_);
    lean_dec_ref(v_field_94_);
    v___x_99_ = lean_apply_1(v_set_98_, v_a_95_);
    v___x_100_ = lean_apply_2(v_modify_97_, v___x_99_, v___y_96_);
    return v___x_100_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__2(
    mut v_parent_101_: *mut LeanObject,
    mut v_field_102_: *mut LeanObject,
    mut v_f_103_: *mut LeanObject,
    mut v___y_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modify_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modify_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v_modify_105_ = lean_ctor_get(v_parent_101_, 2);
    lean_inc(v_modify_105_);
    lean_dec_ref(v_parent_101_);
    v_modify_106_ = lean_ctor_get(v_field_102_, 2);
    lean_inc(v_modify_106_);
    lean_dec_ref(v_field_102_);
    v___x_107_ = lean_apply_1(v_modify_106_, v_f_103_);
    v___x_108_ = lean_apply_2(v_modify_105_, v___x_107_, v___y_104_);
    return v___x_108_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg___lam__3(
    mut v_field_109_: *mut LeanObject,
    mut v_parent_110_: *mut LeanObject,
    mut v_s_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkDefault_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    v_mkDefault_112_ = lean_ctor_get(v_field_109_, 3);
    lean_inc(v_mkDefault_112_);
    lean_dec_ref(v_field_109_);
    v_get_113_ = lean_ctor_get(v_parent_110_, 0);
    lean_inc(v_get_113_);
    lean_dec_ref(v_parent_110_);
    v___x_114_ = lean_apply_1(v_get_113_, v_s_111_);
    v___x_115_ = lean_apply_1(v_mkDefault_112_, v___x_114_);
    return v___x_115_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___redArg(
    mut v_parent_116_: *mut LeanObject,
    mut v_field_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_parent_116_, 3);
    lean_inc_ref_n(v_field_117_, 3);
    v___f_118_ = lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_118_, 0, v_field_117_);
    lean_closure_set(v___f_118_, 1, v_parent_116_);
    v___f_119_ = lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_119_, 0, v_parent_116_);
    lean_closure_set(v___f_119_, 1, v_field_117_);
    v___f_120_ = lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_120_, 0, v_parent_116_);
    lean_closure_set(v___f_120_, 1, v_field_117_);
    v___f_121_ = lean_alloc_closure(
        l_Lake_instConfigFieldOfConfigParent___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_121_, 0, v_field_117_);
    lean_closure_set(v___f_121_, 1, v_parent_116_);
    v___x_122_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_122_, 0, v___f_118_);
    lean_ctor_set(v___x_122_, 1, v___f_119_);
    lean_ctor_set(v___x_122_, 2, v___f_120_);
    lean_ctor_set(v___x_122_, 3, v___f_121_);
    return v___x_122_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent(
    mut v_00_u03c3_123_: *mut LeanObject,
    mut v_00_u03c1_124_: *mut LeanObject,
    mut v_name_125_: *mut LeanObject,
    mut v_00_u03b1_126_: *mut LeanObject,
    mut v_parent_127_: *mut LeanObject,
    mut v_field_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    v___x_129_ = l_Lake_instConfigFieldOfConfigParent___redArg(v_parent_127_, v_field_128_);
    return v___x_129_;
}
pub unsafe fn l_Lake_instConfigFieldOfConfigParent___boxed(
    mut v_00_u03c3_130_: *mut LeanObject,
    mut v_00_u03c1_131_: *mut LeanObject,
    mut v_name_132_: *mut LeanObject,
    mut v_00_u03b1_133_: *mut LeanObject,
    mut v_parent_134_: *mut LeanObject,
    mut v_field_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_136_: *mut LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Lake_instConfigFieldOfConfigParent(
        v_00_u03c3_130_,
        v_00_u03c1_131_,
        v_name_132_,
        v_00_u03b1_133_,
        v_parent_134_,
        v_field_135_,
    );
    lean_dec(v_name_132_);
    return v_res_136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_MetaClasses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_MetaClasses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_MetaClasses(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_MetaClasses(builtin);
}
