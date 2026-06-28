// Lean compiler output
// Module: Init.Data.String.Lemmas.Intercalate
// Imports: Init.Data.String.Defs Init.Data.String.Defs Init.Data.String.Slice Init.Data.String.Slice Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter___redArg(
    mut v_x_69_: *mut crate::leanh::LeanObject,
    mut v_h__1_70_: *mut crate::leanh::LeanObject,
    mut v_h__2_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_69_) == 0 {
        let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_71_);
        v___x_72_ = crate::leanh::lean_box(0);
        v___x_73_ = crate::leanh::lean_apply_1(v_h__1_70_, v___x_72_);
        return v___x_73_;
    } else {
        let mut v_head_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_70_);
        v_head_74_ = crate::leanh::lean_ctor_get(v_x_69_, 0);
        crate::leanh::lean_inc(v_head_74_);
        v_tail_75_ = crate::leanh::lean_ctor_get(v_x_69_, 1);
        crate::leanh::lean_inc(v_tail_75_);
        crate::leanh::lean_dec_ref_known(v_x_69_, 2);
        v___x_76_ = crate::leanh::lean_apply_2(v_h__2_71_, v_head_74_, v_tail_75_);
        return v___x_76_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter(
    mut v_motive_77_: *mut crate::leanh::LeanObject,
    mut v_x_78_: *mut crate::leanh::LeanObject,
    mut v_h__1_79_: *mut crate::leanh::LeanObject,
    mut v_h__2_80_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_78_) == 0 {
        let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_80_);
        v___x_81_ = crate::leanh::lean_box(0);
        v___x_82_ = crate::leanh::lean_apply_1(v_h__1_79_, v___x_81_);
        return v___x_82_;
    } else {
        let mut v_head_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_79_);
        v_head_83_ = crate::leanh::lean_ctor_get(v_x_78_, 0);
        crate::leanh::lean_inc(v_head_83_);
        v_tail_84_ = crate::leanh::lean_ctor_get(v_x_78_, 1);
        crate::leanh::lean_inc(v_tail_84_);
        crate::leanh::lean_dec_ref_known(v_x_78_, 2);
        v___x_85_ = crate::leanh::lean_apply_2(v_h__2_80_, v_head_83_, v_tail_84_);
        return v___x_85_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter___redArg(
    mut v_x_86_: *mut crate::leanh::LeanObject,
    mut v_h__1_87_: *mut crate::leanh::LeanObject,
    mut v_h__2_88_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_86_) == 0 {
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_87_);
        v___x_89_ = crate::leanh::lean_box(0);
        v___x_90_ = crate::leanh::lean_apply_1(v_h__2_88_, v___x_89_);
        return v___x_90_;
    } else {
        let mut v_head_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_88_);
        v_head_91_ = crate::leanh::lean_ctor_get(v_x_86_, 0);
        crate::leanh::lean_inc(v_head_91_);
        v_tail_92_ = crate::leanh::lean_ctor_get(v_x_86_, 1);
        crate::leanh::lean_inc(v_tail_92_);
        crate::leanh::lean_dec_ref_known(v_x_86_, 2);
        v___x_93_ = crate::leanh::lean_apply_2(v_h__1_87_, v_head_91_, v_tail_92_);
        return v___x_93_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter(
    mut v_motive_94_: *mut crate::leanh::LeanObject,
    mut v_x_95_: *mut crate::leanh::LeanObject,
    mut v_h__1_96_: *mut crate::leanh::LeanObject,
    mut v_h__2_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_95_) == 0 {
        let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_96_);
        v___x_98_ = crate::leanh::lean_box(0);
        v___x_99_ = crate::leanh::lean_apply_1(v_h__2_97_, v___x_98_);
        return v___x_99_;
    } else {
        let mut v_head_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_97_);
        v_head_100_ = crate::leanh::lean_ctor_get(v_x_95_, 0);
        crate::leanh::lean_inc(v_head_100_);
        v_tail_101_ = crate::leanh::lean_ctor_get(v_x_95_, 1);
        crate::leanh::lean_inc(v_tail_101_);
        crate::leanh::lean_dec_ref_known(v_x_95_, 2);
        v___x_102_ = crate::leanh::lean_apply_2(v_h__1_96_, v_head_100_, v_tail_101_);
        return v___x_102_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter___redArg(
    mut v_x_103_: *mut crate::leanh::LeanObject,
    mut v_h__1_104_: *mut crate::leanh::LeanObject,
    mut v_h__2_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_103_) == 0 {
        let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_104_);
        v___x_106_ = crate::leanh::lean_box(0);
        v___x_107_ = crate::leanh::lean_apply_1(v_h__2_105_, v___x_106_);
        return v___x_107_;
    } else {
        let mut v_head_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_105_);
        v_head_108_ = crate::leanh::lean_ctor_get(v_x_103_, 0);
        crate::leanh::lean_inc(v_head_108_);
        v_tail_109_ = crate::leanh::lean_ctor_get(v_x_103_, 1);
        crate::leanh::lean_inc(v_tail_109_);
        crate::leanh::lean_dec_ref_known(v_x_103_, 2);
        v___x_110_ = crate::leanh::lean_apply_2(v_h__1_104_, v_head_108_, v_tail_109_);
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter(
    mut v_motive_111_: *mut crate::leanh::LeanObject,
    mut v_x_112_: *mut crate::leanh::LeanObject,
    mut v_h__1_113_: *mut crate::leanh::LeanObject,
    mut v_h__2_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_112_) == 0 {
        let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_113_);
        v___x_115_ = crate::leanh::lean_box(0);
        v___x_116_ = crate::leanh::lean_apply_1(v_h__2_114_, v___x_115_);
        return v___x_116_;
    } else {
        let mut v_head_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_114_);
        v_head_117_ = crate::leanh::lean_ctor_get(v_x_112_, 0);
        crate::leanh::lean_inc(v_head_117_);
        v_tail_118_ = crate::leanh::lean_ctor_get(v_x_112_, 1);
        crate::leanh::lean_inc(v_tail_118_);
        crate::leanh::lean_dec_ref_known(v_x_112_, 2);
        v___x_119_ = crate::leanh::lean_apply_2(v_h__1_113_, v_head_117_, v_tail_118_);
        return v___x_119_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter___redArg(
    mut v_x_120_: *mut crate::leanh::LeanObject,
    mut v_h__1_121_: *mut crate::leanh::LeanObject,
    mut v_h__2_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_120_) == 0 {
        let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_122_);
        v___x_123_ = crate::leanh::lean_box(0);
        v___x_124_ = crate::leanh::lean_apply_1(v_h__1_121_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_head_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_121_);
        v_head_125_ = crate::leanh::lean_ctor_get(v_x_120_, 0);
        crate::leanh::lean_inc(v_head_125_);
        v_tail_126_ = crate::leanh::lean_ctor_get(v_x_120_, 1);
        crate::leanh::lean_inc(v_tail_126_);
        crate::leanh::lean_dec_ref_known(v_x_120_, 2);
        v___x_127_ = crate::leanh::lean_apply_2(v_h__2_122_, v_head_125_, v_tail_126_);
        return v___x_127_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter(
    mut v_motive_128_: *mut crate::leanh::LeanObject,
    mut v_x_129_: *mut crate::leanh::LeanObject,
    mut v_h__1_130_: *mut crate::leanh::LeanObject,
    mut v_h__2_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_129_) == 0 {
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_131_);
        v___x_132_ = crate::leanh::lean_box(0);
        v___x_133_ = crate::leanh::lean_apply_1(v_h__1_130_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_head_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_130_);
        v_head_134_ = crate::leanh::lean_ctor_get(v_x_129_, 0);
        crate::leanh::lean_inc(v_head_134_);
        v_tail_135_ = crate::leanh::lean_ctor_get(v_x_129_, 1);
        crate::leanh::lean_inc(v_tail_135_);
        crate::leanh::lean_dec_ref_known(v_x_129_, 2);
        v___x_136_ = crate::leanh::lean_apply_2(v_h__2_131_, v_head_134_, v_tail_135_);
        return v___x_136_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Intercalate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Intercalate(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Intercalate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Intercalate(builtin);
}
