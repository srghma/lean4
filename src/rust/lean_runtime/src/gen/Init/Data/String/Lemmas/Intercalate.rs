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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter___redArg(
    mut v_x_69_: *mut LeanObject,
    mut v_h__1_70_: *mut LeanObject,
    mut v_h__2_71_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_69_) == 0 {
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_71_);
        v___x_72_ = lean_box(0);
        v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
        return v___x_73_;
    } else {
        let mut v_head_74_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_75_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_70_);
        v_head_74_ = lean_ctor_get(v_x_69_, 0);
        lean_inc(v_head_74_);
        v_tail_75_ = lean_ctor_get(v_x_69_, 1);
        lean_inc(v_tail_75_);
        lean_dec_ref_known(v_x_69_, 2);
        v___x_76_ = lean_apply_2(v_h__2_71_, v_head_74_, v_tail_75_);
        return v___x_76_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_match__1_splitter(
    mut v_motive_77_: *mut LeanObject,
    mut v_x_78_: *mut LeanObject,
    mut v_h__1_79_: *mut LeanObject,
    mut v_h__2_80_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_78_) == 0 {
        let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_80_);
        v___x_81_ = lean_box(0);
        v___x_82_ = lean_apply_1(v_h__1_79_, v___x_81_);
        return v___x_82_;
    } else {
        let mut v_head_83_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_84_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_79_);
        v_head_83_ = lean_ctor_get(v_x_78_, 0);
        lean_inc(v_head_83_);
        v_tail_84_ = lean_ctor_get(v_x_78_, 1);
        lean_inc(v_tail_84_);
        lean_dec_ref_known(v_x_78_, 2);
        v___x_85_ = lean_apply_2(v_h__2_80_, v_head_83_, v_tail_84_);
        return v___x_85_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter___redArg(
    mut v_x_86_: *mut LeanObject,
    mut v_h__1_87_: *mut LeanObject,
    mut v_h__2_88_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_86_) == 0 {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_87_);
        v___x_89_ = lean_box(0);
        v___x_90_ = lean_apply_1(v_h__2_88_, v___x_89_);
        return v___x_90_;
    } else {
        let mut v_head_91_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_92_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_88_);
        v_head_91_ = lean_ctor_get(v_x_86_, 0);
        lean_inc(v_head_91_);
        v_tail_92_ = lean_ctor_get(v_x_86_, 1);
        lean_inc(v_tail_92_);
        lean_dec_ref_known(v_x_86_, 2);
        v___x_93_ = lean_apply_2(v_h__1_87_, v_head_91_, v_tail_92_);
        return v___x_93_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_intercalate_go_match__1_splitter(
    mut v_motive_94_: *mut LeanObject,
    mut v_x_95_: *mut LeanObject,
    mut v_h__1_96_: *mut LeanObject,
    mut v_h__2_97_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_95_) == 0 {
        let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_96_);
        v___x_98_ = lean_box(0);
        v___x_99_ = lean_apply_1(v_h__2_97_, v___x_98_);
        return v___x_99_;
    } else {
        let mut v_head_100_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_97_);
        v_head_100_ = lean_ctor_get(v_x_95_, 0);
        lean_inc(v_head_100_);
        v_tail_101_ = lean_ctor_get(v_x_95_, 1);
        lean_inc(v_tail_101_);
        lean_dec_ref_known(v_x_95_, 2);
        v___x_102_ = lean_apply_2(v_h__1_96_, v_head_100_, v_tail_101_);
        return v___x_102_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter___redArg(
    mut v_x_103_: *mut LeanObject,
    mut v_h__1_104_: *mut LeanObject,
    mut v_h__2_105_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_103_) == 0 {
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_104_);
        v___x_106_ = lean_box(0);
        v___x_107_ = lean_apply_1(v_h__2_105_, v___x_106_);
        return v___x_107_;
    } else {
        let mut v_head_108_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_105_);
        v_head_108_ = lean_ctor_get(v_x_103_, 0);
        lean_inc(v_head_108_);
        v_tail_109_ = lean_ctor_get(v_x_103_, 1);
        lean_inc(v_tail_109_);
        lean_dec_ref_known(v_x_103_, 2);
        v___x_110_ = lean_apply_2(v_h__1_104_, v_head_108_, v_tail_109_);
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_go_match__1_splitter(
    mut v_motive_111_: *mut LeanObject,
    mut v_x_112_: *mut LeanObject,
    mut v_h__1_113_: *mut LeanObject,
    mut v_h__2_114_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_112_) == 0 {
        let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_113_);
        v___x_115_ = lean_box(0);
        v___x_116_ = lean_apply_1(v_h__2_114_, v___x_115_);
        return v___x_116_;
    } else {
        let mut v_head_117_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_114_);
        v_head_117_ = lean_ctor_get(v_x_112_, 0);
        lean_inc(v_head_117_);
        v_tail_118_ = lean_ctor_get(v_x_112_, 1);
        lean_inc(v_tail_118_);
        lean_dec_ref_known(v_x_112_, 2);
        v___x_119_ = lean_apply_2(v_h__1_113_, v_head_117_, v_tail_118_);
        return v___x_119_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter___redArg(
    mut v_x_120_: *mut LeanObject,
    mut v_h__1_121_: *mut LeanObject,
    mut v_h__2_122_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_120_) == 0 {
        let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_122_);
        v___x_123_ = lean_box(0);
        v___x_124_ = lean_apply_1(v_h__1_121_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_head_125_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_121_);
        v_head_125_ = lean_ctor_get(v_x_120_, 0);
        lean_inc(v_head_125_);
        v_tail_126_ = lean_ctor_get(v_x_120_, 1);
        lean_inc(v_tail_126_);
        lean_dec_ref_known(v_x_120_, 2);
        v___x_127_ = lean_apply_2(v_h__2_122_, v_head_125_, v_tail_126_);
        return v___x_127_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Intercalate_0__String_Slice_intercalate_match__1_splitter(
    mut v_motive_128_: *mut LeanObject,
    mut v_x_129_: *mut LeanObject,
    mut v_h__1_130_: *mut LeanObject,
    mut v_h__2_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_129_) == 0 {
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_131_);
        v___x_132_ = lean_box(0);
        v___x_133_ = lean_apply_1(v_h__1_130_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_head_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_130_);
        v_head_134_ = lean_ctor_get(v_x_129_, 0);
        lean_inc(v_head_134_);
        v_tail_135_ = lean_ctor_get(v_x_129_, 1);
        lean_inc(v_tail_135_);
        lean_dec_ref_known(v_x_129_, 2);
        v___x_136_ = lean_apply_2(v_h__2_131_, v_head_134_, v_tail_135_);
        return v___x_136_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Intercalate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Intercalate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Intercalate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Intercalate(builtin);
}
