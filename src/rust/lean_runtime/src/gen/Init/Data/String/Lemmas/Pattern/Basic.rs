// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Basic
// Imports: Init.Data.String.Pattern.Basic Init.Data.String.Lemmas.Splits Init.Data.Iterators.Consumers.Collect Init.Data.String.Pattern.Basic Init.Data.String.OrderInstances Init.Data.String.Lemmas.IsEmpty Init.Data.String.Lemmas.Basic Init.Data.String.Lemmas.Order Init.Data.String.Termination Init.Data.Order.Lemmas Init.ByCases Init.Data.Option.Lemmas Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Pattern::Basic::{
    initialize_Init_Data_String_Pattern_Basic, runtime_initialize_Init_Data_String_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___redArg(
    mut v_x_78_: *mut LeanObject,
    mut v_h__1_79_: *mut LeanObject,
    mut v_h__2_80_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_78_) == 0 {
        let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_79_);
        v___x_81_ = lean_apply_1(v_h__2_80_, lean_box(0));
        return v___x_81_;
    } else {
        let mut v_val_82_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_80_);
        v_val_82_ = lean_ctor_get(v_x_78_, 0);
        lean_inc(v_val_82_);
        lean_dec_ref_known(v_x_78_, 1);
        v___x_83_ = lean_apply_2(v_h__1_79_, v_val_82_, lean_box(0));
        return v___x_83_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter(
    mut v_00_u03c1_84_: *mut LeanObject,
    mut v_pat_85_: *mut LeanObject,
    mut v_s_86_: *mut LeanObject,
    mut v_it_87_: *mut LeanObject,
    mut v_motive_88_: *mut LeanObject,
    mut v_x_89_: *mut LeanObject,
    mut v_h__1_90_: *mut LeanObject,
    mut v_h__2_91_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_89_) == 0 {
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_90_);
        v___x_92_ = lean_apply_1(v_h__2_91_, lean_box(0));
        return v___x_92_;
    } else {
        let mut v_val_93_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_91_);
        v_val_93_ = lean_ctor_get(v_x_89_, 0);
        lean_inc(v_val_93_);
        lean_dec_ref_known(v_x_89_, 1);
        v___x_94_ = lean_apply_2(v_h__1_90_, v_val_93_, lean_box(0));
        return v___x_94_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter___boxed(
    mut v_00_u03c1_95_: *mut LeanObject,
    mut v_pat_96_: *mut LeanObject,
    mut v_s_97_: *mut LeanObject,
    mut v_it_98_: *mut LeanObject,
    mut v_motive_99_: *mut LeanObject,
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_103_: *mut LeanObject = core::ptr::null_mut();
    v_res_103_ = l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern_match__3_splitter(v_00_u03c1_95_, v_pat_96_, v_s_97_, v_it_98_, v_motive_99_, v_x_100_, v_h__1_101_, v_h__2_102_);
    lean_dec(v_it_98_);
    lean_dec_ref(v_s_97_);
    lean_dec(v_pat_96_);
    return v_res_103_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_104_: *mut LeanObject,
    mut v_h__1_105_: *mut LeanObject,
    mut v_h__2_106_: *mut LeanObject,
    mut v_h__3_107_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_104_) {
        0 => {
            let mut v_it_108_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_107_);
            lean_dec(v_h__2_106_);
            v_it_108_ = lean_ctor_get(v_x_104_, 0);
            lean_inc(v_it_108_);
            v_out_109_ = lean_ctor_get(v_x_104_, 1);
            lean_inc(v_out_109_);
            lean_dec_ref_known(v_x_104_, 2);
            v___x_110_ = lean_apply_2(v_h__1_105_, v_it_108_, v_out_109_);
            return v___x_110_;
        }
        1 => {
            let mut v_it_111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_107_);
            lean_dec(v_h__1_105_);
            v_it_111_ = lean_ctor_get(v_x_104_, 0);
            lean_inc(v_it_111_);
            lean_dec_ref_known(v_x_104_, 1);
            v___x_112_ = lean_apply_1(v_h__2_106_, v_it_111_);
            return v___x_112_;
        }
        _ => {
            let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_106_);
            lean_dec(v_h__1_105_);
            v___x_113_ = lean_box(0);
            v___x_114_ = lean_apply_1(v_h__3_107_, v___x_113_);
            return v___x_114_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_115_: *mut LeanObject,
    mut v_00_u03b2_116_: *mut LeanObject,
    mut v_motive_117_: *mut LeanObject,
    mut v_x_118_: *mut LeanObject,
    mut v_h__1_119_: *mut LeanObject,
    mut v_h__2_120_: *mut LeanObject,
    mut v_h__3_121_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_118_) {
        0 => {
            let mut v_it_122_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_121_);
            lean_dec(v_h__2_120_);
            v_it_122_ = lean_ctor_get(v_x_118_, 0);
            lean_inc(v_it_122_);
            v_out_123_ = lean_ctor_get(v_x_118_, 1);
            lean_inc(v_out_123_);
            lean_dec_ref_known(v_x_118_, 2);
            v___x_124_ = lean_apply_2(v_h__1_119_, v_it_122_, v_out_123_);
            return v___x_124_;
        }
        1 => {
            let mut v_it_125_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_121_);
            lean_dec(v_h__1_119_);
            v_it_125_ = lean_ctor_get(v_x_118_, 0);
            lean_inc(v_it_125_);
            lean_dec_ref_known(v_x_118_, 1);
            v___x_126_ = lean_apply_1(v_h__2_120_, v_it_125_);
            return v___x_126_;
        }
        _ => {
            let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_120_);
            lean_dec(v_h__1_119_);
            v___x_127_ = lean_box(0);
            v___x_128_ = lean_apply_1(v_h__3_121_, v___x_127_);
            return v___x_128_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern_match__3_splitter___redArg(
    mut v_x_129_: *mut LeanObject,
    mut v_h__1_130_: *mut LeanObject,
    mut v_h__2_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_129_) == 0 {
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_130_);
        v___x_132_ = lean_apply_1(v_h__2_131_, lean_box(0));
        return v___x_132_;
    } else {
        let mut v_val_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_131_);
        v_val_133_ = lean_ctor_get(v_x_129_, 0);
        lean_inc(v_val_133_);
        lean_dec_ref_known(v_x_129_, 1);
        v___x_134_ = lean_apply_2(v_h__1_130_, v_val_133_, lean_box(0));
        return v___x_134_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern_match__3_splitter(
    mut v_00_u03c1_135_: *mut LeanObject,
    mut v_pat_136_: *mut LeanObject,
    mut v_s_137_: *mut LeanObject,
    mut v_it_138_: *mut LeanObject,
    mut v_motive_139_: *mut LeanObject,
    mut v_x_140_: *mut LeanObject,
    mut v_h__1_141_: *mut LeanObject,
    mut v_h__2_142_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_140_) == 0 {
        let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_141_);
        v___x_143_ = lean_apply_1(v_h__2_142_, lean_box(0));
        return v___x_143_;
    } else {
        let mut v_val_144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_142_);
        v_val_144_ = lean_ctor_get(v_x_140_, 0);
        lean_inc(v_val_144_);
        lean_dec_ref_known(v_x_140_, 1);
        v___x_145_ = lean_apply_2(v_h__1_141_, v_val_144_, lean_box(0));
        return v___x_145_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern_match__3_splitter___boxed(
    mut v_00_u03c1_146_: *mut LeanObject,
    mut v_pat_147_: *mut LeanObject,
    mut v_s_148_: *mut LeanObject,
    mut v_it_149_: *mut LeanObject,
    mut v_motive_150_: *mut LeanObject,
    mut v_x_151_: *mut LeanObject,
    mut v_h__1_152_: *mut LeanObject,
    mut v_h__2_153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_154_: *mut LeanObject = core::ptr::null_mut();
    v_res_154_ = l___private_Init_Data_String_Lemmas_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern_match__3_splitter(v_00_u03c1_146_, v_pat_147_, v_s_148_, v_it_149_, v_motive_150_, v_x_151_, v_h__1_152_, v_h__2_153_);
    lean_dec(v_it_149_);
    lean_dec_ref(v_s_148_);
    lean_dec(v_pat_147_);
    return v_res_154_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
}
