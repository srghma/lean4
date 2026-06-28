// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.ULift
// Imports: Init.Data.Iterators.Combinators.ULift Init.Data.Iterators.Combinators.ULift Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Loop
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Combinators::ULift::{
    initialize_Init_Data_Iterators_Combinators_ULift,
    runtime_initialize_Init_Data_Iterators_Combinators_ULift,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::ULift::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(
    mut v_x_73_: *mut LeanObject,
    mut v_h__1_74_: *mut LeanObject,
    mut v_h__2_75_: *mut LeanObject,
    mut v_h__3_76_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_73_) {
        0 => {
            let mut v_it_77_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_78_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_76_);
            lean_dec(v_h__2_75_);
            v_it_77_ = lean_ctor_get(v_x_73_, 0);
            lean_inc(v_it_77_);
            v_out_78_ = lean_ctor_get(v_x_73_, 1);
            lean_inc(v_out_78_);
            lean_dec_ref_known(v_x_73_, 2);
            v___x_79_ = lean_apply_3(v_h__1_74_, v_it_77_, v_out_78_, lean_box(0));
            return v___x_79_;
        }
        1 => {
            let mut v_it_80_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_76_);
            lean_dec(v_h__1_74_);
            v_it_80_ = lean_ctor_get(v_x_73_, 0);
            lean_inc(v_it_80_);
            lean_dec_ref_known(v_x_73_, 1);
            v___x_81_ = lean_apply_2(v_h__2_75_, v_it_80_, lean_box(0));
            return v___x_81_;
        }
        _ => {
            let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_75_);
            lean_dec(v_h__1_74_);
            v___x_82_ = lean_apply_1(v_h__3_76_, lean_box(0));
            return v___x_82_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(
    mut v_00_u03b1_83_: *mut LeanObject,
    mut v_m_84_: *mut LeanObject,
    mut v_00_u03b2_85_: *mut LeanObject,
    mut v_inst_86_: *mut LeanObject,
    mut v_it_87_: *mut LeanObject,
    mut v_motive_88_: *mut LeanObject,
    mut v_x_89_: *mut LeanObject,
    mut v_h__1_90_: *mut LeanObject,
    mut v_h__2_91_: *mut LeanObject,
    mut v_h__3_92_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_89_) {
        0 => {
            let mut v_it_93_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_94_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_92_);
            lean_dec(v_h__2_91_);
            v_it_93_ = lean_ctor_get(v_x_89_, 0);
            lean_inc(v_it_93_);
            v_out_94_ = lean_ctor_get(v_x_89_, 1);
            lean_inc(v_out_94_);
            lean_dec_ref_known(v_x_89_, 2);
            v___x_95_ = lean_apply_3(v_h__1_90_, v_it_93_, v_out_94_, lean_box(0));
            return v___x_95_;
        }
        1 => {
            let mut v_it_96_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_92_);
            lean_dec(v_h__1_90_);
            v_it_96_ = lean_ctor_get(v_x_89_, 0);
            lean_inc(v_it_96_);
            lean_dec_ref_known(v_x_89_, 1);
            v___x_97_ = lean_apply_2(v_h__2_91_, v_it_96_, lean_box(0));
            return v___x_97_;
        }
        _ => {
            let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_91_);
            lean_dec(v_h__1_90_);
            v___x_98_ = lean_apply_1(v_h__3_92_, lean_box(0));
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_99_: *mut LeanObject,
    mut v_m_100_: *mut LeanObject,
    mut v_00_u03b2_101_: *mut LeanObject,
    mut v_inst_102_: *mut LeanObject,
    mut v_it_103_: *mut LeanObject,
    mut v_motive_104_: *mut LeanObject,
    mut v_x_105_: *mut LeanObject,
    mut v_h__1_106_: *mut LeanObject,
    mut v_h__2_107_: *mut LeanObject,
    mut v_h__3_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_109_: *mut LeanObject = core::ptr::null_mut();
    v_res_109_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_99_, v_m_100_, v_00_u03b2_101_, v_inst_102_, v_it_103_, v_motive_104_, v_x_105_, v_h__1_106_, v_h__2_107_, v_h__3_108_);
    lean_dec(v_it_103_);
    lean_dec(v_inst_102_);
    return v_res_109_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___redArg(
    mut v_x_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
    mut v_h__2_112_: *mut LeanObject,
    mut v_h__3_113_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_110_) {
        0 => {
            let mut v_it_114_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_113_);
            lean_dec(v_h__2_112_);
            v_it_114_ = lean_ctor_get(v_x_110_, 0);
            lean_inc(v_it_114_);
            v_out_115_ = lean_ctor_get(v_x_110_, 1);
            lean_inc(v_out_115_);
            lean_dec_ref_known(v_x_110_, 2);
            v___x_116_ = lean_apply_3(v_h__1_111_, v_it_114_, v_out_115_, lean_box(0));
            return v___x_116_;
        }
        1 => {
            let mut v_it_117_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_113_);
            lean_dec(v_h__1_111_);
            v_it_117_ = lean_ctor_get(v_x_110_, 0);
            lean_inc(v_it_117_);
            lean_dec_ref_known(v_x_110_, 1);
            v___x_118_ = lean_apply_2(v_h__2_112_, v_it_117_, lean_box(0));
            return v___x_118_;
        }
        _ => {
            let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_112_);
            lean_dec(v_h__1_111_);
            v___x_119_ = lean_apply_1(v_h__3_113_, lean_box(0));
            return v___x_119_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(
    mut v_00_u03b1_120_: *mut LeanObject,
    mut v_00_u03b2_121_: *mut LeanObject,
    mut v_inst_122_: *mut LeanObject,
    mut v_it_123_: *mut LeanObject,
    mut v_motive_124_: *mut LeanObject,
    mut v_x_125_: *mut LeanObject,
    mut v_h__1_126_: *mut LeanObject,
    mut v_h__2_127_: *mut LeanObject,
    mut v_h__3_128_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_125_) {
        0 => {
            let mut v_it_129_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_130_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_128_);
            lean_dec(v_h__2_127_);
            v_it_129_ = lean_ctor_get(v_x_125_, 0);
            lean_inc(v_it_129_);
            v_out_130_ = lean_ctor_get(v_x_125_, 1);
            lean_inc(v_out_130_);
            lean_dec_ref_known(v_x_125_, 2);
            v___x_131_ = lean_apply_3(v_h__1_126_, v_it_129_, v_out_130_, lean_box(0));
            return v___x_131_;
        }
        1 => {
            let mut v_it_132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_128_);
            lean_dec(v_h__1_126_);
            v_it_132_ = lean_ctor_get(v_x_125_, 0);
            lean_inc(v_it_132_);
            lean_dec_ref_known(v_x_125_, 1);
            v___x_133_ = lean_apply_2(v_h__2_127_, v_it_132_, lean_box(0));
            return v___x_133_;
        }
        _ => {
            let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_127_);
            lean_dec(v_h__1_126_);
            v___x_134_ = lean_apply_1(v_h__3_128_, lean_box(0));
            return v___x_134_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_135_: *mut LeanObject,
    mut v_00_u03b2_136_: *mut LeanObject,
    mut v_inst_137_: *mut LeanObject,
    mut v_it_138_: *mut LeanObject,
    mut v_motive_139_: *mut LeanObject,
    mut v_x_140_: *mut LeanObject,
    mut v_h__1_141_: *mut LeanObject,
    mut v_h__2_142_: *mut LeanObject,
    mut v_h__3_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_144_: *mut LeanObject = core::ptr::null_mut();
    v_res_144_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(v_00_u03b1_135_, v_00_u03b2_136_, v_inst_137_, v_it_138_, v_motive_139_, v_x_140_, v_h__1_141_, v_h__2_142_, v_h__3_143_);
    lean_dec(v_it_138_);
    lean_dec(v_inst_137_);
    return v_res_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
}
