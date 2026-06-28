// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.Empty
// Imports: Std.Data.Iterators.Producers.Monadic.Empty Init.Data.Iterators.Lemmas.Consumers.Monadic
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Empty::{
    initialize_Std_Data_Iterators_Producers_Monadic_Empty,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_80_: *mut LeanObject,
    mut v_h__1_81_: *mut LeanObject,
    mut v_h__2_82_: *mut LeanObject,
    mut v_h__3_83_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_80_) {
        0 => {
            let mut v_it_84_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_85_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_83_);
            lean_dec(v_h__2_82_);
            v_it_84_ = lean_ctor_get(v_x_80_, 0);
            lean_inc(v_it_84_);
            v_out_85_ = lean_ctor_get(v_x_80_, 1);
            lean_inc(v_out_85_);
            lean_dec_ref_known(v_x_80_, 2);
            v___x_86_ = lean_apply_2(v_h__1_81_, v_it_84_, v_out_85_);
            return v___x_86_;
        }
        1 => {
            let mut v_it_87_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_83_);
            lean_dec(v_h__1_81_);
            v_it_87_ = lean_ctor_get(v_x_80_, 0);
            lean_inc(v_it_87_);
            lean_dec_ref_known(v_x_80_, 1);
            v___x_88_ = lean_apply_1(v_h__2_82_, v_it_87_);
            return v___x_88_;
        }
        _ => {
            let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_82_);
            lean_dec(v_h__1_81_);
            v___x_89_ = lean_box(0);
            v___x_90_ = lean_apply_1(v_h__3_83_, v___x_89_);
            return v___x_90_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_91_: *mut LeanObject,
    mut v_00_u03b2_92_: *mut LeanObject,
    mut v_m_93_: *mut LeanObject,
    mut v_motive_94_: *mut LeanObject,
    mut v_x_95_: *mut LeanObject,
    mut v_h__1_96_: *mut LeanObject,
    mut v_h__2_97_: *mut LeanObject,
    mut v_h__3_98_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_95_) {
        0 => {
            let mut v_it_99_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_100_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_98_);
            lean_dec(v_h__2_97_);
            v_it_99_ = lean_ctor_get(v_x_95_, 0);
            lean_inc(v_it_99_);
            v_out_100_ = lean_ctor_get(v_x_95_, 1);
            lean_inc(v_out_100_);
            lean_dec_ref_known(v_x_95_, 2);
            v___x_101_ = lean_apply_2(v_h__1_96_, v_it_99_, v_out_100_);
            return v___x_101_;
        }
        1 => {
            let mut v_it_102_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_98_);
            lean_dec(v_h__1_96_);
            v_it_102_ = lean_ctor_get(v_x_95_, 0);
            lean_inc(v_it_102_);
            lean_dec_ref_known(v_x_95_, 1);
            v___x_103_ = lean_apply_1(v_h__2_97_, v_it_102_);
            return v___x_103_;
        }
        _ => {
            let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_97_);
            lean_dec(v_h__1_96_);
            v___x_104_ = lean_box(0);
            v___x_105_ = lean_apply_1(v_h__3_98_, v___x_104_);
            return v___x_105_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_106_: *mut LeanObject,
    mut v_h__1_107_: *mut LeanObject,
    mut v_h__2_108_: *mut LeanObject,
    mut v_h__3_109_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_106_) {
        0 => {
            let mut v_it_110_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_109_);
            lean_dec(v_h__2_108_);
            v_it_110_ = lean_ctor_get(v_x_106_, 0);
            lean_inc(v_it_110_);
            v_out_111_ = lean_ctor_get(v_x_106_, 1);
            lean_inc(v_out_111_);
            lean_dec_ref_known(v_x_106_, 2);
            v___x_112_ = lean_apply_3(v_h__1_107_, v_it_110_, v_out_111_, lean_box(0));
            return v___x_112_;
        }
        1 => {
            let mut v_it_113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_109_);
            lean_dec(v_h__1_107_);
            v_it_113_ = lean_ctor_get(v_x_106_, 0);
            lean_inc(v_it_113_);
            lean_dec_ref_known(v_x_106_, 1);
            v___x_114_ = lean_apply_2(v_h__2_108_, v_it_113_, lean_box(0));
            return v___x_114_;
        }
        _ => {
            let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_108_);
            lean_dec(v_h__1_107_);
            v___x_115_ = lean_apply_1(v_h__3_109_, lean_box(0));
            return v___x_115_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_116_: *mut LeanObject,
    mut v_00_u03b2_117_: *mut LeanObject,
    mut v_m_118_: *mut LeanObject,
    mut v_inst_119_: *mut LeanObject,
    mut v_it_120_: *mut LeanObject,
    mut v_motive_121_: *mut LeanObject,
    mut v_x_122_: *mut LeanObject,
    mut v_h__1_123_: *mut LeanObject,
    mut v_h__2_124_: *mut LeanObject,
    mut v_h__3_125_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_122_) {
        0 => {
            let mut v_it_126_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_127_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_125_);
            lean_dec(v_h__2_124_);
            v_it_126_ = lean_ctor_get(v_x_122_, 0);
            lean_inc(v_it_126_);
            v_out_127_ = lean_ctor_get(v_x_122_, 1);
            lean_inc(v_out_127_);
            lean_dec_ref_known(v_x_122_, 2);
            v___x_128_ = lean_apply_3(v_h__1_123_, v_it_126_, v_out_127_, lean_box(0));
            return v___x_128_;
        }
        1 => {
            let mut v_it_129_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_125_);
            lean_dec(v_h__1_123_);
            v_it_129_ = lean_ctor_get(v_x_122_, 0);
            lean_inc(v_it_129_);
            lean_dec_ref_known(v_x_122_, 1);
            v___x_130_ = lean_apply_2(v_h__2_124_, v_it_129_, lean_box(0));
            return v___x_130_;
        }
        _ => {
            let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_124_);
            lean_dec(v_h__1_123_);
            v___x_131_ = lean_apply_1(v_h__3_125_, lean_box(0));
            return v___x_131_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_132_: *mut LeanObject,
    mut v_00_u03b2_133_: *mut LeanObject,
    mut v_m_134_: *mut LeanObject,
    mut v_inst_135_: *mut LeanObject,
    mut v_it_136_: *mut LeanObject,
    mut v_motive_137_: *mut LeanObject,
    mut v_x_138_: *mut LeanObject,
    mut v_h__1_139_: *mut LeanObject,
    mut v_h__2_140_: *mut LeanObject,
    mut v_h__3_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_142_: *mut LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_132_, v_00_u03b2_133_, v_m_134_, v_inst_135_, v_it_136_, v_motive_137_, v_x_138_, v_h__1_139_, v_h__2_140_, v_h__3_141_);
    lean_dec(v_it_136_);
    lean_dec(v_inst_135_);
    return v_res_142_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_143_: *mut LeanObject,
    mut v_h__1_144_: *mut LeanObject,
    mut v_h__2_145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_143_) == 0 {
        let mut v_a_146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_144_);
        v_a_146_ = lean_ctor_get(v_____do__lift_143_, 0);
        lean_inc(v_a_146_);
        lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_147_ = lean_apply_1(v_h__2_145_, v_a_146_);
        return v___x_147_;
    } else {
        let mut v_a_148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_145_);
        v_a_148_ = lean_ctor_get(v_____do__lift_143_, 0);
        lean_inc(v_a_148_);
        lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_149_ = lean_apply_1(v_h__1_144_, v_a_148_);
        return v___x_149_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_150_: *mut LeanObject,
    mut v_motive_151_: *mut LeanObject,
    mut v_____do__lift_152_: *mut LeanObject,
    mut v_h__1_153_: *mut LeanObject,
    mut v_h__2_154_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_152_) == 0 {
        let mut v_a_155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_153_);
        v_a_155_ = lean_ctor_get(v_____do__lift_152_, 0);
        lean_inc(v_a_155_);
        lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_156_ = lean_apply_1(v_h__2_154_, v_a_155_);
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_154_);
        v_a_157_ = lean_ctor_get(v_____do__lift_152_, 0);
        lean_inc(v_a_157_);
        lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_158_ = lean_apply_1(v_h__1_153_, v_a_157_);
        return v___x_158_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
}
