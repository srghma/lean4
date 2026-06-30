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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_80_: *mut leanh::LeanObject,
    mut v_h__1_81_: *mut leanh::LeanObject,
    mut v_h__2_82_: *mut leanh::LeanObject,
    mut v_h__3_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_80_) {
        0 => {
            let mut v_it_84_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_85_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_83_);
            leanh::lean_dec(v_h__2_82_);
            v_it_84_ = leanh::lean_ctor_get(v_x_80_, 0);
            leanh::lean_inc(v_it_84_);
            v_out_85_ = leanh::lean_ctor_get(v_x_80_, 1);
            leanh::lean_inc(v_out_85_);
            leanh::lean_dec_ref_known(v_x_80_, 2);
            v___x_86_ = leanh::lean_apply_2(v_h__1_81_, v_it_84_, v_out_85_);
            return v___x_86_;
        }
        1 => {
            let mut v_it_87_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_83_);
            leanh::lean_dec(v_h__1_81_);
            v_it_87_ = leanh::lean_ctor_get(v_x_80_, 0);
            leanh::lean_inc(v_it_87_);
            leanh::lean_dec_ref_known(v_x_80_, 1);
            v___x_88_ = leanh::lean_apply_1(v_h__2_82_, v_it_87_);
            return v___x_88_;
        }
        _ => {
            let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_82_);
            leanh::lean_dec(v_h__1_81_);
            v___x_89_ = leanh::lean_box(0);
            v___x_90_ = leanh::lean_apply_1(v_h__3_83_, v___x_89_);
            return v___x_90_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_91_: *mut leanh::LeanObject,
    mut v_00_u03b2_92_: *mut leanh::LeanObject,
    mut v_m_93_: *mut leanh::LeanObject,
    mut v_motive_94_: *mut leanh::LeanObject,
    mut v_x_95_: *mut leanh::LeanObject,
    mut v_h__1_96_: *mut leanh::LeanObject,
    mut v_h__2_97_: *mut leanh::LeanObject,
    mut v_h__3_98_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_95_) {
        0 => {
            let mut v_it_99_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_100_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_98_);
            leanh::lean_dec(v_h__2_97_);
            v_it_99_ = leanh::lean_ctor_get(v_x_95_, 0);
            leanh::lean_inc(v_it_99_);
            v_out_100_ = leanh::lean_ctor_get(v_x_95_, 1);
            leanh::lean_inc(v_out_100_);
            leanh::lean_dec_ref_known(v_x_95_, 2);
            v___x_101_ = leanh::lean_apply_2(v_h__1_96_, v_it_99_, v_out_100_);
            return v___x_101_;
        }
        1 => {
            let mut v_it_102_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_98_);
            leanh::lean_dec(v_h__1_96_);
            v_it_102_ = leanh::lean_ctor_get(v_x_95_, 0);
            leanh::lean_inc(v_it_102_);
            leanh::lean_dec_ref_known(v_x_95_, 1);
            v___x_103_ = leanh::lean_apply_1(v_h__2_97_, v_it_102_);
            return v___x_103_;
        }
        _ => {
            let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_97_);
            leanh::lean_dec(v_h__1_96_);
            v___x_104_ = leanh::lean_box(0);
            v___x_105_ = leanh::lean_apply_1(v_h__3_98_, v___x_104_);
            return v___x_105_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_106_: *mut leanh::LeanObject,
    mut v_h__1_107_: *mut leanh::LeanObject,
    mut v_h__2_108_: *mut leanh::LeanObject,
    mut v_h__3_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_106_) {
        0 => {
            let mut v_it_110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_111_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_109_);
            leanh::lean_dec(v_h__2_108_);
            v_it_110_ = leanh::lean_ctor_get(v_x_106_, 0);
            leanh::lean_inc(v_it_110_);
            v_out_111_ = leanh::lean_ctor_get(v_x_106_, 1);
            leanh::lean_inc(v_out_111_);
            leanh::lean_dec_ref_known(v_x_106_, 2);
            v___x_112_ = leanh::lean_apply_3(
                v_h__1_107_,
                v_it_110_,
                v_out_111_,
                leanh::lean_box(0),
            );
            return v___x_112_;
        }
        1 => {
            let mut v_it_113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_109_);
            leanh::lean_dec(v_h__1_107_);
            v_it_113_ = leanh::lean_ctor_get(v_x_106_, 0);
            leanh::lean_inc(v_it_113_);
            leanh::lean_dec_ref_known(v_x_106_, 1);
            v___x_114_ =
                leanh::lean_apply_2(v_h__2_108_, v_it_113_, leanh::lean_box(0));
            return v___x_114_;
        }
        _ => {
            let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_108_);
            leanh::lean_dec(v_h__1_107_);
            v___x_115_ = leanh::lean_apply_1(v_h__3_109_, leanh::lean_box(0));
            return v___x_115_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_116_: *mut leanh::LeanObject,
    mut v_00_u03b2_117_: *mut leanh::LeanObject,
    mut v_m_118_: *mut leanh::LeanObject,
    mut v_inst_119_: *mut leanh::LeanObject,
    mut v_it_120_: *mut leanh::LeanObject,
    mut v_motive_121_: *mut leanh::LeanObject,
    mut v_x_122_: *mut leanh::LeanObject,
    mut v_h__1_123_: *mut leanh::LeanObject,
    mut v_h__2_124_: *mut leanh::LeanObject,
    mut v_h__3_125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_122_) {
        0 => {
            let mut v_it_126_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_125_);
            leanh::lean_dec(v_h__2_124_);
            v_it_126_ = leanh::lean_ctor_get(v_x_122_, 0);
            leanh::lean_inc(v_it_126_);
            v_out_127_ = leanh::lean_ctor_get(v_x_122_, 1);
            leanh::lean_inc(v_out_127_);
            leanh::lean_dec_ref_known(v_x_122_, 2);
            v___x_128_ = leanh::lean_apply_3(
                v_h__1_123_,
                v_it_126_,
                v_out_127_,
                leanh::lean_box(0),
            );
            return v___x_128_;
        }
        1 => {
            let mut v_it_129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_125_);
            leanh::lean_dec(v_h__1_123_);
            v_it_129_ = leanh::lean_ctor_get(v_x_122_, 0);
            leanh::lean_inc(v_it_129_);
            leanh::lean_dec_ref_known(v_x_122_, 1);
            v___x_130_ =
                leanh::lean_apply_2(v_h__2_124_, v_it_129_, leanh::lean_box(0));
            return v___x_130_;
        }
        _ => {
            let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_124_);
            leanh::lean_dec(v_h__1_123_);
            v___x_131_ = leanh::lean_apply_1(v_h__3_125_, leanh::lean_box(0));
            return v___x_131_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_132_: *mut leanh::LeanObject,
    mut v_00_u03b2_133_: *mut leanh::LeanObject,
    mut v_m_134_: *mut leanh::LeanObject,
    mut v_inst_135_: *mut leanh::LeanObject,
    mut v_it_136_: *mut leanh::LeanObject,
    mut v_motive_137_: *mut leanh::LeanObject,
    mut v_x_138_: *mut leanh::LeanObject,
    mut v_h__1_139_: *mut leanh::LeanObject,
    mut v_h__2_140_: *mut leanh::LeanObject,
    mut v_h__3_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_132_, v_00_u03b2_133_, v_m_134_, v_inst_135_, v_it_136_, v_motive_137_, v_x_138_, v_h__1_139_, v_h__2_140_, v_h__3_141_);
    leanh::lean_dec(v_it_136_);
    leanh::lean_dec(v_inst_135_);
    return v_res_142_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
    mut v_h__2_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_143_) == 0 {
        let mut v_a_146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_144_);
        v_a_146_ = leanh::lean_ctor_get(v_____do__lift_143_, 0);
        leanh::lean_inc(v_a_146_);
        leanh::lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_147_ = leanh::lean_apply_1(v_h__2_145_, v_a_146_);
        return v___x_147_;
    } else {
        let mut v_a_148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_145_);
        v_a_148_ = leanh::lean_ctor_get(v_____do__lift_143_, 0);
        leanh::lean_inc(v_a_148_);
        leanh::lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_149_ = leanh::lean_apply_1(v_h__1_144_, v_a_148_);
        return v___x_149_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_150_: *mut leanh::LeanObject,
    mut v_motive_151_: *mut leanh::LeanObject,
    mut v_____do__lift_152_: *mut leanh::LeanObject,
    mut v_h__1_153_: *mut leanh::LeanObject,
    mut v_h__2_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_152_) == 0 {
        let mut v_a_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_153_);
        v_a_155_ = leanh::lean_ctor_get(v_____do__lift_152_, 0);
        leanh::lean_inc(v_a_155_);
        leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_156_ = leanh::lean_apply_1(v_h__2_154_, v_a_155_);
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_154_);
        v_a_157_ = leanh::lean_ctor_get(v_____do__lift_152_, 0);
        leanh::lean_inc(v_a_157_);
        leanh::lean_dec_ref_known(v_____do__lift_152_, 1);
        v___x_158_ = leanh::lean_apply_1(v_h__1_153_, v_a_157_);
        return v___x_158_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
}