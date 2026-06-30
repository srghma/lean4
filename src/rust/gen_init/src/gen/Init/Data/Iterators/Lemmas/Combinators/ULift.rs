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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(
    mut v_x_73_: *mut leanh::LeanObject,
    mut v_h__1_74_: *mut leanh::LeanObject,
    mut v_h__2_75_: *mut leanh::LeanObject,
    mut v_h__3_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_73_) {
        0 => {
            let mut v_it_77_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_78_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_76_);
            leanh::lean_dec(v_h__2_75_);
            v_it_77_ = leanh::lean_ctor_get(v_x_73_, 0);
            leanh::lean_inc(v_it_77_);
            v_out_78_ = leanh::lean_ctor_get(v_x_73_, 1);
            leanh::lean_inc(v_out_78_);
            leanh::lean_dec_ref_known(v_x_73_, 2);
            v___x_79_ = leanh::lean_apply_3(
                v_h__1_74_,
                v_it_77_,
                v_out_78_,
                leanh::lean_box(0),
            );
            return v___x_79_;
        }
        1 => {
            let mut v_it_80_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_76_);
            leanh::lean_dec(v_h__1_74_);
            v_it_80_ = leanh::lean_ctor_get(v_x_73_, 0);
            leanh::lean_inc(v_it_80_);
            leanh::lean_dec_ref_known(v_x_73_, 1);
            v___x_81_ = leanh::lean_apply_2(v_h__2_75_, v_it_80_, leanh::lean_box(0));
            return v___x_81_;
        }
        _ => {
            let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_75_);
            leanh::lean_dec(v_h__1_74_);
            v___x_82_ = leanh::lean_apply_1(v_h__3_76_, leanh::lean_box(0));
            return v___x_82_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(
    mut v_00_u03b1_83_: *mut leanh::LeanObject,
    mut v_m_84_: *mut leanh::LeanObject,
    mut v_00_u03b2_85_: *mut leanh::LeanObject,
    mut v_inst_86_: *mut leanh::LeanObject,
    mut v_it_87_: *mut leanh::LeanObject,
    mut v_motive_88_: *mut leanh::LeanObject,
    mut v_x_89_: *mut leanh::LeanObject,
    mut v_h__1_90_: *mut leanh::LeanObject,
    mut v_h__2_91_: *mut leanh::LeanObject,
    mut v_h__3_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_89_) {
        0 => {
            let mut v_it_93_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_94_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_92_);
            leanh::lean_dec(v_h__2_91_);
            v_it_93_ = leanh::lean_ctor_get(v_x_89_, 0);
            leanh::lean_inc(v_it_93_);
            v_out_94_ = leanh::lean_ctor_get(v_x_89_, 1);
            leanh::lean_inc(v_out_94_);
            leanh::lean_dec_ref_known(v_x_89_, 2);
            v___x_95_ = leanh::lean_apply_3(
                v_h__1_90_,
                v_it_93_,
                v_out_94_,
                leanh::lean_box(0),
            );
            return v___x_95_;
        }
        1 => {
            let mut v_it_96_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_92_);
            leanh::lean_dec(v_h__1_90_);
            v_it_96_ = leanh::lean_ctor_get(v_x_89_, 0);
            leanh::lean_inc(v_it_96_);
            leanh::lean_dec_ref_known(v_x_89_, 1);
            v___x_97_ = leanh::lean_apply_2(v_h__2_91_, v_it_96_, leanh::lean_box(0));
            return v___x_97_;
        }
        _ => {
            let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_91_);
            leanh::lean_dec(v_h__1_90_);
            v___x_98_ = leanh::lean_apply_1(v_h__3_92_, leanh::lean_box(0));
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_99_: *mut leanh::LeanObject,
    mut v_m_100_: *mut leanh::LeanObject,
    mut v_00_u03b2_101_: *mut leanh::LeanObject,
    mut v_inst_102_: *mut leanh::LeanObject,
    mut v_it_103_: *mut leanh::LeanObject,
    mut v_motive_104_: *mut leanh::LeanObject,
    mut v_x_105_: *mut leanh::LeanObject,
    mut v_h__1_106_: *mut leanh::LeanObject,
    mut v_h__2_107_: *mut leanh::LeanObject,
    mut v_h__3_108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_109_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_99_, v_m_100_, v_00_u03b2_101_, v_inst_102_, v_it_103_, v_motive_104_, v_x_105_, v_h__1_106_, v_h__2_107_, v_h__3_108_);
    leanh::lean_dec(v_it_103_);
    leanh::lean_dec(v_inst_102_);
    return v_res_109_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___redArg(
    mut v_x_110_: *mut leanh::LeanObject,
    mut v_h__1_111_: *mut leanh::LeanObject,
    mut v_h__2_112_: *mut leanh::LeanObject,
    mut v_h__3_113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_110_) {
        0 => {
            let mut v_it_114_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_113_);
            leanh::lean_dec(v_h__2_112_);
            v_it_114_ = leanh::lean_ctor_get(v_x_110_, 0);
            leanh::lean_inc(v_it_114_);
            v_out_115_ = leanh::lean_ctor_get(v_x_110_, 1);
            leanh::lean_inc(v_out_115_);
            leanh::lean_dec_ref_known(v_x_110_, 2);
            v___x_116_ = leanh::lean_apply_3(
                v_h__1_111_,
                v_it_114_,
                v_out_115_,
                leanh::lean_box(0),
            );
            return v___x_116_;
        }
        1 => {
            let mut v_it_117_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_113_);
            leanh::lean_dec(v_h__1_111_);
            v_it_117_ = leanh::lean_ctor_get(v_x_110_, 0);
            leanh::lean_inc(v_it_117_);
            leanh::lean_dec_ref_known(v_x_110_, 1);
            v___x_118_ =
                leanh::lean_apply_2(v_h__2_112_, v_it_117_, leanh::lean_box(0));
            return v___x_118_;
        }
        _ => {
            let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_112_);
            leanh::lean_dec(v_h__1_111_);
            v___x_119_ = leanh::lean_apply_1(v_h__3_113_, leanh::lean_box(0));
            return v___x_119_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(
    mut v_00_u03b1_120_: *mut leanh::LeanObject,
    mut v_00_u03b2_121_: *mut leanh::LeanObject,
    mut v_inst_122_: *mut leanh::LeanObject,
    mut v_it_123_: *mut leanh::LeanObject,
    mut v_motive_124_: *mut leanh::LeanObject,
    mut v_x_125_: *mut leanh::LeanObject,
    mut v_h__1_126_: *mut leanh::LeanObject,
    mut v_h__2_127_: *mut leanh::LeanObject,
    mut v_h__3_128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_125_) {
        0 => {
            let mut v_it_129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_130_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_128_);
            leanh::lean_dec(v_h__2_127_);
            v_it_129_ = leanh::lean_ctor_get(v_x_125_, 0);
            leanh::lean_inc(v_it_129_);
            v_out_130_ = leanh::lean_ctor_get(v_x_125_, 1);
            leanh::lean_inc(v_out_130_);
            leanh::lean_dec_ref_known(v_x_125_, 2);
            v___x_131_ = leanh::lean_apply_3(
                v_h__1_126_,
                v_it_129_,
                v_out_130_,
                leanh::lean_box(0),
            );
            return v___x_131_;
        }
        1 => {
            let mut v_it_132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_128_);
            leanh::lean_dec(v_h__1_126_);
            v_it_132_ = leanh::lean_ctor_get(v_x_125_, 0);
            leanh::lean_inc(v_it_132_);
            leanh::lean_dec_ref_known(v_x_125_, 1);
            v___x_133_ =
                leanh::lean_apply_2(v_h__2_127_, v_it_132_, leanh::lean_box(0));
            return v___x_133_;
        }
        _ => {
            let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_127_);
            leanh::lean_dec(v_h__1_126_);
            v___x_134_ = leanh::lean_apply_1(v_h__3_128_, leanh::lean_box(0));
            return v___x_134_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_135_: *mut leanh::LeanObject,
    mut v_00_u03b2_136_: *mut leanh::LeanObject,
    mut v_inst_137_: *mut leanh::LeanObject,
    mut v_it_138_: *mut leanh::LeanObject,
    mut v_motive_139_: *mut leanh::LeanObject,
    mut v_x_140_: *mut leanh::LeanObject,
    mut v_h__1_141_: *mut leanh::LeanObject,
    mut v_h__2_142_: *mut leanh::LeanObject,
    mut v_h__3_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_144_ = l___private_Init_Data_Iterators_Lemmas_Combinators_ULift_0__Std_Iter_step__uLift_match__1_splitter(v_00_u03b1_135_, v_00_u03b2_136_, v_inst_137_, v_it_138_, v_motive_139_, v_x_140_, v_h__1_141_, v_h__2_142_, v_h__3_143_);
    leanh::lean_dec(v_it_138_);
    leanh::lean_dec(v_inst_137_);
    return v_res_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
}