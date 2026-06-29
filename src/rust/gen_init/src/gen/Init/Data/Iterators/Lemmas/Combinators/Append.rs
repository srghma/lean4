// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Append
// Imports: Init.Data.Iterators.Combinators.Append Init.Data.Iterators.Lemmas.Combinators.Monadic.Append Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Basic Init.Omega
use crate::r#gen::Init::Data::Iterators::Combinators::Append::{
    initialize_Init_Data_Iterators_Combinators_Append,
    runtime_initialize_Init_Data_Iterators_Combinators_Append,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::Append::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Access::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_IterM_step__append_match__1_splitter___redArg(
    mut v_x_73_: *mut crate::leanh::LeanObject,
    mut v_h__1_74_: *mut crate::leanh::LeanObject,
    mut v_h__2_75_: *mut crate::leanh::LeanObject,
    mut v_h__3_76_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_73_) {
        0 => {
            let mut v_it_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_76_);
            crate::leanh::lean_dec(v_h__2_75_);
            v_it_77_ = crate::leanh::lean_ctor_get(v_x_73_, 0);
            crate::leanh::lean_inc(v_it_77_);
            v_out_78_ = crate::leanh::lean_ctor_get(v_x_73_, 1);
            crate::leanh::lean_inc(v_out_78_);
            crate::leanh::lean_dec_ref_known(v_x_73_, 2);
            v___x_79_ = crate::leanh::lean_apply_3(
                v_h__1_74_,
                v_it_77_,
                v_out_78_,
                crate::leanh::lean_box(0),
            );
            return v___x_79_;
        }
        1 => {
            let mut v_it_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_76_);
            crate::leanh::lean_dec(v_h__1_74_);
            v_it_80_ = crate::leanh::lean_ctor_get(v_x_73_, 0);
            crate::leanh::lean_inc(v_it_80_);
            crate::leanh::lean_dec_ref_known(v_x_73_, 1);
            v___x_81_ = crate::leanh::lean_apply_2(v_h__2_75_, v_it_80_, crate::leanh::lean_box(0));
            return v___x_81_;
        }
        _ => {
            let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_75_);
            crate::leanh::lean_dec(v_h__1_74_);
            v___x_82_ = crate::leanh::lean_apply_1(v_h__3_76_, crate::leanh::lean_box(0));
            return v___x_82_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_IterM_step__append_match__1_splitter(
    mut v_00_u03b1_u2081_83_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_84_: *mut crate::leanh::LeanObject,
    mut v_m_85_: *mut crate::leanh::LeanObject,
    mut v_inst_86_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_87_: *mut crate::leanh::LeanObject,
    mut v_motive_88_: *mut crate::leanh::LeanObject,
    mut v_x_89_: *mut crate::leanh::LeanObject,
    mut v_h__1_90_: *mut crate::leanh::LeanObject,
    mut v_h__2_91_: *mut crate::leanh::LeanObject,
    mut v_h__3_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_89_) {
        0 => {
            let mut v_it_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_92_);
            crate::leanh::lean_dec(v_h__2_91_);
            v_it_93_ = crate::leanh::lean_ctor_get(v_x_89_, 0);
            crate::leanh::lean_inc(v_it_93_);
            v_out_94_ = crate::leanh::lean_ctor_get(v_x_89_, 1);
            crate::leanh::lean_inc(v_out_94_);
            crate::leanh::lean_dec_ref_known(v_x_89_, 2);
            v___x_95_ = crate::leanh::lean_apply_3(
                v_h__1_90_,
                v_it_93_,
                v_out_94_,
                crate::leanh::lean_box(0),
            );
            return v___x_95_;
        }
        1 => {
            let mut v_it_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_92_);
            crate::leanh::lean_dec(v_h__1_90_);
            v_it_96_ = crate::leanh::lean_ctor_get(v_x_89_, 0);
            crate::leanh::lean_inc(v_it_96_);
            crate::leanh::lean_dec_ref_known(v_x_89_, 1);
            v___x_97_ = crate::leanh::lean_apply_2(v_h__2_91_, v_it_96_, crate::leanh::lean_box(0));
            return v___x_97_;
        }
        _ => {
            let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_91_);
            crate::leanh::lean_dec(v_h__1_90_);
            v___x_98_ = crate::leanh::lean_apply_1(v_h__3_92_, crate::leanh::lean_box(0));
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_IterM_step__append_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_99_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_100_: *mut crate::leanh::LeanObject,
    mut v_m_101_: *mut crate::leanh::LeanObject,
    mut v_inst_102_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_103_: *mut crate::leanh::LeanObject,
    mut v_motive_104_: *mut crate::leanh::LeanObject,
    mut v_x_105_: *mut crate::leanh::LeanObject,
    mut v_h__1_106_: *mut crate::leanh::LeanObject,
    mut v_h__2_107_: *mut crate::leanh::LeanObject,
    mut v_h__3_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_109_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_IterM_step__append_match__1_splitter(v_00_u03b1_u2081_99_, v_00_u03b2_100_, v_m_101_, v_inst_102_, v_it_u2081_103_, v_motive_104_, v_x_105_, v_h__1_106_, v_h__2_107_, v_h__3_108_);
    crate::leanh::lean_dec(v_it_u2081_103_);
    crate::leanh::lean_dec(v_inst_102_);
    return v_res_109_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_Iter_step__append_match__1_splitter___redArg(
    mut v_x_110_: *mut crate::leanh::LeanObject,
    mut v_h__1_111_: *mut crate::leanh::LeanObject,
    mut v_h__2_112_: *mut crate::leanh::LeanObject,
    mut v_h__3_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_110_) {
        0 => {
            let mut v_it_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_113_);
            crate::leanh::lean_dec(v_h__2_112_);
            v_it_114_ = crate::leanh::lean_ctor_get(v_x_110_, 0);
            crate::leanh::lean_inc(v_it_114_);
            v_out_115_ = crate::leanh::lean_ctor_get(v_x_110_, 1);
            crate::leanh::lean_inc(v_out_115_);
            crate::leanh::lean_dec_ref_known(v_x_110_, 2);
            v___x_116_ = crate::leanh::lean_apply_3(
                v_h__1_111_,
                v_it_114_,
                v_out_115_,
                crate::leanh::lean_box(0),
            );
            return v___x_116_;
        }
        1 => {
            let mut v_it_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_113_);
            crate::leanh::lean_dec(v_h__1_111_);
            v_it_117_ = crate::leanh::lean_ctor_get(v_x_110_, 0);
            crate::leanh::lean_inc(v_it_117_);
            crate::leanh::lean_dec_ref_known(v_x_110_, 1);
            v___x_118_ =
                crate::leanh::lean_apply_2(v_h__2_112_, v_it_117_, crate::leanh::lean_box(0));
            return v___x_118_;
        }
        _ => {
            let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_112_);
            crate::leanh::lean_dec(v_h__1_111_);
            v___x_119_ = crate::leanh::lean_apply_1(v_h__3_113_, crate::leanh::lean_box(0));
            return v___x_119_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_Iter_step__append_match__1_splitter(
    mut v_00_u03b1_u2081_120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_121_: *mut crate::leanh::LeanObject,
    mut v_inst_122_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_123_: *mut crate::leanh::LeanObject,
    mut v_motive_124_: *mut crate::leanh::LeanObject,
    mut v_x_125_: *mut crate::leanh::LeanObject,
    mut v_h__1_126_: *mut crate::leanh::LeanObject,
    mut v_h__2_127_: *mut crate::leanh::LeanObject,
    mut v_h__3_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_125_) {
        0 => {
            let mut v_it_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_128_);
            crate::leanh::lean_dec(v_h__2_127_);
            v_it_129_ = crate::leanh::lean_ctor_get(v_x_125_, 0);
            crate::leanh::lean_inc(v_it_129_);
            v_out_130_ = crate::leanh::lean_ctor_get(v_x_125_, 1);
            crate::leanh::lean_inc(v_out_130_);
            crate::leanh::lean_dec_ref_known(v_x_125_, 2);
            v___x_131_ = crate::leanh::lean_apply_3(
                v_h__1_126_,
                v_it_129_,
                v_out_130_,
                crate::leanh::lean_box(0),
            );
            return v___x_131_;
        }
        1 => {
            let mut v_it_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_128_);
            crate::leanh::lean_dec(v_h__1_126_);
            v_it_132_ = crate::leanh::lean_ctor_get(v_x_125_, 0);
            crate::leanh::lean_inc(v_it_132_);
            crate::leanh::lean_dec_ref_known(v_x_125_, 1);
            v___x_133_ =
                crate::leanh::lean_apply_2(v_h__2_127_, v_it_132_, crate::leanh::lean_box(0));
            return v___x_133_;
        }
        _ => {
            let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_127_);
            crate::leanh::lean_dec(v_h__1_126_);
            v___x_134_ = crate::leanh::lean_apply_1(v_h__3_128_, crate::leanh::lean_box(0));
            return v___x_134_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_Iter_step__append_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_135_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_136_: *mut crate::leanh::LeanObject,
    mut v_inst_137_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_138_: *mut crate::leanh::LeanObject,
    mut v_motive_139_: *mut crate::leanh::LeanObject,
    mut v_x_140_: *mut crate::leanh::LeanObject,
    mut v_h__1_141_: *mut crate::leanh::LeanObject,
    mut v_h__2_142_: *mut crate::leanh::LeanObject,
    mut v_h__3_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_144_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Append_0__Std_Iter_step__append_match__1_splitter(v_00_u03b1_u2081_135_, v_00_u03b2_136_, v_inst_137_, v_it_u2081_138_, v_motive_139_, v_x_140_, v_h__1_141_, v_h__2_142_, v_h__3_143_);
    crate::leanh::lean_dec(v_it_u2081_138_);
    crate::leanh::lean_dec(v_inst_137_);
    return v_res_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Append(builtin);
}
