// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CompactLRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATCheckerSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(
    mut v_step_77_: *mut crate::leanh::LeanObject,
    mut v_h__1_78_: *mut crate::leanh::LeanObject,
    mut v_h__2_79_: *mut crate::leanh::LeanObject,
    mut v_h__3_80_: *mut crate::leanh::LeanObject,
    mut v_h__4_81_: *mut crate::leanh::LeanObject,
    mut v_h__5_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_77_) == 0 {
        let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_82_);
        crate::leanh::lean_dec(v_h__4_81_);
        crate::leanh::lean_dec(v_h__3_80_);
        crate::leanh::lean_dec(v_h__2_79_);
        v___x_83_ = crate::leanh::lean_box(0);
        v___x_84_ = crate::leanh::lean_apply_1(v_h__1_78_, v___x_83_);
        return v___x_84_;
    } else {
        let mut v_val_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_78_);
        v_val_85_ = crate::leanh::lean_ctor_get(v_step_77_, 0);
        crate::leanh::lean_inc(v_val_85_);
        crate::leanh::lean_dec_ref_known(v_step_77_, 1);
        match crate::leanh::lean_obj_tag(v_val_85_) {
            0 => {
                let mut v_id_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_82_);
                crate::leanh::lean_dec(v_h__4_81_);
                crate::leanh::lean_dec(v_h__3_80_);
                v_id_86_ = crate::leanh::lean_ctor_get(v_val_85_, 0);
                crate::leanh::lean_inc(v_id_86_);
                v_rupHints_87_ = crate::leanh::lean_ctor_get(v_val_85_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_87_);
                crate::leanh::lean_dec_ref_known(v_val_85_, 2);
                v___x_88_ = crate::leanh::lean_apply_2(v_h__2_79_, v_id_86_, v_rupHints_87_);
                return v___x_88_;
            }
            1 => {
                let mut v_id_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_82_);
                crate::leanh::lean_dec(v_h__4_81_);
                crate::leanh::lean_dec(v_h__2_79_);
                v_id_89_ = crate::leanh::lean_ctor_get(v_val_85_, 0);
                crate::leanh::lean_inc(v_id_89_);
                v_c_90_ = crate::leanh::lean_ctor_get(v_val_85_, 1);
                crate::leanh::lean_inc(v_c_90_);
                v_rupHints_91_ = crate::leanh::lean_ctor_get(v_val_85_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_91_);
                crate::leanh::lean_dec_ref_known(v_val_85_, 3);
                v___x_92_ =
                    crate::leanh::lean_apply_3(v_h__3_80_, v_id_89_, v_c_90_, v_rupHints_91_);
                return v___x_92_;
            }
            2 => {
                let mut v_id_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_82_);
                crate::leanh::lean_dec(v_h__3_80_);
                crate::leanh::lean_dec(v_h__2_79_);
                v_id_93_ = crate::leanh::lean_ctor_get(v_val_85_, 0);
                crate::leanh::lean_inc(v_id_93_);
                v_c_94_ = crate::leanh::lean_ctor_get(v_val_85_, 1);
                crate::leanh::lean_inc(v_c_94_);
                v_pivot_95_ = crate::leanh::lean_ctor_get(v_val_85_, 2);
                crate::leanh::lean_inc_ref(v_pivot_95_);
                v_rupHints_96_ = crate::leanh::lean_ctor_get(v_val_85_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_96_);
                v_ratHints_97_ = crate::leanh::lean_ctor_get(v_val_85_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_97_);
                crate::leanh::lean_dec_ref_known(v_val_85_, 5);
                v___x_98_ = crate::leanh::lean_apply_5(
                    v_h__4_81_,
                    v_id_93_,
                    v_c_94_,
                    v_pivot_95_,
                    v_rupHints_96_,
                    v_ratHints_97_,
                );
                return v___x_98_;
            }
            _ => {
                let mut v_ids_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_81_);
                crate::leanh::lean_dec(v_h__3_80_);
                crate::leanh::lean_dec(v_h__2_79_);
                v_ids_99_ = crate::leanh::lean_ctor_get(v_val_85_, 0);
                crate::leanh::lean_inc_ref(v_ids_99_);
                crate::leanh::lean_dec_ref_known(v_val_85_, 1);
                v___x_100_ = crate::leanh::lean_apply_1(v_h__5_82_, v_ids_99_);
                return v___x_100_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_101_: *mut crate::leanh::LeanObject,
    mut v_motive_102_: *mut crate::leanh::LeanObject,
    mut v_step_103_: *mut crate::leanh::LeanObject,
    mut v_h__1_104_: *mut crate::leanh::LeanObject,
    mut v_h__2_105_: *mut crate::leanh::LeanObject,
    mut v_h__3_106_: *mut crate::leanh::LeanObject,
    mut v_h__4_107_: *mut crate::leanh::LeanObject,
    mut v_h__5_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_103_) == 0 {
        let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_108_);
        crate::leanh::lean_dec(v_h__4_107_);
        crate::leanh::lean_dec(v_h__3_106_);
        crate::leanh::lean_dec(v_h__2_105_);
        v___x_109_ = crate::leanh::lean_box(0);
        v___x_110_ = crate::leanh::lean_apply_1(v_h__1_104_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_104_);
        v_val_111_ = crate::leanh::lean_ctor_get(v_step_103_, 0);
        crate::leanh::lean_inc(v_val_111_);
        crate::leanh::lean_dec_ref_known(v_step_103_, 1);
        match crate::leanh::lean_obj_tag(v_val_111_) {
            0 => {
                let mut v_id_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_108_);
                crate::leanh::lean_dec(v_h__4_107_);
                crate::leanh::lean_dec(v_h__3_106_);
                v_id_112_ = crate::leanh::lean_ctor_get(v_val_111_, 0);
                crate::leanh::lean_inc(v_id_112_);
                v_rupHints_113_ = crate::leanh::lean_ctor_get(v_val_111_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_113_);
                crate::leanh::lean_dec_ref_known(v_val_111_, 2);
                v___x_114_ = crate::leanh::lean_apply_2(v_h__2_105_, v_id_112_, v_rupHints_113_);
                return v___x_114_;
            }
            1 => {
                let mut v_id_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_108_);
                crate::leanh::lean_dec(v_h__4_107_);
                crate::leanh::lean_dec(v_h__2_105_);
                v_id_115_ = crate::leanh::lean_ctor_get(v_val_111_, 0);
                crate::leanh::lean_inc(v_id_115_);
                v_c_116_ = crate::leanh::lean_ctor_get(v_val_111_, 1);
                crate::leanh::lean_inc(v_c_116_);
                v_rupHints_117_ = crate::leanh::lean_ctor_get(v_val_111_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_117_);
                crate::leanh::lean_dec_ref_known(v_val_111_, 3);
                v___x_118_ =
                    crate::leanh::lean_apply_3(v_h__3_106_, v_id_115_, v_c_116_, v_rupHints_117_);
                return v___x_118_;
            }
            2 => {
                let mut v_id_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_108_);
                crate::leanh::lean_dec(v_h__3_106_);
                crate::leanh::lean_dec(v_h__2_105_);
                v_id_119_ = crate::leanh::lean_ctor_get(v_val_111_, 0);
                crate::leanh::lean_inc(v_id_119_);
                v_c_120_ = crate::leanh::lean_ctor_get(v_val_111_, 1);
                crate::leanh::lean_inc(v_c_120_);
                v_pivot_121_ = crate::leanh::lean_ctor_get(v_val_111_, 2);
                crate::leanh::lean_inc_ref(v_pivot_121_);
                v_rupHints_122_ = crate::leanh::lean_ctor_get(v_val_111_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_122_);
                v_ratHints_123_ = crate::leanh::lean_ctor_get(v_val_111_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_123_);
                crate::leanh::lean_dec_ref_known(v_val_111_, 5);
                v___x_124_ = crate::leanh::lean_apply_5(
                    v_h__4_107_,
                    v_id_119_,
                    v_c_120_,
                    v_pivot_121_,
                    v_rupHints_122_,
                    v_ratHints_123_,
                );
                return v___x_124_;
            }
            _ => {
                let mut v_ids_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_107_);
                crate::leanh::lean_dec(v_h__3_106_);
                crate::leanh::lean_dec(v_h__2_105_);
                v_ids_125_ = crate::leanh::lean_ctor_get(v_val_111_, 0);
                crate::leanh::lean_inc_ref(v_ids_125_);
                crate::leanh::lean_dec_ref_known(v_val_111_, 1);
                v___x_126_ = crate::leanh::lean_apply_1(v_h__5_108_, v_ids_125_);
                return v___x_126_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_127_: *mut crate::leanh::LeanObject,
    mut v_motive_128_: *mut crate::leanh::LeanObject,
    mut v_step_129_: *mut crate::leanh::LeanObject,
    mut v_h__1_130_: *mut crate::leanh::LeanObject,
    mut v_h__2_131_: *mut crate::leanh::LeanObject,
    mut v_h__3_132_: *mut crate::leanh::LeanObject,
    mut v_h__4_133_: *mut crate::leanh::LeanObject,
    mut v_h__5_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_127_, v_motive_128_, v_step_129_, v_h__1_130_, v_h__2_131_, v_h__3_132_, v_h__4_133_, v_h__5_134_);
    crate::leanh::lean_dec(v_n_127_);
    return v_res_135_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_136_: *mut crate::leanh::LeanObject,
    mut v_h__1_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_138_ = crate::leanh::lean_ctor_get(v_x_136_, 0);
    crate::leanh::lean_inc(v_fst_138_);
    v_snd_139_ = crate::leanh::lean_ctor_get(v_x_136_, 1);
    crate::leanh::lean_inc(v_snd_139_);
    crate::leanh::lean_dec_ref(v_x_136_);
    v___x_140_ = crate::leanh::lean_apply_2(v_h__1_137_, v_fst_138_, v_snd_139_);
    return v___x_140_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_141_: *mut crate::leanh::LeanObject,
    mut v_motive_142_: *mut crate::leanh::LeanObject,
    mut v_x_143_: *mut crate::leanh::LeanObject,
    mut v_h__1_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_145_ = crate::leanh::lean_ctor_get(v_x_143_, 0);
    crate::leanh::lean_inc(v_fst_145_);
    v_snd_146_ = crate::leanh::lean_ctor_get(v_x_143_, 1);
    crate::leanh::lean_inc(v_snd_146_);
    crate::leanh::lean_dec_ref(v_x_143_);
    v___x_147_ = crate::leanh::lean_apply_2(v_h__1_144_, v_fst_145_, v_snd_146_);
    return v___x_147_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_148_: *mut crate::leanh::LeanObject,
    mut v_motive_149_: *mut crate::leanh::LeanObject,
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v_h__1_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_148_, v_motive_149_, v_x_150_, v_h__1_151_);
    crate::leanh::lean_dec(v_n_148_);
    return v_res_152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
}
