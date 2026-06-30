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
    mut v_step_77_: *mut leanh::LeanObject,
    mut v_h__1_78_: *mut leanh::LeanObject,
    mut v_h__2_79_: *mut leanh::LeanObject,
    mut v_h__3_80_: *mut leanh::LeanObject,
    mut v_h__4_81_: *mut leanh::LeanObject,
    mut v_h__5_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_step_77_) == 0 {
        let mut v___x_83_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_82_);
        leanh::lean_dec(v_h__4_81_);
        leanh::lean_dec(v_h__3_80_);
        leanh::lean_dec(v_h__2_79_);
        v___x_83_ = leanh::lean_box(0);
        v___x_84_ = leanh::lean_apply_1(v_h__1_78_, v___x_83_);
        return v___x_84_;
    } else {
        let mut v_val_85_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_78_);
        v_val_85_ = leanh::lean_ctor_get(v_step_77_, 0);
        leanh::lean_inc(v_val_85_);
        leanh::lean_dec_ref_known(v_step_77_, 1);
        match leanh::lean_obj_tag(v_val_85_) {
            0 => {
                let mut v_id_86_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_87_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_82_);
                leanh::lean_dec(v_h__4_81_);
                leanh::lean_dec(v_h__3_80_);
                v_id_86_ = leanh::lean_ctor_get(v_val_85_, 0);
                leanh::lean_inc(v_id_86_);
                v_rupHints_87_ = leanh::lean_ctor_get(v_val_85_, 1);
                leanh::lean_inc_ref(v_rupHints_87_);
                leanh::lean_dec_ref_known(v_val_85_, 2);
                v___x_88_ = leanh::lean_apply_2(v_h__2_79_, v_id_86_, v_rupHints_87_);
                return v___x_88_;
            }
            1 => {
                let mut v_id_89_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_90_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_91_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_82_);
                leanh::lean_dec(v_h__4_81_);
                leanh::lean_dec(v_h__2_79_);
                v_id_89_ = leanh::lean_ctor_get(v_val_85_, 0);
                leanh::lean_inc(v_id_89_);
                v_c_90_ = leanh::lean_ctor_get(v_val_85_, 1);
                leanh::lean_inc(v_c_90_);
                v_rupHints_91_ = leanh::lean_ctor_get(v_val_85_, 2);
                leanh::lean_inc_ref(v_rupHints_91_);
                leanh::lean_dec_ref_known(v_val_85_, 3);
                v___x_92_ =
                    leanh::lean_apply_3(v_h__3_80_, v_id_89_, v_c_90_, v_rupHints_91_);
                return v___x_92_;
            }
            2 => {
                let mut v_id_93_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_94_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_95_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_96_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_97_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_82_);
                leanh::lean_dec(v_h__3_80_);
                leanh::lean_dec(v_h__2_79_);
                v_id_93_ = leanh::lean_ctor_get(v_val_85_, 0);
                leanh::lean_inc(v_id_93_);
                v_c_94_ = leanh::lean_ctor_get(v_val_85_, 1);
                leanh::lean_inc(v_c_94_);
                v_pivot_95_ = leanh::lean_ctor_get(v_val_85_, 2);
                leanh::lean_inc_ref(v_pivot_95_);
                v_rupHints_96_ = leanh::lean_ctor_get(v_val_85_, 3);
                leanh::lean_inc_ref(v_rupHints_96_);
                v_ratHints_97_ = leanh::lean_ctor_get(v_val_85_, 4);
                leanh::lean_inc_ref(v_ratHints_97_);
                leanh::lean_dec_ref_known(v_val_85_, 5);
                v___x_98_ = leanh::lean_apply_5(
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
                let mut v_ids_99_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_81_);
                leanh::lean_dec(v_h__3_80_);
                leanh::lean_dec(v_h__2_79_);
                v_ids_99_ = leanh::lean_ctor_get(v_val_85_, 0);
                leanh::lean_inc_ref(v_ids_99_);
                leanh::lean_dec_ref_known(v_val_85_, 1);
                v___x_100_ = leanh::lean_apply_1(v_h__5_82_, v_ids_99_);
                return v___x_100_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_101_: *mut leanh::LeanObject,
    mut v_motive_102_: *mut leanh::LeanObject,
    mut v_step_103_: *mut leanh::LeanObject,
    mut v_h__1_104_: *mut leanh::LeanObject,
    mut v_h__2_105_: *mut leanh::LeanObject,
    mut v_h__3_106_: *mut leanh::LeanObject,
    mut v_h__4_107_: *mut leanh::LeanObject,
    mut v_h__5_108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_step_103_) == 0 {
        let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_108_);
        leanh::lean_dec(v_h__4_107_);
        leanh::lean_dec(v_h__3_106_);
        leanh::lean_dec(v_h__2_105_);
        v___x_109_ = leanh::lean_box(0);
        v___x_110_ = leanh::lean_apply_1(v_h__1_104_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_104_);
        v_val_111_ = leanh::lean_ctor_get(v_step_103_, 0);
        leanh::lean_inc(v_val_111_);
        leanh::lean_dec_ref_known(v_step_103_, 1);
        match leanh::lean_obj_tag(v_val_111_) {
            0 => {
                let mut v_id_112_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_113_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_108_);
                leanh::lean_dec(v_h__4_107_);
                leanh::lean_dec(v_h__3_106_);
                v_id_112_ = leanh::lean_ctor_get(v_val_111_, 0);
                leanh::lean_inc(v_id_112_);
                v_rupHints_113_ = leanh::lean_ctor_get(v_val_111_, 1);
                leanh::lean_inc_ref(v_rupHints_113_);
                leanh::lean_dec_ref_known(v_val_111_, 2);
                v___x_114_ = leanh::lean_apply_2(v_h__2_105_, v_id_112_, v_rupHints_113_);
                return v___x_114_;
            }
            1 => {
                let mut v_id_115_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_116_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_108_);
                leanh::lean_dec(v_h__4_107_);
                leanh::lean_dec(v_h__2_105_);
                v_id_115_ = leanh::lean_ctor_get(v_val_111_, 0);
                leanh::lean_inc(v_id_115_);
                v_c_116_ = leanh::lean_ctor_get(v_val_111_, 1);
                leanh::lean_inc(v_c_116_);
                v_rupHints_117_ = leanh::lean_ctor_get(v_val_111_, 2);
                leanh::lean_inc_ref(v_rupHints_117_);
                leanh::lean_dec_ref_known(v_val_111_, 3);
                v___x_118_ =
                    leanh::lean_apply_3(v_h__3_106_, v_id_115_, v_c_116_, v_rupHints_117_);
                return v___x_118_;
            }
            2 => {
                let mut v_id_119_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_120_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_121_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_122_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_123_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_108_);
                leanh::lean_dec(v_h__3_106_);
                leanh::lean_dec(v_h__2_105_);
                v_id_119_ = leanh::lean_ctor_get(v_val_111_, 0);
                leanh::lean_inc(v_id_119_);
                v_c_120_ = leanh::lean_ctor_get(v_val_111_, 1);
                leanh::lean_inc(v_c_120_);
                v_pivot_121_ = leanh::lean_ctor_get(v_val_111_, 2);
                leanh::lean_inc_ref(v_pivot_121_);
                v_rupHints_122_ = leanh::lean_ctor_get(v_val_111_, 3);
                leanh::lean_inc_ref(v_rupHints_122_);
                v_ratHints_123_ = leanh::lean_ctor_get(v_val_111_, 4);
                leanh::lean_inc_ref(v_ratHints_123_);
                leanh::lean_dec_ref_known(v_val_111_, 5);
                v___x_124_ = leanh::lean_apply_5(
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
                let mut v_ids_125_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_107_);
                leanh::lean_dec(v_h__3_106_);
                leanh::lean_dec(v_h__2_105_);
                v_ids_125_ = leanh::lean_ctor_get(v_val_111_, 0);
                leanh::lean_inc_ref(v_ids_125_);
                leanh::lean_dec_ref_known(v_val_111_, 1);
                v___x_126_ = leanh::lean_apply_1(v_h__5_108_, v_ids_125_);
                return v___x_126_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_127_: *mut leanh::LeanObject,
    mut v_motive_128_: *mut leanh::LeanObject,
    mut v_step_129_: *mut leanh::LeanObject,
    mut v_h__1_130_: *mut leanh::LeanObject,
    mut v_h__2_131_: *mut leanh::LeanObject,
    mut v_h__3_132_: *mut leanh::LeanObject,
    mut v_h__4_133_: *mut leanh::LeanObject,
    mut v_h__5_134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_127_, v_motive_128_, v_step_129_, v_h__1_130_, v_h__2_131_, v_h__3_132_, v_h__4_133_, v_h__5_134_);
    leanh::lean_dec(v_n_127_);
    return v_res_135_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_136_: *mut leanh::LeanObject,
    mut v_h__1_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_138_ = leanh::lean_ctor_get(v_x_136_, 0);
    leanh::lean_inc(v_fst_138_);
    v_snd_139_ = leanh::lean_ctor_get(v_x_136_, 1);
    leanh::lean_inc(v_snd_139_);
    leanh::lean_dec_ref(v_x_136_);
    v___x_140_ = leanh::lean_apply_2(v_h__1_137_, v_fst_138_, v_snd_139_);
    return v___x_140_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_141_: *mut leanh::LeanObject,
    mut v_motive_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_145_ = leanh::lean_ctor_get(v_x_143_, 0);
    leanh::lean_inc(v_fst_145_);
    v_snd_146_ = leanh::lean_ctor_get(v_x_143_, 1);
    leanh::lean_inc(v_snd_146_);
    leanh::lean_dec_ref(v_x_143_);
    v___x_147_ = leanh::lean_apply_2(v_h__1_144_, v_fst_145_, v_snd_146_);
    return v___x_147_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_148_: *mut leanh::LeanObject,
    mut v_motive_149_: *mut leanh::LeanObject,
    mut v_x_150_: *mut leanh::LeanObject,
    mut v_h__1_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_148_, v_motive_149_, v_x_150_, v_h__1_151_);
    leanh::lean_dec(v_n_148_);
    return v_res_152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
}