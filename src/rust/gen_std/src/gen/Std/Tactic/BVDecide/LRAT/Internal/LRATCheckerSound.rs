// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker Std.Tactic.BVDecide.LRAT.Internal.CNF Std.Tactic.BVDecide.LRAT.Internal.Actions
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CNF::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter___redArg(
    mut v_prf_95_: *mut leanh::LeanObject,
    mut v_h__1_96_: *mut leanh::LeanObject,
    mut v_h__2_97_: *mut leanh::LeanObject,
    mut v_h__3_98_: *mut leanh::LeanObject,
    mut v_h__4_99_: *mut leanh::LeanObject,
    mut v_h__5_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_prf_95_) == 0 {
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_100_);
        leanh::lean_dec(v_h__4_99_);
        leanh::lean_dec(v_h__3_98_);
        leanh::lean_dec(v_h__2_97_);
        v___x_101_ = leanh::lean_box(0);
        v___x_102_ = leanh::lean_apply_1(v_h__1_96_, v___x_101_);
        return v___x_102_;
    } else {
        let mut v_head_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_96_);
        v_head_103_ = leanh::lean_ctor_get(v_prf_95_, 0);
        leanh::lean_inc(v_head_103_);
        match leanh::lean_obj_tag(v_head_103_) {
            0 => {
                let mut v_tail_104_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_105_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_106_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_100_);
                leanh::lean_dec(v_h__4_99_);
                leanh::lean_dec(v_h__3_98_);
                v_tail_104_ = leanh::lean_ctor_get(v_prf_95_, 1);
                leanh::lean_inc(v_tail_104_);
                leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_105_ = leanh::lean_ctor_get(v_head_103_, 0);
                leanh::lean_inc(v_id_105_);
                v_rupHints_106_ = leanh::lean_ctor_get(v_head_103_, 1);
                leanh::lean_inc_ref(v_rupHints_106_);
                leanh::lean_dec_ref_known(v_head_103_, 2);
                v___x_107_ =
                    leanh::lean_apply_3(v_h__2_97_, v_id_105_, v_rupHints_106_, v_tail_104_);
                return v___x_107_;
            }
            1 => {
                let mut v_tail_108_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_109_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_110_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_111_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_100_);
                leanh::lean_dec(v_h__4_99_);
                leanh::lean_dec(v_h__2_97_);
                v_tail_108_ = leanh::lean_ctor_get(v_prf_95_, 1);
                leanh::lean_inc(v_tail_108_);
                leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_109_ = leanh::lean_ctor_get(v_head_103_, 0);
                leanh::lean_inc(v_id_109_);
                v_c_110_ = leanh::lean_ctor_get(v_head_103_, 1);
                leanh::lean_inc(v_c_110_);
                v_rupHints_111_ = leanh::lean_ctor_get(v_head_103_, 2);
                leanh::lean_inc_ref(v_rupHints_111_);
                leanh::lean_dec_ref_known(v_head_103_, 3);
                v___x_112_ = leanh::lean_apply_4(
                    v_h__3_98_,
                    v_id_109_,
                    v_c_110_,
                    v_rupHints_111_,
                    v_tail_108_,
                );
                return v___x_112_;
            }
            2 => {
                let mut v_tail_113_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_114_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_115_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_116_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_118_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_100_);
                leanh::lean_dec(v_h__3_98_);
                leanh::lean_dec(v_h__2_97_);
                v_tail_113_ = leanh::lean_ctor_get(v_prf_95_, 1);
                leanh::lean_inc(v_tail_113_);
                leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_114_ = leanh::lean_ctor_get(v_head_103_, 0);
                leanh::lean_inc(v_id_114_);
                v_c_115_ = leanh::lean_ctor_get(v_head_103_, 1);
                leanh::lean_inc(v_c_115_);
                v_pivot_116_ = leanh::lean_ctor_get(v_head_103_, 2);
                leanh::lean_inc_ref(v_pivot_116_);
                v_rupHints_117_ = leanh::lean_ctor_get(v_head_103_, 3);
                leanh::lean_inc_ref(v_rupHints_117_);
                v_ratHints_118_ = leanh::lean_ctor_get(v_head_103_, 4);
                leanh::lean_inc_ref(v_ratHints_118_);
                leanh::lean_dec_ref_known(v_head_103_, 5);
                v___x_119_ = leanh::lean_apply_6(
                    v_h__4_99_,
                    v_id_114_,
                    v_c_115_,
                    v_pivot_116_,
                    v_rupHints_117_,
                    v_ratHints_118_,
                    v_tail_113_,
                );
                return v___x_119_;
            }
            _ => {
                let mut v_tail_120_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ids_121_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_99_);
                leanh::lean_dec(v_h__3_98_);
                leanh::lean_dec(v_h__2_97_);
                v_tail_120_ = leanh::lean_ctor_get(v_prf_95_, 1);
                leanh::lean_inc(v_tail_120_);
                leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_ids_121_ = leanh::lean_ctor_get(v_head_103_, 0);
                leanh::lean_inc_ref(v_ids_121_);
                leanh::lean_dec_ref_known(v_head_103_, 1);
                v___x_122_ = leanh::lean_apply_2(v_h__5_100_, v_ids_121_, v_tail_120_);
                return v___x_122_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter(
    mut v_00_u03b1_123_: *mut leanh::LeanObject,
    mut v_00_u03b2_124_: *mut leanh::LeanObject,
    mut v_motive_125_: *mut leanh::LeanObject,
    mut v_prf_126_: *mut leanh::LeanObject,
    mut v_h__1_127_: *mut leanh::LeanObject,
    mut v_h__2_128_: *mut leanh::LeanObject,
    mut v_h__3_129_: *mut leanh::LeanObject,
    mut v_h__4_130_: *mut leanh::LeanObject,
    mut v_h__5_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_prf_126_) == 0 {
        let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_131_);
        leanh::lean_dec(v_h__4_130_);
        leanh::lean_dec(v_h__3_129_);
        leanh::lean_dec(v_h__2_128_);
        v___x_132_ = leanh::lean_box(0);
        v___x_133_ = leanh::lean_apply_1(v_h__1_127_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_head_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_127_);
        v_head_134_ = leanh::lean_ctor_get(v_prf_126_, 0);
        leanh::lean_inc(v_head_134_);
        match leanh::lean_obj_tag(v_head_134_) {
            0 => {
                let mut v_tail_135_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_136_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_137_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_131_);
                leanh::lean_dec(v_h__4_130_);
                leanh::lean_dec(v_h__3_129_);
                v_tail_135_ = leanh::lean_ctor_get(v_prf_126_, 1);
                leanh::lean_inc(v_tail_135_);
                leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_136_ = leanh::lean_ctor_get(v_head_134_, 0);
                leanh::lean_inc(v_id_136_);
                v_rupHints_137_ = leanh::lean_ctor_get(v_head_134_, 1);
                leanh::lean_inc_ref(v_rupHints_137_);
                leanh::lean_dec_ref_known(v_head_134_, 2);
                v___x_138_ = leanh::lean_apply_3(
                    v_h__2_128_,
                    v_id_136_,
                    v_rupHints_137_,
                    v_tail_135_,
                );
                return v___x_138_;
            }
            1 => {
                let mut v_tail_139_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_140_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_141_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_142_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_131_);
                leanh::lean_dec(v_h__4_130_);
                leanh::lean_dec(v_h__2_128_);
                v_tail_139_ = leanh::lean_ctor_get(v_prf_126_, 1);
                leanh::lean_inc(v_tail_139_);
                leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_140_ = leanh::lean_ctor_get(v_head_134_, 0);
                leanh::lean_inc(v_id_140_);
                v_c_141_ = leanh::lean_ctor_get(v_head_134_, 1);
                leanh::lean_inc(v_c_141_);
                v_rupHints_142_ = leanh::lean_ctor_get(v_head_134_, 2);
                leanh::lean_inc_ref(v_rupHints_142_);
                leanh::lean_dec_ref_known(v_head_134_, 3);
                v___x_143_ = leanh::lean_apply_4(
                    v_h__3_129_,
                    v_id_140_,
                    v_c_141_,
                    v_rupHints_142_,
                    v_tail_139_,
                );
                return v___x_143_;
            }
            2 => {
                let mut v_tail_144_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_145_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_146_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_147_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_148_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_149_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_131_);
                leanh::lean_dec(v_h__3_129_);
                leanh::lean_dec(v_h__2_128_);
                v_tail_144_ = leanh::lean_ctor_get(v_prf_126_, 1);
                leanh::lean_inc(v_tail_144_);
                leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_145_ = leanh::lean_ctor_get(v_head_134_, 0);
                leanh::lean_inc(v_id_145_);
                v_c_146_ = leanh::lean_ctor_get(v_head_134_, 1);
                leanh::lean_inc(v_c_146_);
                v_pivot_147_ = leanh::lean_ctor_get(v_head_134_, 2);
                leanh::lean_inc_ref(v_pivot_147_);
                v_rupHints_148_ = leanh::lean_ctor_get(v_head_134_, 3);
                leanh::lean_inc_ref(v_rupHints_148_);
                v_ratHints_149_ = leanh::lean_ctor_get(v_head_134_, 4);
                leanh::lean_inc_ref(v_ratHints_149_);
                leanh::lean_dec_ref_known(v_head_134_, 5);
                v___x_150_ = leanh::lean_apply_6(
                    v_h__4_130_,
                    v_id_145_,
                    v_c_146_,
                    v_pivot_147_,
                    v_rupHints_148_,
                    v_ratHints_149_,
                    v_tail_144_,
                );
                return v___x_150_;
            }
            _ => {
                let mut v_tail_151_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ids_152_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_130_);
                leanh::lean_dec(v_h__3_129_);
                leanh::lean_dec(v_h__2_128_);
                v_tail_151_ = leanh::lean_ctor_get(v_prf_126_, 1);
                leanh::lean_inc(v_tail_151_);
                leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_ids_152_ = leanh::lean_ctor_get(v_head_134_, 0);
                leanh::lean_inc_ref(v_ids_152_);
                leanh::lean_dec_ref_known(v_head_134_, 1);
                v___x_153_ = leanh::lean_apply_2(v_h__5_131_, v_ids_152_, v_tail_151_);
                return v___x_153_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(
    mut v_x_154_: *mut leanh::LeanObject,
    mut v_h__1_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_156_ = leanh::lean_ctor_get(v_x_154_, 0);
    leanh::lean_inc(v_fst_156_);
    v_snd_157_ = leanh::lean_ctor_get(v_x_154_, 1);
    leanh::lean_inc(v_snd_157_);
    leanh::lean_dec_ref(v_x_154_);
    v___x_158_ = leanh::lean_apply_2(v_h__1_155_, v_fst_156_, v_snd_157_);
    return v___x_158_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(
    mut v_00_u03c3_159_: *mut leanh::LeanObject,
    mut v_motive_160_: *mut leanh::LeanObject,
    mut v_x_161_: *mut leanh::LeanObject,
    mut v_h__1_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_163_ = leanh::lean_ctor_get(v_x_161_, 0);
    leanh::lean_inc(v_fst_163_);
    v_snd_164_ = leanh::lean_ctor_get(v_x_161_, 1);
    leanh::lean_inc(v_snd_164_);
    leanh::lean_dec_ref(v_x_161_);
    v___x_165_ = leanh::lean_apply_2(v_h__1_162_, v_fst_163_, v_snd_164_);
    return v___x_165_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(
    mut v_x_166_: *mut leanh::LeanObject,
    mut v_h__1_167_: *mut leanh::LeanObject,
    mut v_h__2_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_166_) == 2 {
        let mut v_id_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pivot_171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rupHints_172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ratHints_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_168_);
        v_id_169_ = leanh::lean_ctor_get(v_x_166_, 0);
        leanh::lean_inc(v_id_169_);
        v_c_170_ = leanh::lean_ctor_get(v_x_166_, 1);
        leanh::lean_inc(v_c_170_);
        v_pivot_171_ = leanh::lean_ctor_get(v_x_166_, 2);
        leanh::lean_inc_ref(v_pivot_171_);
        v_rupHints_172_ = leanh::lean_ctor_get(v_x_166_, 3);
        leanh::lean_inc_ref(v_rupHints_172_);
        v_ratHints_173_ = leanh::lean_ctor_get(v_x_166_, 4);
        leanh::lean_inc_ref(v_ratHints_173_);
        leanh::lean_dec_ref_known(v_x_166_, 5);
        v___x_174_ = leanh::lean_apply_5(
            v_h__1_167_,
            v_id_169_,
            v_c_170_,
            v_pivot_171_,
            v_rupHints_172_,
            v_ratHints_173_,
        );
        return v___x_174_;
    } else {
        let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_167_);
        v___x_175_ = leanh::lean_apply_2(v_h__2_168_, v_x_166_, leanh::lean_box(0));
        return v___x_175_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(
    mut v_00_u03b1_176_: *mut leanh::LeanObject,
    mut v_00_u03b2_177_: *mut leanh::LeanObject,
    mut v_motive_178_: *mut leanh::LeanObject,
    mut v_x_179_: *mut leanh::LeanObject,
    mut v_h__1_180_: *mut leanh::LeanObject,
    mut v_h__2_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_179_) == 2 {
        let mut v_id_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pivot_184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rupHints_185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ratHints_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_181_);
        v_id_182_ = leanh::lean_ctor_get(v_x_179_, 0);
        leanh::lean_inc(v_id_182_);
        v_c_183_ = leanh::lean_ctor_get(v_x_179_, 1);
        leanh::lean_inc(v_c_183_);
        v_pivot_184_ = leanh::lean_ctor_get(v_x_179_, 2);
        leanh::lean_inc_ref(v_pivot_184_);
        v_rupHints_185_ = leanh::lean_ctor_get(v_x_179_, 3);
        leanh::lean_inc_ref(v_rupHints_185_);
        v_ratHints_186_ = leanh::lean_ctor_get(v_x_179_, 4);
        leanh::lean_inc_ref(v_ratHints_186_);
        leanh::lean_dec_ref_known(v_x_179_, 5);
        v___x_187_ = leanh::lean_apply_5(
            v_h__1_180_,
            v_id_182_,
            v_c_183_,
            v_pivot_184_,
            v_rupHints_185_,
            v_ratHints_186_,
        );
        return v___x_187_;
    } else {
        let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_180_);
        v___x_188_ = leanh::lean_apply_2(v_h__2_181_, v_x_179_, leanh::lean_box(0));
        return v___x_188_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
}