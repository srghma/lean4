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
    mut v_prf_95_: *mut crate::leanh::LeanObject,
    mut v_h__1_96_: *mut crate::leanh::LeanObject,
    mut v_h__2_97_: *mut crate::leanh::LeanObject,
    mut v_h__3_98_: *mut crate::leanh::LeanObject,
    mut v_h__4_99_: *mut crate::leanh::LeanObject,
    mut v_h__5_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_prf_95_) == 0 {
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_100_);
        crate::leanh::lean_dec(v_h__4_99_);
        crate::leanh::lean_dec(v_h__3_98_);
        crate::leanh::lean_dec(v_h__2_97_);
        v___x_101_ = crate::leanh::lean_box(0);
        v___x_102_ = crate::leanh::lean_apply_1(v_h__1_96_, v___x_101_);
        return v___x_102_;
    } else {
        let mut v_head_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_96_);
        v_head_103_ = crate::leanh::lean_ctor_get(v_prf_95_, 0);
        crate::leanh::lean_inc(v_head_103_);
        match crate::leanh::lean_obj_tag(v_head_103_) {
            0 => {
                let mut v_tail_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_100_);
                crate::leanh::lean_dec(v_h__4_99_);
                crate::leanh::lean_dec(v_h__3_98_);
                v_tail_104_ = crate::leanh::lean_ctor_get(v_prf_95_, 1);
                crate::leanh::lean_inc(v_tail_104_);
                crate::leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_105_ = crate::leanh::lean_ctor_get(v_head_103_, 0);
                crate::leanh::lean_inc(v_id_105_);
                v_rupHints_106_ = crate::leanh::lean_ctor_get(v_head_103_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_106_);
                crate::leanh::lean_dec_ref_known(v_head_103_, 2);
                v___x_107_ =
                    crate::leanh::lean_apply_3(v_h__2_97_, v_id_105_, v_rupHints_106_, v_tail_104_);
                return v___x_107_;
            }
            1 => {
                let mut v_tail_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_100_);
                crate::leanh::lean_dec(v_h__4_99_);
                crate::leanh::lean_dec(v_h__2_97_);
                v_tail_108_ = crate::leanh::lean_ctor_get(v_prf_95_, 1);
                crate::leanh::lean_inc(v_tail_108_);
                crate::leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_109_ = crate::leanh::lean_ctor_get(v_head_103_, 0);
                crate::leanh::lean_inc(v_id_109_);
                v_c_110_ = crate::leanh::lean_ctor_get(v_head_103_, 1);
                crate::leanh::lean_inc(v_c_110_);
                v_rupHints_111_ = crate::leanh::lean_ctor_get(v_head_103_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_111_);
                crate::leanh::lean_dec_ref_known(v_head_103_, 3);
                v___x_112_ = crate::leanh::lean_apply_4(
                    v_h__3_98_,
                    v_id_109_,
                    v_c_110_,
                    v_rupHints_111_,
                    v_tail_108_,
                );
                return v___x_112_;
            }
            2 => {
                let mut v_tail_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_100_);
                crate::leanh::lean_dec(v_h__3_98_);
                crate::leanh::lean_dec(v_h__2_97_);
                v_tail_113_ = crate::leanh::lean_ctor_get(v_prf_95_, 1);
                crate::leanh::lean_inc(v_tail_113_);
                crate::leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_id_114_ = crate::leanh::lean_ctor_get(v_head_103_, 0);
                crate::leanh::lean_inc(v_id_114_);
                v_c_115_ = crate::leanh::lean_ctor_get(v_head_103_, 1);
                crate::leanh::lean_inc(v_c_115_);
                v_pivot_116_ = crate::leanh::lean_ctor_get(v_head_103_, 2);
                crate::leanh::lean_inc_ref(v_pivot_116_);
                v_rupHints_117_ = crate::leanh::lean_ctor_get(v_head_103_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_117_);
                v_ratHints_118_ = crate::leanh::lean_ctor_get(v_head_103_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_118_);
                crate::leanh::lean_dec_ref_known(v_head_103_, 5);
                v___x_119_ = crate::leanh::lean_apply_6(
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
                let mut v_tail_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ids_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_99_);
                crate::leanh::lean_dec(v_h__3_98_);
                crate::leanh::lean_dec(v_h__2_97_);
                v_tail_120_ = crate::leanh::lean_ctor_get(v_prf_95_, 1);
                crate::leanh::lean_inc(v_tail_120_);
                crate::leanh::lean_dec_ref_known(v_prf_95_, 2);
                v_ids_121_ = crate::leanh::lean_ctor_get(v_head_103_, 0);
                crate::leanh::lean_inc_ref(v_ids_121_);
                crate::leanh::lean_dec_ref_known(v_head_103_, 1);
                v___x_122_ = crate::leanh::lean_apply_2(v_h__5_100_, v_ids_121_, v_tail_120_);
                return v___x_122_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter(
    mut v_00_u03b1_123_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_124_: *mut crate::leanh::LeanObject,
    mut v_motive_125_: *mut crate::leanh::LeanObject,
    mut v_prf_126_: *mut crate::leanh::LeanObject,
    mut v_h__1_127_: *mut crate::leanh::LeanObject,
    mut v_h__2_128_: *mut crate::leanh::LeanObject,
    mut v_h__3_129_: *mut crate::leanh::LeanObject,
    mut v_h__4_130_: *mut crate::leanh::LeanObject,
    mut v_h__5_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_prf_126_) == 0 {
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_131_);
        crate::leanh::lean_dec(v_h__4_130_);
        crate::leanh::lean_dec(v_h__3_129_);
        crate::leanh::lean_dec(v_h__2_128_);
        v___x_132_ = crate::leanh::lean_box(0);
        v___x_133_ = crate::leanh::lean_apply_1(v_h__1_127_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_head_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_127_);
        v_head_134_ = crate::leanh::lean_ctor_get(v_prf_126_, 0);
        crate::leanh::lean_inc(v_head_134_);
        match crate::leanh::lean_obj_tag(v_head_134_) {
            0 => {
                let mut v_tail_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_131_);
                crate::leanh::lean_dec(v_h__4_130_);
                crate::leanh::lean_dec(v_h__3_129_);
                v_tail_135_ = crate::leanh::lean_ctor_get(v_prf_126_, 1);
                crate::leanh::lean_inc(v_tail_135_);
                crate::leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_136_ = crate::leanh::lean_ctor_get(v_head_134_, 0);
                crate::leanh::lean_inc(v_id_136_);
                v_rupHints_137_ = crate::leanh::lean_ctor_get(v_head_134_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_137_);
                crate::leanh::lean_dec_ref_known(v_head_134_, 2);
                v___x_138_ = crate::leanh::lean_apply_3(
                    v_h__2_128_,
                    v_id_136_,
                    v_rupHints_137_,
                    v_tail_135_,
                );
                return v___x_138_;
            }
            1 => {
                let mut v_tail_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_131_);
                crate::leanh::lean_dec(v_h__4_130_);
                crate::leanh::lean_dec(v_h__2_128_);
                v_tail_139_ = crate::leanh::lean_ctor_get(v_prf_126_, 1);
                crate::leanh::lean_inc(v_tail_139_);
                crate::leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_140_ = crate::leanh::lean_ctor_get(v_head_134_, 0);
                crate::leanh::lean_inc(v_id_140_);
                v_c_141_ = crate::leanh::lean_ctor_get(v_head_134_, 1);
                crate::leanh::lean_inc(v_c_141_);
                v_rupHints_142_ = crate::leanh::lean_ctor_get(v_head_134_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_142_);
                crate::leanh::lean_dec_ref_known(v_head_134_, 3);
                v___x_143_ = crate::leanh::lean_apply_4(
                    v_h__3_129_,
                    v_id_140_,
                    v_c_141_,
                    v_rupHints_142_,
                    v_tail_139_,
                );
                return v___x_143_;
            }
            2 => {
                let mut v_tail_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_131_);
                crate::leanh::lean_dec(v_h__3_129_);
                crate::leanh::lean_dec(v_h__2_128_);
                v_tail_144_ = crate::leanh::lean_ctor_get(v_prf_126_, 1);
                crate::leanh::lean_inc(v_tail_144_);
                crate::leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_id_145_ = crate::leanh::lean_ctor_get(v_head_134_, 0);
                crate::leanh::lean_inc(v_id_145_);
                v_c_146_ = crate::leanh::lean_ctor_get(v_head_134_, 1);
                crate::leanh::lean_inc(v_c_146_);
                v_pivot_147_ = crate::leanh::lean_ctor_get(v_head_134_, 2);
                crate::leanh::lean_inc_ref(v_pivot_147_);
                v_rupHints_148_ = crate::leanh::lean_ctor_get(v_head_134_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_148_);
                v_ratHints_149_ = crate::leanh::lean_ctor_get(v_head_134_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_149_);
                crate::leanh::lean_dec_ref_known(v_head_134_, 5);
                v___x_150_ = crate::leanh::lean_apply_6(
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
                let mut v_tail_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ids_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_130_);
                crate::leanh::lean_dec(v_h__3_129_);
                crate::leanh::lean_dec(v_h__2_128_);
                v_tail_151_ = crate::leanh::lean_ctor_get(v_prf_126_, 1);
                crate::leanh::lean_inc(v_tail_151_);
                crate::leanh::lean_dec_ref_known(v_prf_126_, 2);
                v_ids_152_ = crate::leanh::lean_ctor_get(v_head_134_, 0);
                crate::leanh::lean_inc_ref(v_ids_152_);
                crate::leanh::lean_dec_ref_known(v_head_134_, 1);
                v___x_153_ = crate::leanh::lean_apply_2(v_h__5_131_, v_ids_152_, v_tail_151_);
                return v___x_153_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_h__1_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_156_ = crate::leanh::lean_ctor_get(v_x_154_, 0);
    crate::leanh::lean_inc(v_fst_156_);
    v_snd_157_ = crate::leanh::lean_ctor_get(v_x_154_, 1);
    crate::leanh::lean_inc(v_snd_157_);
    crate::leanh::lean_dec_ref(v_x_154_);
    v___x_158_ = crate::leanh::lean_apply_2(v_h__1_155_, v_fst_156_, v_snd_157_);
    return v___x_158_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(
    mut v_00_u03c3_159_: *mut crate::leanh::LeanObject,
    mut v_motive_160_: *mut crate::leanh::LeanObject,
    mut v_x_161_: *mut crate::leanh::LeanObject,
    mut v_h__1_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_163_ = crate::leanh::lean_ctor_get(v_x_161_, 0);
    crate::leanh::lean_inc(v_fst_163_);
    v_snd_164_ = crate::leanh::lean_ctor_get(v_x_161_, 1);
    crate::leanh::lean_inc(v_snd_164_);
    crate::leanh::lean_dec_ref(v_x_161_);
    v___x_165_ = crate::leanh::lean_apply_2(v_h__1_162_, v_fst_163_, v_snd_164_);
    return v___x_165_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_h__1_167_: *mut crate::leanh::LeanObject,
    mut v_h__2_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_166_) == 2 {
        let mut v_id_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pivot_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rupHints_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ratHints_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_168_);
        v_id_169_ = crate::leanh::lean_ctor_get(v_x_166_, 0);
        crate::leanh::lean_inc(v_id_169_);
        v_c_170_ = crate::leanh::lean_ctor_get(v_x_166_, 1);
        crate::leanh::lean_inc(v_c_170_);
        v_pivot_171_ = crate::leanh::lean_ctor_get(v_x_166_, 2);
        crate::leanh::lean_inc_ref(v_pivot_171_);
        v_rupHints_172_ = crate::leanh::lean_ctor_get(v_x_166_, 3);
        crate::leanh::lean_inc_ref(v_rupHints_172_);
        v_ratHints_173_ = crate::leanh::lean_ctor_get(v_x_166_, 4);
        crate::leanh::lean_inc_ref(v_ratHints_173_);
        crate::leanh::lean_dec_ref_known(v_x_166_, 5);
        v___x_174_ = crate::leanh::lean_apply_5(
            v_h__1_167_,
            v_id_169_,
            v_c_170_,
            v_pivot_171_,
            v_rupHints_172_,
            v_ratHints_173_,
        );
        return v___x_174_;
    } else {
        let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_167_);
        v___x_175_ = crate::leanh::lean_apply_2(v_h__2_168_, v_x_166_, crate::leanh::lean_box(0));
        return v___x_175_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(
    mut v_00_u03b1_176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_177_: *mut crate::leanh::LeanObject,
    mut v_motive_178_: *mut crate::leanh::LeanObject,
    mut v_x_179_: *mut crate::leanh::LeanObject,
    mut v_h__1_180_: *mut crate::leanh::LeanObject,
    mut v_h__2_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_179_) == 2 {
        let mut v_id_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pivot_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rupHints_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ratHints_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_181_);
        v_id_182_ = crate::leanh::lean_ctor_get(v_x_179_, 0);
        crate::leanh::lean_inc(v_id_182_);
        v_c_183_ = crate::leanh::lean_ctor_get(v_x_179_, 1);
        crate::leanh::lean_inc(v_c_183_);
        v_pivot_184_ = crate::leanh::lean_ctor_get(v_x_179_, 2);
        crate::leanh::lean_inc_ref(v_pivot_184_);
        v_rupHints_185_ = crate::leanh::lean_ctor_get(v_x_179_, 3);
        crate::leanh::lean_inc_ref(v_rupHints_185_);
        v_ratHints_186_ = crate::leanh::lean_ctor_get(v_x_179_, 4);
        crate::leanh::lean_inc_ref(v_ratHints_186_);
        crate::leanh::lean_dec_ref_known(v_x_179_, 5);
        v___x_187_ = crate::leanh::lean_apply_5(
            v_h__1_180_,
            v_id_182_,
            v_c_183_,
            v_pivot_184_,
            v_rupHints_185_,
            v_ratHints_186_,
        );
        return v___x_187_;
    } else {
        let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_180_);
        v___x_188_ = crate::leanh::lean_apply_2(v_h__2_181_, v_x_179_, crate::leanh::lean_box(0));
        return v___x_188_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
}
