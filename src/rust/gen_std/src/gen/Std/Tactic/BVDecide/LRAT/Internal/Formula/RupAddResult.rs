// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas Init.GrindInstances.ToInt Init.ByCases Init.Data.Array.Bootstrap Init.Data.Fin.Lemmas Init.Data.Int.OfNat Init.Data.Nat.Linear Init.Data.Nat.Simproc
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::GrindInstances::ToInt::{
    initialize_Init_GrindInstances_ToInt, runtime_initialize_Init_GrindInstances_ToInt,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Lemmas::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(
    mut v_x_138_: *mut leanh::LeanObject,
    mut v_x_139_: *mut leanh::LeanObject,
    mut v_h__1_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_141_ = leanh::lean_ctor_get(v_x_139_, 0);
    leanh::lean_inc(v_fst_141_);
    v_snd_142_ = leanh::lean_ctor_get(v_x_139_, 1);
    leanh::lean_inc(v_snd_142_);
    leanh::lean_dec_ref(v_x_139_);
    v___x_143_ = leanh::lean_apply_3(v_h__1_140_, v_x_138_, v_fst_141_, v_snd_142_);
    return v___x_143_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(
    mut v_n_144_: *mut leanh::LeanObject,
    mut v_motive_145_: *mut leanh::LeanObject,
    mut v_x_146_: *mut leanh::LeanObject,
    mut v_x_147_: *mut leanh::LeanObject,
    mut v_h__1_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_149_ = leanh::lean_ctor_get(v_x_147_, 0);
    leanh::lean_inc(v_fst_149_);
    v_snd_150_ = leanh::lean_ctor_get(v_x_147_, 1);
    leanh::lean_inc(v_snd_150_);
    leanh::lean_dec_ref(v_x_147_);
    v___x_151_ = leanh::lean_apply_3(v_h__1_148_, v_x_146_, v_fst_149_, v_snd_150_);
    return v___x_151_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(
    mut v_n_152_: *mut leanh::LeanObject,
    mut v_motive_153_: *mut leanh::LeanObject,
    mut v_x_154_: *mut leanh::LeanObject,
    mut v_x_155_: *mut leanh::LeanObject,
    mut v_h__1_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_157_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(v_n_152_, v_motive_153_, v_x_154_, v_x_155_, v_h__1_156_);
    leanh::lean_dec(v_n_152_);
    return v_res_157_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_158_: *mut leanh::LeanObject,
    mut v_h__1_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_160_ = leanh::lean_ctor_get(v_f_158_, 0);
    leanh::lean_inc_ref(v_clauses_160_);
    v_rupUnits_161_ = leanh::lean_ctor_get(v_f_158_, 1);
    leanh::lean_inc_ref(v_rupUnits_161_);
    v_ratUnits_162_ = leanh::lean_ctor_get(v_f_158_, 2);
    leanh::lean_inc_ref(v_ratUnits_162_);
    v_assignments_163_ = leanh::lean_ctor_get(v_f_158_, 3);
    leanh::lean_inc_ref(v_assignments_163_);
    leanh::lean_dec_ref(v_f_158_);
    v___x_164_ = leanh::lean_apply_4(
        v_h__1_159_,
        v_clauses_160_,
        v_rupUnits_161_,
        v_ratUnits_162_,
        v_assignments_163_,
    );
    return v___x_164_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_165_: *mut leanh::LeanObject,
    mut v_motive_166_: *mut leanh::LeanObject,
    mut v_f_167_: *mut leanh::LeanObject,
    mut v_h__1_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_169_ = leanh::lean_ctor_get(v_f_167_, 0);
    leanh::lean_inc_ref(v_clauses_169_);
    v_rupUnits_170_ = leanh::lean_ctor_get(v_f_167_, 1);
    leanh::lean_inc_ref(v_rupUnits_170_);
    v_ratUnits_171_ = leanh::lean_ctor_get(v_f_167_, 2);
    leanh::lean_inc_ref(v_ratUnits_171_);
    v_assignments_172_ = leanh::lean_ctor_get(v_f_167_, 3);
    leanh::lean_inc_ref(v_assignments_172_);
    leanh::lean_dec_ref(v_f_167_);
    v___x_173_ = leanh::lean_apply_4(
        v_h__1_168_,
        v_clauses_169_,
        v_rupUnits_170_,
        v_ratUnits_171_,
        v_assignments_172_,
    );
    return v___x_173_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_174_: *mut leanh::LeanObject,
    mut v_motive_175_: *mut leanh::LeanObject,
    mut v_f_176_: *mut leanh::LeanObject,
    mut v_h__1_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_178_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_174_, v_motive_175_, v_f_176_, v_h__1_177_);
    leanh::lean_dec(v_n_174_);
    return v_res_178_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(
    mut v_x_179_: *mut leanh::LeanObject,
    mut v_h__1_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_181_ = leanh::lean_ctor_get(v_x_179_, 1);
    leanh::lean_inc(v_snd_181_);
    v_snd_182_ = leanh::lean_ctor_get(v_snd_181_, 1);
    leanh::lean_inc(v_snd_182_);
    v_fst_183_ = leanh::lean_ctor_get(v_x_179_, 0);
    leanh::lean_inc(v_fst_183_);
    leanh::lean_dec_ref(v_x_179_);
    v_fst_184_ = leanh::lean_ctor_get(v_snd_181_, 0);
    leanh::lean_inc(v_fst_184_);
    leanh::lean_dec(v_snd_181_);
    v_fst_185_ = leanh::lean_ctor_get(v_snd_182_, 0);
    leanh::lean_inc(v_fst_185_);
    v_snd_186_ = leanh::lean_ctor_get(v_snd_182_, 1);
    leanh::lean_inc(v_snd_186_);
    leanh::lean_dec(v_snd_182_);
    v___x_187_ =
        leanh::lean_apply_4(v_h__1_180_, v_fst_183_, v_fst_184_, v_fst_185_, v_snd_186_);
    return v___x_187_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(
    mut v_n_188_: *mut leanh::LeanObject,
    mut v_motive_189_: *mut leanh::LeanObject,
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_192_ = leanh::lean_ctor_get(v_x_190_, 1);
    leanh::lean_inc(v_snd_192_);
    v_snd_193_ = leanh::lean_ctor_get(v_snd_192_, 1);
    leanh::lean_inc(v_snd_193_);
    v_fst_194_ = leanh::lean_ctor_get(v_x_190_, 0);
    leanh::lean_inc(v_fst_194_);
    leanh::lean_dec_ref(v_x_190_);
    v_fst_195_ = leanh::lean_ctor_get(v_snd_192_, 0);
    leanh::lean_inc(v_fst_195_);
    leanh::lean_dec(v_snd_192_);
    v_fst_196_ = leanh::lean_ctor_get(v_snd_193_, 0);
    leanh::lean_inc(v_fst_196_);
    v_snd_197_ = leanh::lean_ctor_get(v_snd_193_, 1);
    leanh::lean_inc(v_snd_197_);
    leanh::lean_dec(v_snd_193_);
    v___x_198_ =
        leanh::lean_apply_4(v_h__1_191_, v_fst_194_, v_fst_195_, v_fst_196_, v_snd_197_);
    return v___x_198_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(
    mut v_n_199_: *mut leanh::LeanObject,
    mut v_motive_200_: *mut leanh::LeanObject,
    mut v_x_201_: *mut leanh::LeanObject,
    mut v_h__1_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_203_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(v_n_199_, v_motive_200_, v_x_201_, v_h__1_202_);
    leanh::lean_dec(v_n_199_);
    return v_res_203_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(
    mut v_x_204_: *mut leanh::LeanObject,
    mut v_h__1_205_: *mut leanh::LeanObject,
    mut v_h__2_206_: *mut leanh::LeanObject,
    mut v_h__3_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_204_) == 0 {
        let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_206_);
        leanh::lean_dec(v_h__1_205_);
        v___x_208_ = leanh::lean_box(0);
        v___x_209_ = leanh::lean_apply_1(v_h__3_207_, v___x_208_);
        return v___x_209_;
    } else {
        let mut v_val_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_207_);
        v_val_210_ = leanh::lean_ctor_get(v_x_204_, 0);
        leanh::lean_inc(v_val_210_);
        leanh::lean_dec_ref_known(v_x_204_, 1);
        if leanh::lean_obj_tag(v_val_210_) == 0 {
            let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_205_);
            v___x_211_ = leanh::lean_box(0);
            v___x_212_ = leanh::lean_apply_1(v_h__2_206_, v___x_211_);
            return v___x_212_;
        } else {
            let mut v_val_213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_206_);
            v_val_213_ = leanh::lean_ctor_get(v_val_210_, 0);
            leanh::lean_inc(v_val_213_);
            leanh::lean_dec_ref_known(v_val_210_, 1);
            v___x_214_ = leanh::lean_apply_1(v_h__1_205_, v_val_213_);
            return v___x_214_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(
    mut v_n_215_: *mut leanh::LeanObject,
    mut v_motive_216_: *mut leanh::LeanObject,
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_h__1_218_: *mut leanh::LeanObject,
    mut v_h__2_219_: *mut leanh::LeanObject,
    mut v_h__3_220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_219_);
        leanh::lean_dec(v_h__1_218_);
        v___x_221_ = leanh::lean_box(0);
        v___x_222_ = leanh::lean_apply_1(v_h__3_220_, v___x_221_);
        return v___x_222_;
    } else {
        let mut v_val_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_220_);
        v_val_223_ = leanh::lean_ctor_get(v_x_217_, 0);
        leanh::lean_inc(v_val_223_);
        leanh::lean_dec_ref_known(v_x_217_, 1);
        if leanh::lean_obj_tag(v_val_223_) == 0 {
            let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_218_);
            v___x_224_ = leanh::lean_box(0);
            v___x_225_ = leanh::lean_apply_1(v_h__2_219_, v___x_224_);
            return v___x_225_;
        } else {
            let mut v_val_226_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_219_);
            v_val_226_ = leanh::lean_ctor_get(v_val_223_, 0);
            leanh::lean_inc(v_val_226_);
            leanh::lean_dec_ref_known(v_val_223_, 1);
            v___x_227_ = leanh::lean_apply_1(v_h__1_218_, v_val_226_);
            return v___x_227_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(
    mut v_n_228_: *mut leanh::LeanObject,
    mut v_motive_229_: *mut leanh::LeanObject,
    mut v_x_230_: *mut leanh::LeanObject,
    mut v_h__1_231_: *mut leanh::LeanObject,
    mut v_h__2_232_: *mut leanh::LeanObject,
    mut v_h__3_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_228_, v_motive_229_, v_x_230_, v_h__1_231_, v_h__2_232_, v_h__3_233_);
    leanh::lean_dec(v_n_228_);
    return v_res_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(
    mut v_x_235_: *mut leanh::LeanObject,
    mut v_h__1_236_: *mut leanh::LeanObject,
    mut v_h__2_237_: *mut leanh::LeanObject,
    mut v_h__3_238_: *mut leanh::LeanObject,
    mut v_h__4_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_235_) {
        0 => {
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_239_);
            leanh::lean_dec(v_h__3_238_);
            leanh::lean_dec(v_h__2_237_);
            v___x_240_ = leanh::lean_box(0);
            v___x_241_ = leanh::lean_apply_1(v_h__1_236_, v___x_240_);
            return v___x_241_;
        }
        1 => {
            let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_239_);
            leanh::lean_dec(v_h__3_238_);
            leanh::lean_dec(v_h__1_236_);
            v___x_242_ = leanh::lean_box(0);
            v___x_243_ = leanh::lean_apply_1(v_h__2_237_, v___x_242_);
            return v___x_243_;
        }
        2 => {
            let mut v_l_244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_239_);
            leanh::lean_dec(v_h__2_237_);
            leanh::lean_dec(v_h__1_236_);
            v_l_244_ = leanh::lean_ctor_get(v_x_235_, 0);
            leanh::lean_inc_ref(v_l_244_);
            leanh::lean_dec_ref_known(v_x_235_, 1);
            v_fst_245_ = leanh::lean_ctor_get(v_l_244_, 0);
            leanh::lean_inc(v_fst_245_);
            v_snd_246_ = leanh::lean_ctor_get(v_l_244_, 1);
            leanh::lean_inc(v_snd_246_);
            leanh::lean_dec_ref(v_l_244_);
            v___x_247_ = leanh::lean_apply_2(v_h__3_238_, v_fst_245_, v_snd_246_);
            return v___x_247_;
        }
        _ => {
            let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_238_);
            leanh::lean_dec(v_h__2_237_);
            leanh::lean_dec(v_h__1_236_);
            v___x_248_ = leanh::lean_box(0);
            v___x_249_ = leanh::lean_apply_1(v_h__4_239_, v___x_248_);
            return v___x_249_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(
    mut v_n_250_: *mut leanh::LeanObject,
    mut v_motive_251_: *mut leanh::LeanObject,
    mut v_x_252_: *mut leanh::LeanObject,
    mut v_h__1_253_: *mut leanh::LeanObject,
    mut v_h__2_254_: *mut leanh::LeanObject,
    mut v_h__3_255_: *mut leanh::LeanObject,
    mut v_h__4_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_252_) {
        0 => {
            let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_256_);
            leanh::lean_dec(v_h__3_255_);
            leanh::lean_dec(v_h__2_254_);
            v___x_257_ = leanh::lean_box(0);
            v___x_258_ = leanh::lean_apply_1(v_h__1_253_, v___x_257_);
            return v___x_258_;
        }
        1 => {
            let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_256_);
            leanh::lean_dec(v_h__3_255_);
            leanh::lean_dec(v_h__1_253_);
            v___x_259_ = leanh::lean_box(0);
            v___x_260_ = leanh::lean_apply_1(v_h__2_254_, v___x_259_);
            return v___x_260_;
        }
        2 => {
            let mut v_l_261_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_262_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_263_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_256_);
            leanh::lean_dec(v_h__2_254_);
            leanh::lean_dec(v_h__1_253_);
            v_l_261_ = leanh::lean_ctor_get(v_x_252_, 0);
            leanh::lean_inc_ref(v_l_261_);
            leanh::lean_dec_ref_known(v_x_252_, 1);
            v_fst_262_ = leanh::lean_ctor_get(v_l_261_, 0);
            leanh::lean_inc(v_fst_262_);
            v_snd_263_ = leanh::lean_ctor_get(v_l_261_, 1);
            leanh::lean_inc(v_snd_263_);
            leanh::lean_dec_ref(v_l_261_);
            v___x_264_ = leanh::lean_apply_2(v_h__3_255_, v_fst_262_, v_snd_263_);
            return v___x_264_;
        }
        _ => {
            let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_255_);
            leanh::lean_dec(v_h__2_254_);
            leanh::lean_dec(v_h__1_253_);
            v___x_265_ = leanh::lean_box(0);
            v___x_266_ = leanh::lean_apply_1(v_h__4_256_, v___x_265_);
            return v___x_266_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(
    mut v_n_267_: *mut leanh::LeanObject,
    mut v_motive_268_: *mut leanh::LeanObject,
    mut v_x_269_: *mut leanh::LeanObject,
    mut v_h__1_270_: *mut leanh::LeanObject,
    mut v_h__2_271_: *mut leanh::LeanObject,
    mut v_h__3_272_: *mut leanh::LeanObject,
    mut v_h__4_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_267_, v_motive_268_, v_x_269_, v_h__1_270_, v_h__2_271_, v_h__3_272_, v_h__4_273_);
    leanh::lean_dec(v_n_267_);
    return v_res_274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
}