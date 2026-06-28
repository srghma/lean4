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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___redArg(
    mut v_x_138_: *mut LeanObject,
    mut v_x_139_: *mut LeanObject,
    mut v_h__1_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    v_fst_141_ = lean_ctor_get(v_x_139_, 0);
    lean_inc(v_fst_141_);
    v_snd_142_ = lean_ctor_get(v_x_139_, 1);
    lean_inc(v_snd_142_);
    lean_dec_ref(v_x_139_);
    v___x_143_ = lean_apply_3(v_h__1_140_, v_x_138_, v_fst_141_, v_snd_142_);
    return v___x_143_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(
    mut v_n_144_: *mut LeanObject,
    mut v_motive_145_: *mut LeanObject,
    mut v_x_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_h__1_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    v_fst_149_ = lean_ctor_get(v_x_147_, 0);
    lean_inc(v_fst_149_);
    v_snd_150_ = lean_ctor_get(v_x_147_, 1);
    lean_inc(v_snd_150_);
    lean_dec_ref(v_x_147_);
    v___x_151_ = lean_apply_3(v_h__1_148_, v_x_146_, v_fst_149_, v_snd_150_);
    return v___x_151_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter___boxed(
    mut v_n_152_: *mut LeanObject,
    mut v_motive_153_: *mut LeanObject,
    mut v_x_154_: *mut LeanObject,
    mut v_x_155_: *mut LeanObject,
    mut v_h__1_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_157_: *mut LeanObject = core::ptr::null_mut();
    v_res_157_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit_match__1_splitter(v_n_152_, v_motive_153_, v_x_154_, v_x_155_, v_h__1_156_);
    lean_dec(v_n_152_);
    return v_res_157_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_158_: *mut LeanObject,
    mut v_h__1_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_160_ = lean_ctor_get(v_f_158_, 0);
    lean_inc_ref(v_clauses_160_);
    v_rupUnits_161_ = lean_ctor_get(v_f_158_, 1);
    lean_inc_ref(v_rupUnits_161_);
    v_ratUnits_162_ = lean_ctor_get(v_f_158_, 2);
    lean_inc_ref(v_ratUnits_162_);
    v_assignments_163_ = lean_ctor_get(v_f_158_, 3);
    lean_inc_ref(v_assignments_163_);
    lean_dec_ref(v_f_158_);
    v___x_164_ = lean_apply_4(
        v_h__1_159_,
        v_clauses_160_,
        v_rupUnits_161_,
        v_ratUnits_162_,
        v_assignments_163_,
    );
    return v___x_164_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_165_: *mut LeanObject,
    mut v_motive_166_: *mut LeanObject,
    mut v_f_167_: *mut LeanObject,
    mut v_h__1_168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_169_ = lean_ctor_get(v_f_167_, 0);
    lean_inc_ref(v_clauses_169_);
    v_rupUnits_170_ = lean_ctor_get(v_f_167_, 1);
    lean_inc_ref(v_rupUnits_170_);
    v_ratUnits_171_ = lean_ctor_get(v_f_167_, 2);
    lean_inc_ref(v_ratUnits_171_);
    v_assignments_172_ = lean_ctor_get(v_f_167_, 3);
    lean_inc_ref(v_assignments_172_);
    lean_dec_ref(v_f_167_);
    v___x_173_ = lean_apply_4(
        v_h__1_168_,
        v_clauses_169_,
        v_rupUnits_170_,
        v_ratUnits_171_,
        v_assignments_172_,
    );
    return v___x_173_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_174_: *mut LeanObject,
    mut v_motive_175_: *mut LeanObject,
    mut v_f_176_: *mut LeanObject,
    mut v_h__1_177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_178_: *mut LeanObject = core::ptr::null_mut();
    v_res_178_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_174_, v_motive_175_, v_f_176_, v_h__1_177_);
    lean_dec(v_n_174_);
    return v_res_178_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___redArg(
    mut v_x_179_: *mut LeanObject,
    mut v_h__1_180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    v_snd_181_ = lean_ctor_get(v_x_179_, 1);
    lean_inc(v_snd_181_);
    v_snd_182_ = lean_ctor_get(v_snd_181_, 1);
    lean_inc(v_snd_182_);
    v_fst_183_ = lean_ctor_get(v_x_179_, 0);
    lean_inc(v_fst_183_);
    lean_dec_ref(v_x_179_);
    v_fst_184_ = lean_ctor_get(v_snd_181_, 0);
    lean_inc(v_fst_184_);
    lean_dec(v_snd_181_);
    v_fst_185_ = lean_ctor_get(v_snd_182_, 0);
    lean_inc(v_fst_185_);
    v_snd_186_ = lean_ctor_get(v_snd_182_, 1);
    lean_inc(v_snd_186_);
    lean_dec(v_snd_182_);
    v___x_187_ = lean_apply_4(v_h__1_180_, v_fst_183_, v_fst_184_, v_fst_185_, v_snd_186_);
    return v___x_187_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(
    mut v_n_188_: *mut LeanObject,
    mut v_motive_189_: *mut LeanObject,
    mut v_x_190_: *mut LeanObject,
    mut v_h__1_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    v_snd_192_ = lean_ctor_get(v_x_190_, 1);
    lean_inc(v_snd_192_);
    v_snd_193_ = lean_ctor_get(v_snd_192_, 1);
    lean_inc(v_snd_193_);
    v_fst_194_ = lean_ctor_get(v_x_190_, 0);
    lean_inc(v_fst_194_);
    lean_dec_ref(v_x_190_);
    v_fst_195_ = lean_ctor_get(v_snd_192_, 0);
    lean_inc(v_fst_195_);
    lean_dec(v_snd_192_);
    v_fst_196_ = lean_ctor_get(v_snd_193_, 0);
    lean_inc(v_fst_196_);
    v_snd_197_ = lean_ctor_get(v_snd_193_, 1);
    lean_inc(v_snd_197_);
    lean_dec(v_snd_193_);
    v___x_198_ = lean_apply_4(v_h__1_191_, v_fst_194_, v_fst_195_, v_fst_196_, v_snd_197_);
    return v___x_198_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter___boxed(
    mut v_n_199_: *mut LeanObject,
    mut v_motive_200_: *mut LeanObject,
    mut v_x_201_: *mut LeanObject,
    mut v_h__1_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_203_: *mut LeanObject = core::ptr::null_mut();
    v_res_203_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__5_splitter(v_n_199_, v_motive_200_, v_x_201_, v_h__1_202_);
    lean_dec(v_n_199_);
    return v_res_203_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(
    mut v_x_204_: *mut LeanObject,
    mut v_h__1_205_: *mut LeanObject,
    mut v_h__2_206_: *mut LeanObject,
    mut v_h__3_207_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_204_) == 0 {
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_206_);
        lean_dec(v_h__1_205_);
        v___x_208_ = lean_box(0);
        v___x_209_ = lean_apply_1(v_h__3_207_, v___x_208_);
        return v___x_209_;
    } else {
        let mut v_val_210_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_207_);
        v_val_210_ = lean_ctor_get(v_x_204_, 0);
        lean_inc(v_val_210_);
        lean_dec_ref_known(v_x_204_, 1);
        if lean_obj_tag(v_val_210_) == 0 {
            let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_205_);
            v___x_211_ = lean_box(0);
            v___x_212_ = lean_apply_1(v_h__2_206_, v___x_211_);
            return v___x_212_;
        } else {
            let mut v_val_213_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_206_);
            v_val_213_ = lean_ctor_get(v_val_210_, 0);
            lean_inc(v_val_213_);
            lean_dec_ref_known(v_val_210_, 1);
            v___x_214_ = lean_apply_1(v_h__1_205_, v_val_213_);
            return v___x_214_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(
    mut v_n_215_: *mut LeanObject,
    mut v_motive_216_: *mut LeanObject,
    mut v_x_217_: *mut LeanObject,
    mut v_h__1_218_: *mut LeanObject,
    mut v_h__2_219_: *mut LeanObject,
    mut v_h__3_220_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_217_) == 0 {
        let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_219_);
        lean_dec(v_h__1_218_);
        v___x_221_ = lean_box(0);
        v___x_222_ = lean_apply_1(v_h__3_220_, v___x_221_);
        return v___x_222_;
    } else {
        let mut v_val_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_220_);
        v_val_223_ = lean_ctor_get(v_x_217_, 0);
        lean_inc(v_val_223_);
        lean_dec_ref_known(v_x_217_, 1);
        if lean_obj_tag(v_val_223_) == 0 {
            let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_218_);
            v___x_224_ = lean_box(0);
            v___x_225_ = lean_apply_1(v_h__2_219_, v___x_224_);
            return v___x_225_;
        } else {
            let mut v_val_226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_219_);
            v_val_226_ = lean_ctor_get(v_val_223_, 0);
            lean_inc(v_val_226_);
            lean_dec_ref_known(v_val_223_, 1);
            v___x_227_ = lean_apply_1(v_h__1_218_, v_val_226_);
            return v___x_227_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(
    mut v_n_228_: *mut LeanObject,
    mut v_motive_229_: *mut LeanObject,
    mut v_x_230_: *mut LeanObject,
    mut v_h__1_231_: *mut LeanObject,
    mut v_h__2_232_: *mut LeanObject,
    mut v_h__3_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_234_: *mut LeanObject = core::ptr::null_mut();
    v_res_234_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_228_, v_motive_229_, v_x_230_, v_h__1_231_, v_h__2_232_, v_h__3_233_);
    lean_dec(v_n_228_);
    return v_res_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(
    mut v_x_235_: *mut LeanObject,
    mut v_h__1_236_: *mut LeanObject,
    mut v_h__2_237_: *mut LeanObject,
    mut v_h__3_238_: *mut LeanObject,
    mut v_h__4_239_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_235_) {
        0 => {
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_239_);
            lean_dec(v_h__3_238_);
            lean_dec(v_h__2_237_);
            v___x_240_ = lean_box(0);
            v___x_241_ = lean_apply_1(v_h__1_236_, v___x_240_);
            return v___x_241_;
        }
        1 => {
            let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_239_);
            lean_dec(v_h__3_238_);
            lean_dec(v_h__1_236_);
            v___x_242_ = lean_box(0);
            v___x_243_ = lean_apply_1(v_h__2_237_, v___x_242_);
            return v___x_243_;
        }
        2 => {
            let mut v_l_244_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_245_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_246_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_239_);
            lean_dec(v_h__2_237_);
            lean_dec(v_h__1_236_);
            v_l_244_ = lean_ctor_get(v_x_235_, 0);
            lean_inc_ref(v_l_244_);
            lean_dec_ref_known(v_x_235_, 1);
            v_fst_245_ = lean_ctor_get(v_l_244_, 0);
            lean_inc(v_fst_245_);
            v_snd_246_ = lean_ctor_get(v_l_244_, 1);
            lean_inc(v_snd_246_);
            lean_dec_ref(v_l_244_);
            v___x_247_ = lean_apply_2(v_h__3_238_, v_fst_245_, v_snd_246_);
            return v___x_247_;
        }
        _ => {
            let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_238_);
            lean_dec(v_h__2_237_);
            lean_dec(v_h__1_236_);
            v___x_248_ = lean_box(0);
            v___x_249_ = lean_apply_1(v_h__4_239_, v___x_248_);
            return v___x_249_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(
    mut v_n_250_: *mut LeanObject,
    mut v_motive_251_: *mut LeanObject,
    mut v_x_252_: *mut LeanObject,
    mut v_h__1_253_: *mut LeanObject,
    mut v_h__2_254_: *mut LeanObject,
    mut v_h__3_255_: *mut LeanObject,
    mut v_h__4_256_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_252_) {
        0 => {
            let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_256_);
            lean_dec(v_h__3_255_);
            lean_dec(v_h__2_254_);
            v___x_257_ = lean_box(0);
            v___x_258_ = lean_apply_1(v_h__1_253_, v___x_257_);
            return v___x_258_;
        }
        1 => {
            let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_256_);
            lean_dec(v_h__3_255_);
            lean_dec(v_h__1_253_);
            v___x_259_ = lean_box(0);
            v___x_260_ = lean_apply_1(v_h__2_254_, v___x_259_);
            return v___x_260_;
        }
        2 => {
            let mut v_l_261_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_262_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_263_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_256_);
            lean_dec(v_h__2_254_);
            lean_dec(v_h__1_253_);
            v_l_261_ = lean_ctor_get(v_x_252_, 0);
            lean_inc_ref(v_l_261_);
            lean_dec_ref_known(v_x_252_, 1);
            v_fst_262_ = lean_ctor_get(v_l_261_, 0);
            lean_inc(v_fst_262_);
            v_snd_263_ = lean_ctor_get(v_l_261_, 1);
            lean_inc(v_snd_263_);
            lean_dec_ref(v_l_261_);
            v___x_264_ = lean_apply_2(v_h__3_255_, v_fst_262_, v_snd_263_);
            return v___x_264_;
        }
        _ => {
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_255_);
            lean_dec(v_h__2_254_);
            lean_dec(v_h__1_253_);
            v___x_265_ = lean_box(0);
            v___x_266_ = lean_apply_1(v_h__4_256_, v___x_265_);
            return v___x_266_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(
    mut v_n_267_: *mut LeanObject,
    mut v_motive_268_: *mut LeanObject,
    mut v_x_269_: *mut LeanObject,
    mut v_h__1_270_: *mut LeanObject,
    mut v_h__2_271_: *mut LeanObject,
    mut v_h__3_272_: *mut LeanObject,
    mut v_h__4_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_274_: *mut LeanObject = core::ptr::null_mut();
    v_res_274_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_267_, v_motive_268_, v_x_269_, v_h__1_270_, v_h__2_271_, v_h__3_272_, v_h__4_273_);
    lean_dec(v_n_267_);
    return v_res_274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
}
