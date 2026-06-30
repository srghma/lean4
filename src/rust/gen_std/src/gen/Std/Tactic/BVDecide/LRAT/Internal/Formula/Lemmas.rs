// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation Std.Tactic.BVDecide.LRAT.Internal.CNF Init.ByCases Init.Data.Array.Bootstrap Init.Data.Int.OfNat Init.Data.List.Pairwise Init.Data.Nat.Linear
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::CNF::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Implementation::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_150_: *mut leanh::LeanObject,
    mut v_h__1_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_152_ = leanh::lean_ctor_get(v_f_150_, 0);
    leanh::lean_inc_ref(v_clauses_152_);
    v_rupUnits_153_ = leanh::lean_ctor_get(v_f_150_, 1);
    leanh::lean_inc_ref(v_rupUnits_153_);
    v_ratUnits_154_ = leanh::lean_ctor_get(v_f_150_, 2);
    leanh::lean_inc_ref(v_ratUnits_154_);
    v_assignments_155_ = leanh::lean_ctor_get(v_f_150_, 3);
    leanh::lean_inc_ref(v_assignments_155_);
    leanh::lean_dec_ref(v_f_150_);
    v___x_156_ = leanh::lean_apply_4(
        v_h__1_151_,
        v_clauses_152_,
        v_rupUnits_153_,
        v_ratUnits_154_,
        v_assignments_155_,
    );
    return v___x_156_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_157_: *mut leanh::LeanObject,
    mut v_motive_158_: *mut leanh::LeanObject,
    mut v_f_159_: *mut leanh::LeanObject,
    mut v_h__1_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_161_ = leanh::lean_ctor_get(v_f_159_, 0);
    leanh::lean_inc_ref(v_clauses_161_);
    v_rupUnits_162_ = leanh::lean_ctor_get(v_f_159_, 1);
    leanh::lean_inc_ref(v_rupUnits_162_);
    v_ratUnits_163_ = leanh::lean_ctor_get(v_f_159_, 2);
    leanh::lean_inc_ref(v_ratUnits_163_);
    v_assignments_164_ = leanh::lean_ctor_get(v_f_159_, 3);
    leanh::lean_inc_ref(v_assignments_164_);
    leanh::lean_dec_ref(v_f_159_);
    v___x_165_ = leanh::lean_apply_4(
        v_h__1_160_,
        v_clauses_161_,
        v_rupUnits_162_,
        v_ratUnits_163_,
        v_assignments_164_,
    );
    return v___x_165_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_166_: *mut leanh::LeanObject,
    mut v_motive_167_: *mut leanh::LeanObject,
    mut v_f_168_: *mut leanh::LeanObject,
    mut v_h__1_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_166_, v_motive_167_, v_f_168_, v_h__1_169_);
    leanh::lean_dec(v_n_166_);
    return v_res_170_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(
    mut v_x_171_: *mut leanh::LeanObject,
    mut v_h__1_172_: *mut leanh::LeanObject,
    mut v_h__2_173_: *mut leanh::LeanObject,
    mut v_h__3_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_174_);
        leanh::lean_dec(v_h__2_173_);
        v___x_175_ = leanh::lean_box(0);
        v___x_176_ = leanh::lean_apply_1(v_h__1_172_, v___x_175_);
        return v___x_176_;
    } else {
        let mut v_val_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_179_: u8 = 0;
        leanh::lean_dec(v_h__1_172_);
        v_val_177_ = leanh::lean_ctor_get(v_x_171_, 0);
        leanh::lean_inc(v_val_177_);
        leanh::lean_dec_ref_known(v_x_171_, 1);
        v_snd_178_ = leanh::lean_ctor_get(v_val_177_, 1);
        v___x_179_ = (leanh::lean_unbox(v_snd_178_) as u8);
        if v___x_179_ == 0 {
            let mut v_fst_180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_173_);
            v_fst_180_ = leanh::lean_ctor_get(v_val_177_, 0);
            leanh::lean_inc(v_fst_180_);
            leanh::lean_dec(v_val_177_);
            v___x_181_ = leanh::lean_apply_1(v_h__3_174_, v_fst_180_);
            return v___x_181_;
        } else {
            let mut v_fst_182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_174_);
            v_fst_182_ = leanh::lean_ctor_get(v_val_177_, 0);
            leanh::lean_inc(v_fst_182_);
            leanh::lean_dec(v_val_177_);
            v___x_183_ = leanh::lean_apply_1(v_h__2_173_, v_fst_182_);
            return v___x_183_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(
    mut v_n_184_: *mut leanh::LeanObject,
    mut v_motive_185_: *mut leanh::LeanObject,
    mut v_x_186_: *mut leanh::LeanObject,
    mut v_h__1_187_: *mut leanh::LeanObject,
    mut v_h__2_188_: *mut leanh::LeanObject,
    mut v_h__3_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_186_) == 0 {
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_189_);
        leanh::lean_dec(v_h__2_188_);
        v___x_190_ = leanh::lean_box(0);
        v___x_191_ = leanh::lean_apply_1(v_h__1_187_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: u8 = 0;
        leanh::lean_dec(v_h__1_187_);
        v_val_192_ = leanh::lean_ctor_get(v_x_186_, 0);
        leanh::lean_inc(v_val_192_);
        leanh::lean_dec_ref_known(v_x_186_, 1);
        v_snd_193_ = leanh::lean_ctor_get(v_val_192_, 1);
        v___x_194_ = (leanh::lean_unbox(v_snd_193_) as u8);
        if v___x_194_ == 0 {
            let mut v_fst_195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_188_);
            v_fst_195_ = leanh::lean_ctor_get(v_val_192_, 0);
            leanh::lean_inc(v_fst_195_);
            leanh::lean_dec(v_val_192_);
            v___x_196_ = leanh::lean_apply_1(v_h__3_189_, v_fst_195_);
            return v___x_196_;
        } else {
            let mut v_fst_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_189_);
            v_fst_197_ = leanh::lean_ctor_get(v_val_192_, 0);
            leanh::lean_inc(v_fst_197_);
            leanh::lean_dec(v_val_192_);
            v___x_198_ = leanh::lean_apply_1(v_h__2_188_, v_fst_197_);
            return v___x_198_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___boxed(
    mut v_n_199_: *mut leanh::LeanObject,
    mut v_motive_200_: *mut leanh::LeanObject,
    mut v_x_201_: *mut leanh::LeanObject,
    mut v_h__1_202_: *mut leanh::LeanObject,
    mut v_h__2_203_: *mut leanh::LeanObject,
    mut v_h__3_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_205_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(v_n_199_, v_motive_200_, v_x_201_, v_h__1_202_, v_h__2_203_, v_h__3_204_);
    leanh::lean_dec(v_n_199_);
    return v_res_205_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(
    mut v_cOpt_206_: *mut leanh::LeanObject,
    mut v_h__1_207_: *mut leanh::LeanObject,
    mut v_h__2_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_cOpt_206_) == 0 {
        let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_208_);
        v___x_209_ = leanh::lean_box(0);
        v___x_210_ = leanh::lean_apply_1(v_h__1_207_, v___x_209_);
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_207_);
        v_val_211_ = leanh::lean_ctor_get(v_cOpt_206_, 0);
        leanh::lean_inc(v_val_211_);
        leanh::lean_dec_ref_known(v_cOpt_206_, 1);
        v___x_212_ = leanh::lean_apply_1(v_h__2_208_, v_val_211_);
        return v___x_212_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(
    mut v_n_213_: *mut leanh::LeanObject,
    mut v_motive_214_: *mut leanh::LeanObject,
    mut v_cOpt_215_: *mut leanh::LeanObject,
    mut v_h__1_216_: *mut leanh::LeanObject,
    mut v_h__2_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_cOpt_215_) == 0 {
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_217_);
        v___x_218_ = leanh::lean_box(0);
        v___x_219_ = leanh::lean_apply_1(v_h__1_216_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v_val_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_216_);
        v_val_220_ = leanh::lean_ctor_get(v_cOpt_215_, 0);
        leanh::lean_inc(v_val_220_);
        leanh::lean_dec_ref_known(v_cOpt_215_, 1);
        v___x_221_ = leanh::lean_apply_1(v_h__2_217_, v_val_220_);
        return v___x_221_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(
    mut v_n_222_: *mut leanh::LeanObject,
    mut v_motive_223_: *mut leanh::LeanObject,
    mut v_cOpt_224_: *mut leanh::LeanObject,
    mut v_h__1_225_: *mut leanh::LeanObject,
    mut v_h__2_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_227_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_222_, v_motive_223_, v_cOpt_224_, v_h__1_225_, v_h__2_226_);
    leanh::lean_dec(v_n_222_);
    return v_res_227_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(
    mut v_x_228_: *mut leanh::LeanObject,
    mut v_h__1_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_230_ = leanh::lean_ctor_get(v_x_228_, 1);
    leanh::lean_inc(v_snd_230_);
    v_fst_231_ = leanh::lean_ctor_get(v_x_228_, 0);
    leanh::lean_inc(v_fst_231_);
    leanh::lean_dec_ref(v_x_228_);
    v_fst_232_ = leanh::lean_ctor_get(v_snd_230_, 0);
    leanh::lean_inc(v_fst_232_);
    v_snd_233_ = leanh::lean_ctor_get(v_snd_230_, 1);
    leanh::lean_inc(v_snd_233_);
    leanh::lean_dec(v_snd_230_);
    v___x_234_ = leanh::lean_apply_3(v_h__1_229_, v_fst_231_, v_fst_232_, v_snd_233_);
    return v___x_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(
    mut v_n_235_: *mut leanh::LeanObject,
    mut v_motive_236_: *mut leanh::LeanObject,
    mut v_x_237_: *mut leanh::LeanObject,
    mut v_h__1_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_239_ = leanh::lean_ctor_get(v_x_237_, 1);
    leanh::lean_inc(v_snd_239_);
    v_fst_240_ = leanh::lean_ctor_get(v_x_237_, 0);
    leanh::lean_inc(v_fst_240_);
    leanh::lean_dec_ref(v_x_237_);
    v_fst_241_ = leanh::lean_ctor_get(v_snd_239_, 0);
    leanh::lean_inc(v_fst_241_);
    v_snd_242_ = leanh::lean_ctor_get(v_snd_239_, 1);
    leanh::lean_inc(v_snd_242_);
    leanh::lean_dec(v_snd_239_);
    v___x_243_ = leanh::lean_apply_3(v_h__1_238_, v_fst_240_, v_fst_241_, v_snd_242_);
    return v___x_243_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(
    mut v_n_244_: *mut leanh::LeanObject,
    mut v_motive_245_: *mut leanh::LeanObject,
    mut v_x_246_: *mut leanh::LeanObject,
    mut v_h__1_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_248_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(v_n_244_, v_motive_245_, v_x_246_, v_h__1_247_);
    leanh::lean_dec(v_n_244_);
    return v_res_248_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(
    mut v_x_249_: *mut leanh::LeanObject,
    mut v_h__1_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_251_ = leanh::lean_ctor_get(v_x_249_, 0);
    leanh::lean_inc(v_fst_251_);
    v_snd_252_ = leanh::lean_ctor_get(v_x_249_, 1);
    leanh::lean_inc(v_snd_252_);
    leanh::lean_dec_ref(v_x_249_);
    v___x_253_ = leanh::lean_apply_2(v_h__1_250_, v_fst_251_, v_snd_252_);
    return v___x_253_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(
    mut v_n_254_: *mut leanh::LeanObject,
    mut v_motive_255_: *mut leanh::LeanObject,
    mut v_x_256_: *mut leanh::LeanObject,
    mut v_h__1_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_258_ = leanh::lean_ctor_get(v_x_256_, 0);
    leanh::lean_inc(v_fst_258_);
    v_snd_259_ = leanh::lean_ctor_get(v_x_256_, 1);
    leanh::lean_inc(v_snd_259_);
    leanh::lean_dec_ref(v_x_256_);
    v___x_260_ = leanh::lean_apply_2(v_h__1_257_, v_fst_258_, v_snd_259_);
    return v___x_260_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(
    mut v_n_261_: *mut leanh::LeanObject,
    mut v_motive_262_: *mut leanh::LeanObject,
    mut v_x_263_: *mut leanh::LeanObject,
    mut v_h__1_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(v_n_261_, v_motive_262_, v_x_263_, v_h__1_264_);
    leanh::lean_dec(v_n_261_);
    return v_res_265_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___redArg(
    mut v_x_266_: *mut leanh::LeanObject,
    mut v_h__1_267_: *mut leanh::LeanObject,
    mut v_h__2_268_: *mut leanh::LeanObject,
    mut v_h__3_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_269_);
        leanh::lean_dec(v_h__2_268_);
        v___x_270_ = leanh::lean_box(0);
        v___x_271_ = leanh::lean_apply_1(v_h__1_267_, v___x_270_);
        return v___x_271_;
    } else {
        let mut v_val_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_267_);
        v_val_272_ = leanh::lean_ctor_get(v_x_266_, 0);
        leanh::lean_inc(v_val_272_);
        leanh::lean_dec_ref_known(v_x_266_, 1);
        if leanh::lean_obj_tag(v_val_272_) == 1 {
            let mut v_tail_273_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_tail_273_ = leanh::lean_ctor_get(v_val_272_, 1);
            if leanh::lean_obj_tag(v_tail_273_) == 0 {
                let mut v_head_274_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_269_);
                v_head_274_ = leanh::lean_ctor_get(v_val_272_, 0);
                leanh::lean_inc(v_head_274_);
                leanh::lean_dec_ref_known(v_val_272_, 2);
                v___x_275_ = leanh::lean_apply_3(
                    v_h__2_268_,
                    v_head_274_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_275_;
            } else {
                let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_268_);
                v___x_276_ =
                    leanh::lean_apply_2(v_h__3_269_, v_val_272_, leanh::lean_box(0));
                return v___x_276_;
            }
        } else {
            let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_268_);
            v___x_277_ =
                leanh::lean_apply_2(v_h__3_269_, v_val_272_, leanh::lean_box(0));
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(
    mut v_n_278_: *mut leanh::LeanObject,
    mut v_motive_279_: *mut leanh::LeanObject,
    mut v_x_280_: *mut leanh::LeanObject,
    mut v_h__1_281_: *mut leanh::LeanObject,
    mut v_h__2_282_: *mut leanh::LeanObject,
    mut v_h__3_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_280_) == 0 {
        let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_283_);
        leanh::lean_dec(v_h__2_282_);
        v___x_284_ = leanh::lean_box(0);
        v___x_285_ = leanh::lean_apply_1(v_h__1_281_, v___x_284_);
        return v___x_285_;
    } else {
        let mut v_val_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_281_);
        v_val_286_ = leanh::lean_ctor_get(v_x_280_, 0);
        leanh::lean_inc(v_val_286_);
        leanh::lean_dec_ref_known(v_x_280_, 1);
        if leanh::lean_obj_tag(v_val_286_) == 1 {
            let mut v_tail_287_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_tail_287_ = leanh::lean_ctor_get(v_val_286_, 1);
            if leanh::lean_obj_tag(v_tail_287_) == 0 {
                let mut v_head_288_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_283_);
                v_head_288_ = leanh::lean_ctor_get(v_val_286_, 0);
                leanh::lean_inc(v_head_288_);
                leanh::lean_dec_ref_known(v_val_286_, 2);
                v___x_289_ = leanh::lean_apply_3(
                    v_h__2_282_,
                    v_head_288_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_289_;
            } else {
                let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_282_);
                v___x_290_ =
                    leanh::lean_apply_2(v_h__3_283_, v_val_286_, leanh::lean_box(0));
                return v___x_290_;
            }
        } else {
            let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_282_);
            v___x_291_ =
                leanh::lean_apply_2(v_h__3_283_, v_val_286_, leanh::lean_box(0));
            return v___x_291_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___boxed(
    mut v_n_292_: *mut leanh::LeanObject,
    mut v_motive_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
    mut v_h__2_296_: *mut leanh::LeanObject,
    mut v_h__3_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(v_n_292_, v_motive_293_, v_x_294_, v_h__1_295_, v_h__2_296_, v_h__3_297_);
    leanh::lean_dec(v_n_292_);
    return v_res_298_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
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
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
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
    res = initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
}