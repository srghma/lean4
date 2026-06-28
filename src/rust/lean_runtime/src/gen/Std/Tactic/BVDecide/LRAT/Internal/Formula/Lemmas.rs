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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___redArg(
    mut v_f_150_: *mut LeanObject,
    mut v_h__1_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_152_ = lean_ctor_get(v_f_150_, 0);
    lean_inc_ref(v_clauses_152_);
    v_rupUnits_153_ = lean_ctor_get(v_f_150_, 1);
    lean_inc_ref(v_rupUnits_153_);
    v_ratUnits_154_ = lean_ctor_get(v_f_150_, 2);
    lean_inc_ref(v_ratUnits_154_);
    v_assignments_155_ = lean_ctor_get(v_f_150_, 3);
    lean_inc_ref(v_assignments_155_);
    lean_dec_ref(v_f_150_);
    v___x_156_ = lean_apply_4(
        v_h__1_151_,
        v_clauses_152_,
        v_rupUnits_153_,
        v_ratUnits_154_,
        v_assignments_155_,
    );
    return v___x_156_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(
    mut v_n_157_: *mut LeanObject,
    mut v_motive_158_: *mut LeanObject,
    mut v_f_159_: *mut LeanObject,
    mut v_h__1_160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_clauses_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignments_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    v_clauses_161_ = lean_ctor_get(v_f_159_, 0);
    lean_inc_ref(v_clauses_161_);
    v_rupUnits_162_ = lean_ctor_get(v_f_159_, 1);
    lean_inc_ref(v_rupUnits_162_);
    v_ratUnits_163_ = lean_ctor_get(v_f_159_, 2);
    lean_inc_ref(v_ratUnits_163_);
    v_assignments_164_ = lean_ctor_get(v_f_159_, 3);
    lean_inc_ref(v_assignments_164_);
    lean_dec_ref(v_f_159_);
    v___x_165_ = lean_apply_4(
        v_h__1_160_,
        v_clauses_161_,
        v_rupUnits_162_,
        v_ratUnits_163_,
        v_assignments_164_,
    );
    return v___x_165_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter___boxed(
    mut v_n_166_: *mut LeanObject,
    mut v_motive_167_: *mut LeanObject,
    mut v_f_168_: *mut LeanObject,
    mut v_h__1_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_170_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert_match__1_splitter(v_n_166_, v_motive_167_, v_f_168_, v_h__1_169_);
    lean_dec(v_n_166_);
    return v_res_170_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___redArg(
    mut v_x_171_: *mut LeanObject,
    mut v_h__1_172_: *mut LeanObject,
    mut v_h__2_173_: *mut LeanObject,
    mut v_h__3_174_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_174_);
        lean_dec(v_h__2_173_);
        v___x_175_ = lean_box(0);
        v___x_176_ = lean_apply_1(v_h__1_172_, v___x_175_);
        return v___x_176_;
    } else {
        let mut v_val_177_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_179_: u8 = 0;
        lean_dec(v_h__1_172_);
        v_val_177_ = lean_ctor_get(v_x_171_, 0);
        lean_inc(v_val_177_);
        lean_dec_ref_known(v_x_171_, 1);
        v_snd_178_ = lean_ctor_get(v_val_177_, 1);
        v___x_179_ = (lean_unbox(v_snd_178_) as u8);
        if v___x_179_ == 0 {
            let mut v_fst_180_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_173_);
            v_fst_180_ = lean_ctor_get(v_val_177_, 0);
            lean_inc(v_fst_180_);
            lean_dec(v_val_177_);
            v___x_181_ = lean_apply_1(v_h__3_174_, v_fst_180_);
            return v___x_181_;
        } else {
            let mut v_fst_182_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_174_);
            v_fst_182_ = lean_ctor_get(v_val_177_, 0);
            lean_inc(v_fst_182_);
            lean_dec(v_val_177_);
            v___x_183_ = lean_apply_1(v_h__2_173_, v_fst_182_);
            return v___x_183_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(
    mut v_n_184_: *mut LeanObject,
    mut v_motive_185_: *mut LeanObject,
    mut v_x_186_: *mut LeanObject,
    mut v_h__1_187_: *mut LeanObject,
    mut v_h__2_188_: *mut LeanObject,
    mut v_h__3_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_186_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_189_);
        lean_dec(v_h__2_188_);
        v___x_190_ = lean_box(0);
        v___x_191_ = lean_apply_1(v_h__1_187_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_194_: u8 = 0;
        lean_dec(v_h__1_187_);
        v_val_192_ = lean_ctor_get(v_x_186_, 0);
        lean_inc(v_val_192_);
        lean_dec_ref_known(v_x_186_, 1);
        v_snd_193_ = lean_ctor_get(v_val_192_, 1);
        v___x_194_ = (lean_unbox(v_snd_193_) as u8);
        if v___x_194_ == 0 {
            let mut v_fst_195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_188_);
            v_fst_195_ = lean_ctor_get(v_val_192_, 0);
            lean_inc(v_fst_195_);
            lean_dec(v_val_192_);
            v___x_196_ = lean_apply_1(v_h__3_189_, v_fst_195_);
            return v___x_196_;
        } else {
            let mut v_fst_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_189_);
            v_fst_197_ = lean_ctor_get(v_val_192_, 0);
            lean_inc(v_fst_197_);
            lean_dec(v_val_192_);
            v___x_198_ = lean_apply_1(v_h__2_188_, v_fst_197_);
            return v___x_198_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter___boxed(
    mut v_n_199_: *mut LeanObject,
    mut v_motive_200_: *mut LeanObject,
    mut v_x_201_: *mut LeanObject,
    mut v_h__1_202_: *mut LeanObject,
    mut v_h__2_203_: *mut LeanObject,
    mut v_h__3_204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_205_: *mut LeanObject = core::ptr::null_mut();
    v_res_205_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__1_splitter(v_n_199_, v_motive_200_, v_x_201_, v_h__1_202_, v_h__2_203_, v_h__3_204_);
    lean_dec(v_n_199_);
    return v_res_205_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___redArg(
    mut v_cOpt_206_: *mut LeanObject,
    mut v_h__1_207_: *mut LeanObject,
    mut v_h__2_208_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_cOpt_206_) == 0 {
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_208_);
        v___x_209_ = lean_box(0);
        v___x_210_ = lean_apply_1(v_h__1_207_, v___x_209_);
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_207_);
        v_val_211_ = lean_ctor_get(v_cOpt_206_, 0);
        lean_inc(v_val_211_);
        lean_dec_ref_known(v_cOpt_206_, 1);
        v___x_212_ = lean_apply_1(v_h__2_208_, v_val_211_);
        return v___x_212_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(
    mut v_n_213_: *mut LeanObject,
    mut v_motive_214_: *mut LeanObject,
    mut v_cOpt_215_: *mut LeanObject,
    mut v_h__1_216_: *mut LeanObject,
    mut v_h__2_217_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_cOpt_215_) == 0 {
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_217_);
        v___x_218_ = lean_box(0);
        v___x_219_ = lean_apply_1(v_h__1_216_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v_val_220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_216_);
        v_val_220_ = lean_ctor_get(v_cOpt_215_, 0);
        lean_inc(v_val_220_);
        lean_dec_ref_known(v_cOpt_215_, 1);
        v___x_221_ = lean_apply_1(v_h__2_217_, v_val_220_);
        return v___x_221_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter___boxed(
    mut v_n_222_: *mut LeanObject,
    mut v_motive_223_: *mut LeanObject,
    mut v_cOpt_224_: *mut LeanObject,
    mut v_h__1_225_: *mut LeanObject,
    mut v_h__2_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_227_: *mut LeanObject = core::ptr::null_mut();
    v_res_227_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn_match__3_splitter(v_n_222_, v_motive_223_, v_cOpt_224_, v_h__1_225_, v_h__2_226_);
    lean_dec(v_n_222_);
    return v_res_227_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___redArg(
    mut v_x_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    v_snd_230_ = lean_ctor_get(v_x_228_, 1);
    lean_inc(v_snd_230_);
    v_fst_231_ = lean_ctor_get(v_x_228_, 0);
    lean_inc(v_fst_231_);
    lean_dec_ref(v_x_228_);
    v_fst_232_ = lean_ctor_get(v_snd_230_, 0);
    lean_inc(v_fst_232_);
    v_snd_233_ = lean_ctor_get(v_snd_230_, 1);
    lean_inc(v_snd_233_);
    lean_dec(v_snd_230_);
    v___x_234_ = lean_apply_3(v_h__1_229_, v_fst_231_, v_fst_232_, v_snd_233_);
    return v___x_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(
    mut v_n_235_: *mut LeanObject,
    mut v_motive_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
    mut v_h__1_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    v_snd_239_ = lean_ctor_get(v_x_237_, 1);
    lean_inc(v_snd_239_);
    v_fst_240_ = lean_ctor_get(v_x_237_, 0);
    lean_inc(v_fst_240_);
    lean_dec_ref(v_x_237_);
    v_fst_241_ = lean_ctor_get(v_snd_239_, 0);
    lean_inc(v_fst_241_);
    v_snd_242_ = lean_ctor_get(v_snd_239_, 1);
    lean_inc(v_snd_242_);
    lean_dec(v_snd_239_);
    v___x_243_ = lean_apply_3(v_h__1_238_, v_fst_240_, v_fst_241_, v_snd_242_);
    return v___x_243_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter___boxed(
    mut v_n_244_: *mut LeanObject,
    mut v_motive_245_: *mut LeanObject,
    mut v_x_246_: *mut LeanObject,
    mut v_h__1_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_248_: *mut LeanObject = core::ptr::null_mut();
    v_res_248_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__3_splitter(v_n_244_, v_motive_245_, v_x_246_, v_h__1_247_);
    lean_dec(v_n_244_);
    return v_res_248_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___redArg(
    mut v_x_249_: *mut LeanObject,
    mut v_h__1_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v_fst_251_ = lean_ctor_get(v_x_249_, 0);
    lean_inc(v_fst_251_);
    v_snd_252_ = lean_ctor_get(v_x_249_, 1);
    lean_inc(v_snd_252_);
    lean_dec_ref(v_x_249_);
    v___x_253_ = lean_apply_2(v_h__1_250_, v_fst_251_, v_snd_252_);
    return v___x_253_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(
    mut v_n_254_: *mut LeanObject,
    mut v_motive_255_: *mut LeanObject,
    mut v_x_256_: *mut LeanObject,
    mut v_h__1_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v_fst_258_ = lean_ctor_get(v_x_256_, 0);
    lean_inc(v_fst_258_);
    v_snd_259_ = lean_ctor_get(v_x_256_, 1);
    lean_inc(v_snd_259_);
    lean_dec_ref(v_x_256_);
    v___x_260_ = lean_apply_2(v_h__1_257_, v_fst_258_, v_snd_259_);
    return v___x_260_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter___boxed(
    mut v_n_261_: *mut LeanObject,
    mut v_motive_262_: *mut LeanObject,
    mut v_x_263_: *mut LeanObject,
    mut v_h__1_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_265_: *mut LeanObject = core::ptr::null_mut();
    v_res_265_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit_match__1_splitter(v_n_261_, v_motive_262_, v_x_263_, v_h__1_264_);
    lean_dec(v_n_261_);
    return v_res_265_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___redArg(
    mut v_x_266_: *mut LeanObject,
    mut v_h__1_267_: *mut LeanObject,
    mut v_h__2_268_: *mut LeanObject,
    mut v_h__3_269_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_269_);
        lean_dec(v_h__2_268_);
        v___x_270_ = lean_box(0);
        v___x_271_ = lean_apply_1(v_h__1_267_, v___x_270_);
        return v___x_271_;
    } else {
        let mut v_val_272_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_267_);
        v_val_272_ = lean_ctor_get(v_x_266_, 0);
        lean_inc(v_val_272_);
        lean_dec_ref_known(v_x_266_, 1);
        if lean_obj_tag(v_val_272_) == 1 {
            let mut v_tail_273_: *mut LeanObject = core::ptr::null_mut();
            v_tail_273_ = lean_ctor_get(v_val_272_, 1);
            if lean_obj_tag(v_tail_273_) == 0 {
                let mut v_head_274_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_269_);
                v_head_274_ = lean_ctor_get(v_val_272_, 0);
                lean_inc(v_head_274_);
                lean_dec_ref_known(v_val_272_, 2);
                v___x_275_ = lean_apply_3(v_h__2_268_, v_head_274_, lean_box(0), lean_box(0));
                return v___x_275_;
            } else {
                let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_268_);
                v___x_276_ = lean_apply_2(v_h__3_269_, v_val_272_, lean_box(0));
                return v___x_276_;
            }
        } else {
            let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_268_);
            v___x_277_ = lean_apply_2(v_h__3_269_, v_val_272_, lean_box(0));
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(
    mut v_n_278_: *mut LeanObject,
    mut v_motive_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
    mut v_h__1_281_: *mut LeanObject,
    mut v_h__2_282_: *mut LeanObject,
    mut v_h__3_283_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_280_) == 0 {
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_283_);
        lean_dec(v_h__2_282_);
        v___x_284_ = lean_box(0);
        v___x_285_ = lean_apply_1(v_h__1_281_, v___x_284_);
        return v___x_285_;
    } else {
        let mut v_val_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_281_);
        v_val_286_ = lean_ctor_get(v_x_280_, 0);
        lean_inc(v_val_286_);
        lean_dec_ref_known(v_x_280_, 1);
        if lean_obj_tag(v_val_286_) == 1 {
            let mut v_tail_287_: *mut LeanObject = core::ptr::null_mut();
            v_tail_287_ = lean_ctor_get(v_val_286_, 1);
            if lean_obj_tag(v_tail_287_) == 0 {
                let mut v_head_288_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_283_);
                v_head_288_ = lean_ctor_get(v_val_286_, 0);
                lean_inc(v_head_288_);
                lean_dec_ref_known(v_val_286_, 2);
                v___x_289_ = lean_apply_3(v_h__2_282_, v_head_288_, lean_box(0), lean_box(0));
                return v___x_289_;
            } else {
                let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_282_);
                v___x_290_ = lean_apply_2(v_h__3_283_, v_val_286_, lean_box(0));
                return v___x_290_;
            }
        } else {
            let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_282_);
            v___x_291_ = lean_apply_2(v_h__3_283_, v_val_286_, lean_box(0));
            return v___x_291_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter___boxed(
    mut v_n_292_: *mut LeanObject,
    mut v_motive_293_: *mut LeanObject,
    mut v_x_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
    mut v_h__2_296_: *mut LeanObject,
    mut v_h__3_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_298_: *mut LeanObject = core::ptr::null_mut();
    v_res_298_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne_match__1_splitter(v_n_292_, v_motive_293_, v_x_294_, v_h__1_295_, v_h__2_296_, v_h__3_297_);
    lean_dec(v_n_292_);
    return v_res_298_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
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
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
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
    res = initialize_Init_Data_Int_OfNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Lemmas(builtin);
}
