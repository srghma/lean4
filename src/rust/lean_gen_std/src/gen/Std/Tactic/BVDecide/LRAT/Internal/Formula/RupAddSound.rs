// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult Init.ByCases Init.Data.Array.Bootstrap Init.Data.Int.OfNat Init.Data.Nat.Linear Init.Data.Nat.Simproc
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
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
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RupAddResult::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(
    mut v_a_192_: u8,
    mut v_h__1_193_: *mut crate::leanh::LeanObject,
    mut v_h__2_194_: *mut crate::leanh::LeanObject,
    mut v_h__3_195_: *mut crate::leanh::LeanObject,
    mut v_h__4_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_192_ {
        0 => {
            let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_196_);
            crate::leanh::lean_dec(v_h__3_195_);
            crate::leanh::lean_dec(v_h__2_194_);
            v___x_197_ = crate::leanh::lean_box(0);
            v___x_198_ = crate::leanh::lean_apply_1(v_h__1_193_, v___x_197_);
            return v___x_198_;
        }
        1 => {
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_196_);
            crate::leanh::lean_dec(v_h__3_195_);
            crate::leanh::lean_dec(v_h__1_193_);
            v___x_199_ = crate::leanh::lean_box(0);
            v___x_200_ = crate::leanh::lean_apply_1(v_h__2_194_, v___x_199_);
            return v___x_200_;
        }
        2 => {
            let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_196_);
            crate::leanh::lean_dec(v_h__2_194_);
            crate::leanh::lean_dec(v_h__1_193_);
            v___x_201_ = crate::leanh::lean_box(0);
            v___x_202_ = crate::leanh::lean_apply_1(v_h__3_195_, v___x_201_);
            return v___x_202_;
        }
        _ => {
            let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_195_);
            crate::leanh::lean_dec(v_h__2_194_);
            crate::leanh::lean_dec(v_h__1_193_);
            v___x_203_ = crate::leanh::lean_box(0);
            v___x_204_ = crate::leanh::lean_apply_1(v_h__4_196_, v___x_203_);
            return v___x_204_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_205_: *mut crate::leanh::LeanObject,
    mut v_h__1_206_: *mut crate::leanh::LeanObject,
    mut v_h__2_207_: *mut crate::leanh::LeanObject,
    mut v_h__3_208_: *mut crate::leanh::LeanObject,
    mut v_h__4_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_46__boxed_210_: u8 = 0;
    let mut v_res_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_46__boxed_210_ = (crate::leanh::lean_unbox(v_a_205_) as u8);
    v_res_211_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_210_, v_h__1_206_, v_h__2_207_, v_h__3_208_, v_h__4_209_);
    return v_res_211_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_212_: *mut crate::leanh::LeanObject,
    mut v_a_213_: u8,
    mut v_h__1_214_: *mut crate::leanh::LeanObject,
    mut v_h__2_215_: *mut crate::leanh::LeanObject,
    mut v_h__3_216_: *mut crate::leanh::LeanObject,
    mut v_h__4_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_213_ {
        0 => {
            let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_217_);
            crate::leanh::lean_dec(v_h__3_216_);
            crate::leanh::lean_dec(v_h__2_215_);
            v___x_218_ = crate::leanh::lean_box(0);
            v___x_219_ = crate::leanh::lean_apply_1(v_h__1_214_, v___x_218_);
            return v___x_219_;
        }
        1 => {
            let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_217_);
            crate::leanh::lean_dec(v_h__3_216_);
            crate::leanh::lean_dec(v_h__1_214_);
            v___x_220_ = crate::leanh::lean_box(0);
            v___x_221_ = crate::leanh::lean_apply_1(v_h__2_215_, v___x_220_);
            return v___x_221_;
        }
        2 => {
            let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_217_);
            crate::leanh::lean_dec(v_h__2_215_);
            crate::leanh::lean_dec(v_h__1_214_);
            v___x_222_ = crate::leanh::lean_box(0);
            v___x_223_ = crate::leanh::lean_apply_1(v_h__3_216_, v___x_222_);
            return v___x_223_;
        }
        _ => {
            let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_216_);
            crate::leanh::lean_dec(v_h__2_215_);
            crate::leanh::lean_dec(v_h__1_214_);
            v___x_224_ = crate::leanh::lean_box(0);
            v___x_225_ = crate::leanh::lean_apply_1(v_h__4_217_, v___x_224_);
            return v___x_225_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_226_: *mut crate::leanh::LeanObject,
    mut v_a_227_: *mut crate::leanh::LeanObject,
    mut v_h__1_228_: *mut crate::leanh::LeanObject,
    mut v_h__2_229_: *mut crate::leanh::LeanObject,
    mut v_h__3_230_: *mut crate::leanh::LeanObject,
    mut v_h__4_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_65__boxed_232_: u8 = 0;
    let mut v_res_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_65__boxed_232_ = (crate::leanh::lean_unbox(v_a_227_) as u8);
    v_res_233_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_226_, v_a_65__boxed_232_, v_h__1_228_, v_h__2_229_, v_h__3_230_, v_h__4_231_);
    return v_res_233_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(
    mut v_acc_234_: *mut crate::leanh::LeanObject,
    mut v_h__1_235_: *mut crate::leanh::LeanObject,
    mut v_h__2_236_: *mut crate::leanh::LeanObject,
    mut v_h__3_237_: *mut crate::leanh::LeanObject,
    mut v_h__4_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_acc_234_) {
        0 => {
            let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_238_);
            crate::leanh::lean_dec(v_h__3_237_);
            crate::leanh::lean_dec(v_h__2_236_);
            v___x_239_ = crate::leanh::lean_box(0);
            v___x_240_ = crate::leanh::lean_apply_1(v_h__1_235_, v___x_239_);
            return v___x_240_;
        }
        1 => {
            let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_238_);
            crate::leanh::lean_dec(v_h__3_237_);
            crate::leanh::lean_dec(v_h__1_235_);
            v___x_241_ = crate::leanh::lean_box(0);
            v___x_242_ = crate::leanh::lean_apply_1(v_h__2_236_, v___x_241_);
            return v___x_242_;
        }
        2 => {
            let mut v_l_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_238_);
            crate::leanh::lean_dec(v_h__2_236_);
            crate::leanh::lean_dec(v_h__1_235_);
            v_l_243_ = crate::leanh::lean_ctor_get(v_acc_234_, 0);
            crate::leanh::lean_inc_ref(v_l_243_);
            crate::leanh::lean_dec_ref_known(v_acc_234_, 1);
            v___x_244_ = crate::leanh::lean_apply_1(v_h__3_237_, v_l_243_);
            return v___x_244_;
        }
        _ => {
            let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_237_);
            crate::leanh::lean_dec(v_h__2_236_);
            crate::leanh::lean_dec(v_h__1_235_);
            v___x_245_ = crate::leanh::lean_box(0);
            v___x_246_ = crate::leanh::lean_apply_1(v_h__4_238_, v___x_245_);
            return v___x_246_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(
    mut v_n_247_: *mut crate::leanh::LeanObject,
    mut v_motive_248_: *mut crate::leanh::LeanObject,
    mut v_acc_249_: *mut crate::leanh::LeanObject,
    mut v_h__1_250_: *mut crate::leanh::LeanObject,
    mut v_h__2_251_: *mut crate::leanh::LeanObject,
    mut v_h__3_252_: *mut crate::leanh::LeanObject,
    mut v_h__4_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_acc_249_) {
        0 => {
            let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_253_);
            crate::leanh::lean_dec(v_h__3_252_);
            crate::leanh::lean_dec(v_h__2_251_);
            v___x_254_ = crate::leanh::lean_box(0);
            v___x_255_ = crate::leanh::lean_apply_1(v_h__1_250_, v___x_254_);
            return v___x_255_;
        }
        1 => {
            let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_253_);
            crate::leanh::lean_dec(v_h__3_252_);
            crate::leanh::lean_dec(v_h__1_250_);
            v___x_256_ = crate::leanh::lean_box(0);
            v___x_257_ = crate::leanh::lean_apply_1(v_h__2_251_, v___x_256_);
            return v___x_257_;
        }
        2 => {
            let mut v_l_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_253_);
            crate::leanh::lean_dec(v_h__2_251_);
            crate::leanh::lean_dec(v_h__1_250_);
            v_l_258_ = crate::leanh::lean_ctor_get(v_acc_249_, 0);
            crate::leanh::lean_inc_ref(v_l_258_);
            crate::leanh::lean_dec_ref_known(v_acc_249_, 1);
            v___x_259_ = crate::leanh::lean_apply_1(v_h__3_252_, v_l_258_);
            return v___x_259_;
        }
        _ => {
            let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_252_);
            crate::leanh::lean_dec(v_h__2_251_);
            crate::leanh::lean_dec(v_h__1_250_);
            v___x_260_ = crate::leanh::lean_box(0);
            v___x_261_ = crate::leanh::lean_apply_1(v_h__4_253_, v___x_260_);
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(
    mut v_n_262_: *mut crate::leanh::LeanObject,
    mut v_motive_263_: *mut crate::leanh::LeanObject,
    mut v_acc_264_: *mut crate::leanh::LeanObject,
    mut v_h__1_265_: *mut crate::leanh::LeanObject,
    mut v_h__2_266_: *mut crate::leanh::LeanObject,
    mut v_h__3_267_: *mut crate::leanh::LeanObject,
    mut v_h__4_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(v_n_262_, v_motive_263_, v_acc_264_, v_h__1_265_, v_h__2_266_, v_h__3_267_, v_h__4_268_);
    crate::leanh::lean_dec(v_n_262_);
    return v_res_269_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(
    mut v_x_270_: u8,
    mut v_h__1_271_: *mut crate::leanh::LeanObject,
    mut v_h__2_272_: *mut crate::leanh::LeanObject,
    mut v_h__3_273_: *mut crate::leanh::LeanObject,
    mut v_h__4_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_270_ {
        0 => {
            let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_274_);
            crate::leanh::lean_dec(v_h__3_273_);
            crate::leanh::lean_dec(v_h__2_272_);
            v___x_275_ = crate::leanh::lean_box(0);
            v___x_276_ = crate::leanh::lean_apply_1(v_h__1_271_, v___x_275_);
            return v___x_276_;
        }
        1 => {
            let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_274_);
            crate::leanh::lean_dec(v_h__3_273_);
            crate::leanh::lean_dec(v_h__1_271_);
            v___x_277_ = crate::leanh::lean_box(0);
            v___x_278_ = crate::leanh::lean_apply_1(v_h__2_272_, v___x_277_);
            return v___x_278_;
        }
        2 => {
            let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_274_);
            crate::leanh::lean_dec(v_h__2_272_);
            crate::leanh::lean_dec(v_h__1_271_);
            v___x_279_ = crate::leanh::lean_box(0);
            v___x_280_ = crate::leanh::lean_apply_1(v_h__3_273_, v___x_279_);
            return v___x_280_;
        }
        _ => {
            let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_273_);
            crate::leanh::lean_dec(v_h__2_272_);
            crate::leanh::lean_dec(v_h__1_271_);
            v___x_281_ = crate::leanh::lean_box(0);
            v___x_282_ = crate::leanh::lean_apply_1(v_h__4_274_, v___x_281_);
            return v___x_282_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(
    mut v_x_283_: *mut crate::leanh::LeanObject,
    mut v_h__1_284_: *mut crate::leanh::LeanObject,
    mut v_h__2_285_: *mut crate::leanh::LeanObject,
    mut v_h__3_286_: *mut crate::leanh::LeanObject,
    mut v_h__4_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_46__boxed_288_: u8 = 0;
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_46__boxed_288_ = (crate::leanh::lean_unbox(v_x_283_) as u8);
    v_res_289_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_46__boxed_288_, v_h__1_284_, v_h__2_285_, v_h__3_286_, v_h__4_287_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(
    mut v_motive_290_: *mut crate::leanh::LeanObject,
    mut v_x_291_: u8,
    mut v_h__1_292_: *mut crate::leanh::LeanObject,
    mut v_h__2_293_: *mut crate::leanh::LeanObject,
    mut v_h__3_294_: *mut crate::leanh::LeanObject,
    mut v_h__4_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_291_ {
        0 => {
            let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_295_);
            crate::leanh::lean_dec(v_h__3_294_);
            crate::leanh::lean_dec(v_h__2_293_);
            v___x_296_ = crate::leanh::lean_box(0);
            v___x_297_ = crate::leanh::lean_apply_1(v_h__1_292_, v___x_296_);
            return v___x_297_;
        }
        1 => {
            let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_295_);
            crate::leanh::lean_dec(v_h__3_294_);
            crate::leanh::lean_dec(v_h__1_292_);
            v___x_298_ = crate::leanh::lean_box(0);
            v___x_299_ = crate::leanh::lean_apply_1(v_h__2_293_, v___x_298_);
            return v___x_299_;
        }
        2 => {
            let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_295_);
            crate::leanh::lean_dec(v_h__2_293_);
            crate::leanh::lean_dec(v_h__1_292_);
            v___x_300_ = crate::leanh::lean_box(0);
            v___x_301_ = crate::leanh::lean_apply_1(v_h__3_294_, v___x_300_);
            return v___x_301_;
        }
        _ => {
            let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_294_);
            crate::leanh::lean_dec(v_h__2_293_);
            crate::leanh::lean_dec(v_h__1_292_);
            v___x_302_ = crate::leanh::lean_box(0);
            v___x_303_ = crate::leanh::lean_apply_1(v_h__4_295_, v___x_302_);
            return v___x_303_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(
    mut v_motive_304_: *mut crate::leanh::LeanObject,
    mut v_x_305_: *mut crate::leanh::LeanObject,
    mut v_h__1_306_: *mut crate::leanh::LeanObject,
    mut v_h__2_307_: *mut crate::leanh::LeanObject,
    mut v_h__3_308_: *mut crate::leanh::LeanObject,
    mut v_h__4_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_65__boxed_310_: u8 = 0;
    let mut v_res_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_65__boxed_310_ = (crate::leanh::lean_unbox(v_x_305_) as u8);
    v_res_311_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(v_motive_304_, v_x_65__boxed_310_, v_h__1_306_, v_h__2_307_, v_h__3_308_, v_h__4_309_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(
    mut v_x_312_: *mut crate::leanh::LeanObject,
    mut v_h__1_313_: *mut crate::leanh::LeanObject,
    mut v_h__2_314_: *mut crate::leanh::LeanObject,
    mut v_h__3_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_312_) == 0 {
        let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_314_);
        crate::leanh::lean_dec(v_h__1_313_);
        v___x_316_ = crate::leanh::lean_box(0);
        v___x_317_ = crate::leanh::lean_apply_1(v_h__3_315_, v___x_316_);
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_315_);
        v_val_318_ = crate::leanh::lean_ctor_get(v_x_312_, 0);
        crate::leanh::lean_inc(v_val_318_);
        crate::leanh::lean_dec_ref_known(v_x_312_, 1);
        if crate::leanh::lean_obj_tag(v_val_318_) == 0 {
            let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_313_);
            v___x_319_ = crate::leanh::lean_box(0);
            v___x_320_ = crate::leanh::lean_apply_1(v_h__2_314_, v___x_319_);
            return v___x_320_;
        } else {
            let mut v_val_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_314_);
            v_val_321_ = crate::leanh::lean_ctor_get(v_val_318_, 0);
            crate::leanh::lean_inc(v_val_321_);
            crate::leanh::lean_dec_ref_known(v_val_318_, 1);
            v___x_322_ = crate::leanh::lean_apply_1(v_h__1_313_, v_val_321_);
            return v___x_322_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(
    mut v_n_323_: *mut crate::leanh::LeanObject,
    mut v_motive_324_: *mut crate::leanh::LeanObject,
    mut v_x_325_: *mut crate::leanh::LeanObject,
    mut v_h__1_326_: *mut crate::leanh::LeanObject,
    mut v_h__2_327_: *mut crate::leanh::LeanObject,
    mut v_h__3_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_325_) == 0 {
        let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_327_);
        crate::leanh::lean_dec(v_h__1_326_);
        v___x_329_ = crate::leanh::lean_box(0);
        v___x_330_ = crate::leanh::lean_apply_1(v_h__3_328_, v___x_329_);
        return v___x_330_;
    } else {
        let mut v_val_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_328_);
        v_val_331_ = crate::leanh::lean_ctor_get(v_x_325_, 0);
        crate::leanh::lean_inc(v_val_331_);
        crate::leanh::lean_dec_ref_known(v_x_325_, 1);
        if crate::leanh::lean_obj_tag(v_val_331_) == 0 {
            let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_326_);
            v___x_332_ = crate::leanh::lean_box(0);
            v___x_333_ = crate::leanh::lean_apply_1(v_h__2_327_, v___x_332_);
            return v___x_333_;
        } else {
            let mut v_val_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_327_);
            v_val_334_ = crate::leanh::lean_ctor_get(v_val_331_, 0);
            crate::leanh::lean_inc(v_val_334_);
            crate::leanh::lean_dec_ref_known(v_val_331_, 1);
            v___x_335_ = crate::leanh::lean_apply_1(v_h__1_326_, v_val_334_);
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(
    mut v_n_336_: *mut crate::leanh::LeanObject,
    mut v_motive_337_: *mut crate::leanh::LeanObject,
    mut v_x_338_: *mut crate::leanh::LeanObject,
    mut v_h__1_339_: *mut crate::leanh::LeanObject,
    mut v_h__2_340_: *mut crate::leanh::LeanObject,
    mut v_h__3_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_336_, v_motive_337_, v_x_338_, v_h__1_339_, v_h__2_340_, v_h__3_341_);
    crate::leanh::lean_dec(v_n_336_);
    return v_res_342_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(
    mut v_x_343_: *mut crate::leanh::LeanObject,
    mut v_h__1_344_: *mut crate::leanh::LeanObject,
    mut v_h__2_345_: *mut crate::leanh::LeanObject,
    mut v_h__3_346_: *mut crate::leanh::LeanObject,
    mut v_h__4_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_343_) {
        0 => {
            let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_347_);
            crate::leanh::lean_dec(v_h__3_346_);
            crate::leanh::lean_dec(v_h__2_345_);
            v___x_348_ = crate::leanh::lean_box(0);
            v___x_349_ = crate::leanh::lean_apply_1(v_h__1_344_, v___x_348_);
            return v___x_349_;
        }
        1 => {
            let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_347_);
            crate::leanh::lean_dec(v_h__3_346_);
            crate::leanh::lean_dec(v_h__1_344_);
            v___x_350_ = crate::leanh::lean_box(0);
            v___x_351_ = crate::leanh::lean_apply_1(v_h__2_345_, v___x_350_);
            return v___x_351_;
        }
        2 => {
            let mut v_l_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_347_);
            crate::leanh::lean_dec(v_h__2_345_);
            crate::leanh::lean_dec(v_h__1_344_);
            v_l_352_ = crate::leanh::lean_ctor_get(v_x_343_, 0);
            crate::leanh::lean_inc_ref(v_l_352_);
            crate::leanh::lean_dec_ref_known(v_x_343_, 1);
            v_fst_353_ = crate::leanh::lean_ctor_get(v_l_352_, 0);
            crate::leanh::lean_inc(v_fst_353_);
            v_snd_354_ = crate::leanh::lean_ctor_get(v_l_352_, 1);
            crate::leanh::lean_inc(v_snd_354_);
            crate::leanh::lean_dec_ref(v_l_352_);
            v___x_355_ = crate::leanh::lean_apply_2(v_h__3_346_, v_fst_353_, v_snd_354_);
            return v___x_355_;
        }
        _ => {
            let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_346_);
            crate::leanh::lean_dec(v_h__2_345_);
            crate::leanh::lean_dec(v_h__1_344_);
            v___x_356_ = crate::leanh::lean_box(0);
            v___x_357_ = crate::leanh::lean_apply_1(v_h__4_347_, v___x_356_);
            return v___x_357_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(
    mut v_n_358_: *mut crate::leanh::LeanObject,
    mut v_motive_359_: *mut crate::leanh::LeanObject,
    mut v_x_360_: *mut crate::leanh::LeanObject,
    mut v_h__1_361_: *mut crate::leanh::LeanObject,
    mut v_h__2_362_: *mut crate::leanh::LeanObject,
    mut v_h__3_363_: *mut crate::leanh::LeanObject,
    mut v_h__4_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_360_) {
        0 => {
            let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_364_);
            crate::leanh::lean_dec(v_h__3_363_);
            crate::leanh::lean_dec(v_h__2_362_);
            v___x_365_ = crate::leanh::lean_box(0);
            v___x_366_ = crate::leanh::lean_apply_1(v_h__1_361_, v___x_365_);
            return v___x_366_;
        }
        1 => {
            let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_364_);
            crate::leanh::lean_dec(v_h__3_363_);
            crate::leanh::lean_dec(v_h__1_361_);
            v___x_367_ = crate::leanh::lean_box(0);
            v___x_368_ = crate::leanh::lean_apply_1(v_h__2_362_, v___x_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_l_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_364_);
            crate::leanh::lean_dec(v_h__2_362_);
            crate::leanh::lean_dec(v_h__1_361_);
            v_l_369_ = crate::leanh::lean_ctor_get(v_x_360_, 0);
            crate::leanh::lean_inc_ref(v_l_369_);
            crate::leanh::lean_dec_ref_known(v_x_360_, 1);
            v_fst_370_ = crate::leanh::lean_ctor_get(v_l_369_, 0);
            crate::leanh::lean_inc(v_fst_370_);
            v_snd_371_ = crate::leanh::lean_ctor_get(v_l_369_, 1);
            crate::leanh::lean_inc(v_snd_371_);
            crate::leanh::lean_dec_ref(v_l_369_);
            v___x_372_ = crate::leanh::lean_apply_2(v_h__3_363_, v_fst_370_, v_snd_371_);
            return v___x_372_;
        }
        _ => {
            let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_363_);
            crate::leanh::lean_dec(v_h__2_362_);
            crate::leanh::lean_dec(v_h__1_361_);
            v___x_373_ = crate::leanh::lean_box(0);
            v___x_374_ = crate::leanh::lean_apply_1(v_h__4_364_, v___x_373_);
            return v___x_374_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(
    mut v_n_375_: *mut crate::leanh::LeanObject,
    mut v_motive_376_: *mut crate::leanh::LeanObject,
    mut v_x_377_: *mut crate::leanh::LeanObject,
    mut v_h__1_378_: *mut crate::leanh::LeanObject,
    mut v_h__2_379_: *mut crate::leanh::LeanObject,
    mut v_h__3_380_: *mut crate::leanh::LeanObject,
    mut v_h__4_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_375_, v_motive_376_, v_x_377_, v_h__1_378_, v_h__2_379_, v_h__3_380_, v_h__4_381_);
    crate::leanh::lean_dec(v_n_375_);
    return v_res_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
}
