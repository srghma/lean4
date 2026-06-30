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
    mut v_h__1_193_: *mut leanh::LeanObject,
    mut v_h__2_194_: *mut leanh::LeanObject,
    mut v_h__3_195_: *mut leanh::LeanObject,
    mut v_h__4_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_a_192_ {
        0 => {
            let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_196_);
            leanh::lean_dec(v_h__3_195_);
            leanh::lean_dec(v_h__2_194_);
            v___x_197_ = leanh::lean_box(0);
            v___x_198_ = leanh::lean_apply_1(v_h__1_193_, v___x_197_);
            return v___x_198_;
        }
        1 => {
            let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_196_);
            leanh::lean_dec(v_h__3_195_);
            leanh::lean_dec(v_h__1_193_);
            v___x_199_ = leanh::lean_box(0);
            v___x_200_ = leanh::lean_apply_1(v_h__2_194_, v___x_199_);
            return v___x_200_;
        }
        2 => {
            let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_196_);
            leanh::lean_dec(v_h__2_194_);
            leanh::lean_dec(v_h__1_193_);
            v___x_201_ = leanh::lean_box(0);
            v___x_202_ = leanh::lean_apply_1(v_h__3_195_, v___x_201_);
            return v___x_202_;
        }
        _ => {
            let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_195_);
            leanh::lean_dec(v_h__2_194_);
            leanh::lean_dec(v_h__1_193_);
            v___x_203_ = leanh::lean_box(0);
            v___x_204_ = leanh::lean_apply_1(v_h__4_196_, v___x_203_);
            return v___x_204_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_205_: *mut leanh::LeanObject,
    mut v_h__1_206_: *mut leanh::LeanObject,
    mut v_h__2_207_: *mut leanh::LeanObject,
    mut v_h__3_208_: *mut leanh::LeanObject,
    mut v_h__4_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_46__boxed_210_: u8 = 0;
    let mut v_res_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_46__boxed_210_ = (leanh::lean_unbox(v_a_205_) as u8);
    v_res_211_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_210_, v_h__1_206_, v_h__2_207_, v_h__3_208_, v_h__4_209_);
    return v_res_211_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_212_: *mut leanh::LeanObject,
    mut v_a_213_: u8,
    mut v_h__1_214_: *mut leanh::LeanObject,
    mut v_h__2_215_: *mut leanh::LeanObject,
    mut v_h__3_216_: *mut leanh::LeanObject,
    mut v_h__4_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_a_213_ {
        0 => {
            let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_217_);
            leanh::lean_dec(v_h__3_216_);
            leanh::lean_dec(v_h__2_215_);
            v___x_218_ = leanh::lean_box(0);
            v___x_219_ = leanh::lean_apply_1(v_h__1_214_, v___x_218_);
            return v___x_219_;
        }
        1 => {
            let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_217_);
            leanh::lean_dec(v_h__3_216_);
            leanh::lean_dec(v_h__1_214_);
            v___x_220_ = leanh::lean_box(0);
            v___x_221_ = leanh::lean_apply_1(v_h__2_215_, v___x_220_);
            return v___x_221_;
        }
        2 => {
            let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_217_);
            leanh::lean_dec(v_h__2_215_);
            leanh::lean_dec(v_h__1_214_);
            v___x_222_ = leanh::lean_box(0);
            v___x_223_ = leanh::lean_apply_1(v_h__3_216_, v___x_222_);
            return v___x_223_;
        }
        _ => {
            let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_216_);
            leanh::lean_dec(v_h__2_215_);
            leanh::lean_dec(v_h__1_214_);
            v___x_224_ = leanh::lean_box(0);
            v___x_225_ = leanh::lean_apply_1(v_h__4_217_, v___x_224_);
            return v___x_225_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_226_: *mut leanh::LeanObject,
    mut v_a_227_: *mut leanh::LeanObject,
    mut v_h__1_228_: *mut leanh::LeanObject,
    mut v_h__2_229_: *mut leanh::LeanObject,
    mut v_h__3_230_: *mut leanh::LeanObject,
    mut v_h__4_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_65__boxed_232_: u8 = 0;
    let mut v_res_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_65__boxed_232_ = (leanh::lean_unbox(v_a_227_) as u8);
    v_res_233_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_226_, v_a_65__boxed_232_, v_h__1_228_, v_h__2_229_, v_h__3_230_, v_h__4_231_);
    return v_res_233_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(
    mut v_acc_234_: *mut leanh::LeanObject,
    mut v_h__1_235_: *mut leanh::LeanObject,
    mut v_h__2_236_: *mut leanh::LeanObject,
    mut v_h__3_237_: *mut leanh::LeanObject,
    mut v_h__4_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_acc_234_) {
        0 => {
            let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_238_);
            leanh::lean_dec(v_h__3_237_);
            leanh::lean_dec(v_h__2_236_);
            v___x_239_ = leanh::lean_box(0);
            v___x_240_ = leanh::lean_apply_1(v_h__1_235_, v___x_239_);
            return v___x_240_;
        }
        1 => {
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_238_);
            leanh::lean_dec(v_h__3_237_);
            leanh::lean_dec(v_h__1_235_);
            v___x_241_ = leanh::lean_box(0);
            v___x_242_ = leanh::lean_apply_1(v_h__2_236_, v___x_241_);
            return v___x_242_;
        }
        2 => {
            let mut v_l_243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_238_);
            leanh::lean_dec(v_h__2_236_);
            leanh::lean_dec(v_h__1_235_);
            v_l_243_ = leanh::lean_ctor_get(v_acc_234_, 0);
            leanh::lean_inc_ref(v_l_243_);
            leanh::lean_dec_ref_known(v_acc_234_, 1);
            v___x_244_ = leanh::lean_apply_1(v_h__3_237_, v_l_243_);
            return v___x_244_;
        }
        _ => {
            let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_237_);
            leanh::lean_dec(v_h__2_236_);
            leanh::lean_dec(v_h__1_235_);
            v___x_245_ = leanh::lean_box(0);
            v___x_246_ = leanh::lean_apply_1(v_h__4_238_, v___x_245_);
            return v___x_246_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(
    mut v_n_247_: *mut leanh::LeanObject,
    mut v_motive_248_: *mut leanh::LeanObject,
    mut v_acc_249_: *mut leanh::LeanObject,
    mut v_h__1_250_: *mut leanh::LeanObject,
    mut v_h__2_251_: *mut leanh::LeanObject,
    mut v_h__3_252_: *mut leanh::LeanObject,
    mut v_h__4_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_acc_249_) {
        0 => {
            let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_253_);
            leanh::lean_dec(v_h__3_252_);
            leanh::lean_dec(v_h__2_251_);
            v___x_254_ = leanh::lean_box(0);
            v___x_255_ = leanh::lean_apply_1(v_h__1_250_, v___x_254_);
            return v___x_255_;
        }
        1 => {
            let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_253_);
            leanh::lean_dec(v_h__3_252_);
            leanh::lean_dec(v_h__1_250_);
            v___x_256_ = leanh::lean_box(0);
            v___x_257_ = leanh::lean_apply_1(v_h__2_251_, v___x_256_);
            return v___x_257_;
        }
        2 => {
            let mut v_l_258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_253_);
            leanh::lean_dec(v_h__2_251_);
            leanh::lean_dec(v_h__1_250_);
            v_l_258_ = leanh::lean_ctor_get(v_acc_249_, 0);
            leanh::lean_inc_ref(v_l_258_);
            leanh::lean_dec_ref_known(v_acc_249_, 1);
            v___x_259_ = leanh::lean_apply_1(v_h__3_252_, v_l_258_);
            return v___x_259_;
        }
        _ => {
            let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_252_);
            leanh::lean_dec(v_h__2_251_);
            leanh::lean_dec(v_h__1_250_);
            v___x_260_ = leanh::lean_box(0);
            v___x_261_ = leanh::lean_apply_1(v_h__4_253_, v___x_260_);
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(
    mut v_n_262_: *mut leanh::LeanObject,
    mut v_motive_263_: *mut leanh::LeanObject,
    mut v_acc_264_: *mut leanh::LeanObject,
    mut v_h__1_265_: *mut leanh::LeanObject,
    mut v_h__2_266_: *mut leanh::LeanObject,
    mut v_h__3_267_: *mut leanh::LeanObject,
    mut v_h__4_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(v_n_262_, v_motive_263_, v_acc_264_, v_h__1_265_, v_h__2_266_, v_h__3_267_, v_h__4_268_);
    leanh::lean_dec(v_n_262_);
    return v_res_269_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(
    mut v_x_270_: u8,
    mut v_h__1_271_: *mut leanh::LeanObject,
    mut v_h__2_272_: *mut leanh::LeanObject,
    mut v_h__3_273_: *mut leanh::LeanObject,
    mut v_h__4_274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_270_ {
        0 => {
            let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_274_);
            leanh::lean_dec(v_h__3_273_);
            leanh::lean_dec(v_h__2_272_);
            v___x_275_ = leanh::lean_box(0);
            v___x_276_ = leanh::lean_apply_1(v_h__1_271_, v___x_275_);
            return v___x_276_;
        }
        1 => {
            let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_274_);
            leanh::lean_dec(v_h__3_273_);
            leanh::lean_dec(v_h__1_271_);
            v___x_277_ = leanh::lean_box(0);
            v___x_278_ = leanh::lean_apply_1(v_h__2_272_, v___x_277_);
            return v___x_278_;
        }
        2 => {
            let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_274_);
            leanh::lean_dec(v_h__2_272_);
            leanh::lean_dec(v_h__1_271_);
            v___x_279_ = leanh::lean_box(0);
            v___x_280_ = leanh::lean_apply_1(v_h__3_273_, v___x_279_);
            return v___x_280_;
        }
        _ => {
            let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_273_);
            leanh::lean_dec(v_h__2_272_);
            leanh::lean_dec(v_h__1_271_);
            v___x_281_ = leanh::lean_box(0);
            v___x_282_ = leanh::lean_apply_1(v_h__4_274_, v___x_281_);
            return v___x_282_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(
    mut v_x_283_: *mut leanh::LeanObject,
    mut v_h__1_284_: *mut leanh::LeanObject,
    mut v_h__2_285_: *mut leanh::LeanObject,
    mut v_h__3_286_: *mut leanh::LeanObject,
    mut v_h__4_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_46__boxed_288_: u8 = 0;
    let mut v_res_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_46__boxed_288_ = (leanh::lean_unbox(v_x_283_) as u8);
    v_res_289_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_46__boxed_288_, v_h__1_284_, v_h__2_285_, v_h__3_286_, v_h__4_287_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(
    mut v_motive_290_: *mut leanh::LeanObject,
    mut v_x_291_: u8,
    mut v_h__1_292_: *mut leanh::LeanObject,
    mut v_h__2_293_: *mut leanh::LeanObject,
    mut v_h__3_294_: *mut leanh::LeanObject,
    mut v_h__4_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_291_ {
        0 => {
            let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_295_);
            leanh::lean_dec(v_h__3_294_);
            leanh::lean_dec(v_h__2_293_);
            v___x_296_ = leanh::lean_box(0);
            v___x_297_ = leanh::lean_apply_1(v_h__1_292_, v___x_296_);
            return v___x_297_;
        }
        1 => {
            let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_295_);
            leanh::lean_dec(v_h__3_294_);
            leanh::lean_dec(v_h__1_292_);
            v___x_298_ = leanh::lean_box(0);
            v___x_299_ = leanh::lean_apply_1(v_h__2_293_, v___x_298_);
            return v___x_299_;
        }
        2 => {
            let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_295_);
            leanh::lean_dec(v_h__2_293_);
            leanh::lean_dec(v_h__1_292_);
            v___x_300_ = leanh::lean_box(0);
            v___x_301_ = leanh::lean_apply_1(v_h__3_294_, v___x_300_);
            return v___x_301_;
        }
        _ => {
            let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_294_);
            leanh::lean_dec(v_h__2_293_);
            leanh::lean_dec(v_h__1_292_);
            v___x_302_ = leanh::lean_box(0);
            v___x_303_ = leanh::lean_apply_1(v_h__4_295_, v___x_302_);
            return v___x_303_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(
    mut v_motive_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
    mut v_h__1_306_: *mut leanh::LeanObject,
    mut v_h__2_307_: *mut leanh::LeanObject,
    mut v_h__3_308_: *mut leanh::LeanObject,
    mut v_h__4_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_65__boxed_310_: u8 = 0;
    let mut v_res_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_65__boxed_310_ = (leanh::lean_unbox(v_x_305_) as u8);
    v_res_311_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(v_motive_304_, v_x_65__boxed_310_, v_h__1_306_, v_h__2_307_, v_h__3_308_, v_h__4_309_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(
    mut v_x_312_: *mut leanh::LeanObject,
    mut v_h__1_313_: *mut leanh::LeanObject,
    mut v_h__2_314_: *mut leanh::LeanObject,
    mut v_h__3_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_312_) == 0 {
        let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_314_);
        leanh::lean_dec(v_h__1_313_);
        v___x_316_ = leanh::lean_box(0);
        v___x_317_ = leanh::lean_apply_1(v_h__3_315_, v___x_316_);
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_315_);
        v_val_318_ = leanh::lean_ctor_get(v_x_312_, 0);
        leanh::lean_inc(v_val_318_);
        leanh::lean_dec_ref_known(v_x_312_, 1);
        if leanh::lean_obj_tag(v_val_318_) == 0 {
            let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_313_);
            v___x_319_ = leanh::lean_box(0);
            v___x_320_ = leanh::lean_apply_1(v_h__2_314_, v___x_319_);
            return v___x_320_;
        } else {
            let mut v_val_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_314_);
            v_val_321_ = leanh::lean_ctor_get(v_val_318_, 0);
            leanh::lean_inc(v_val_321_);
            leanh::lean_dec_ref_known(v_val_318_, 1);
            v___x_322_ = leanh::lean_apply_1(v_h__1_313_, v_val_321_);
            return v___x_322_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(
    mut v_n_323_: *mut leanh::LeanObject,
    mut v_motive_324_: *mut leanh::LeanObject,
    mut v_x_325_: *mut leanh::LeanObject,
    mut v_h__1_326_: *mut leanh::LeanObject,
    mut v_h__2_327_: *mut leanh::LeanObject,
    mut v_h__3_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_325_) == 0 {
        let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_327_);
        leanh::lean_dec(v_h__1_326_);
        v___x_329_ = leanh::lean_box(0);
        v___x_330_ = leanh::lean_apply_1(v_h__3_328_, v___x_329_);
        return v___x_330_;
    } else {
        let mut v_val_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_328_);
        v_val_331_ = leanh::lean_ctor_get(v_x_325_, 0);
        leanh::lean_inc(v_val_331_);
        leanh::lean_dec_ref_known(v_x_325_, 1);
        if leanh::lean_obj_tag(v_val_331_) == 0 {
            let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_326_);
            v___x_332_ = leanh::lean_box(0);
            v___x_333_ = leanh::lean_apply_1(v_h__2_327_, v___x_332_);
            return v___x_333_;
        } else {
            let mut v_val_334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_327_);
            v_val_334_ = leanh::lean_ctor_get(v_val_331_, 0);
            leanh::lean_inc(v_val_334_);
            leanh::lean_dec_ref_known(v_val_331_, 1);
            v___x_335_ = leanh::lean_apply_1(v_h__1_326_, v_val_334_);
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(
    mut v_n_336_: *mut leanh::LeanObject,
    mut v_motive_337_: *mut leanh::LeanObject,
    mut v_x_338_: *mut leanh::LeanObject,
    mut v_h__1_339_: *mut leanh::LeanObject,
    mut v_h__2_340_: *mut leanh::LeanObject,
    mut v_h__3_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_336_, v_motive_337_, v_x_338_, v_h__1_339_, v_h__2_340_, v_h__3_341_);
    leanh::lean_dec(v_n_336_);
    return v_res_342_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(
    mut v_x_343_: *mut leanh::LeanObject,
    mut v_h__1_344_: *mut leanh::LeanObject,
    mut v_h__2_345_: *mut leanh::LeanObject,
    mut v_h__3_346_: *mut leanh::LeanObject,
    mut v_h__4_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_343_) {
        0 => {
            let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_347_);
            leanh::lean_dec(v_h__3_346_);
            leanh::lean_dec(v_h__2_345_);
            v___x_348_ = leanh::lean_box(0);
            v___x_349_ = leanh::lean_apply_1(v_h__1_344_, v___x_348_);
            return v___x_349_;
        }
        1 => {
            let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_347_);
            leanh::lean_dec(v_h__3_346_);
            leanh::lean_dec(v_h__1_344_);
            v___x_350_ = leanh::lean_box(0);
            v___x_351_ = leanh::lean_apply_1(v_h__2_345_, v___x_350_);
            return v___x_351_;
        }
        2 => {
            let mut v_l_352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_347_);
            leanh::lean_dec(v_h__2_345_);
            leanh::lean_dec(v_h__1_344_);
            v_l_352_ = leanh::lean_ctor_get(v_x_343_, 0);
            leanh::lean_inc_ref(v_l_352_);
            leanh::lean_dec_ref_known(v_x_343_, 1);
            v_fst_353_ = leanh::lean_ctor_get(v_l_352_, 0);
            leanh::lean_inc(v_fst_353_);
            v_snd_354_ = leanh::lean_ctor_get(v_l_352_, 1);
            leanh::lean_inc(v_snd_354_);
            leanh::lean_dec_ref(v_l_352_);
            v___x_355_ = leanh::lean_apply_2(v_h__3_346_, v_fst_353_, v_snd_354_);
            return v___x_355_;
        }
        _ => {
            let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_346_);
            leanh::lean_dec(v_h__2_345_);
            leanh::lean_dec(v_h__1_344_);
            v___x_356_ = leanh::lean_box(0);
            v___x_357_ = leanh::lean_apply_1(v_h__4_347_, v___x_356_);
            return v___x_357_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(
    mut v_n_358_: *mut leanh::LeanObject,
    mut v_motive_359_: *mut leanh::LeanObject,
    mut v_x_360_: *mut leanh::LeanObject,
    mut v_h__1_361_: *mut leanh::LeanObject,
    mut v_h__2_362_: *mut leanh::LeanObject,
    mut v_h__3_363_: *mut leanh::LeanObject,
    mut v_h__4_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_360_) {
        0 => {
            let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_364_);
            leanh::lean_dec(v_h__3_363_);
            leanh::lean_dec(v_h__2_362_);
            v___x_365_ = leanh::lean_box(0);
            v___x_366_ = leanh::lean_apply_1(v_h__1_361_, v___x_365_);
            return v___x_366_;
        }
        1 => {
            let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_364_);
            leanh::lean_dec(v_h__3_363_);
            leanh::lean_dec(v_h__1_361_);
            v___x_367_ = leanh::lean_box(0);
            v___x_368_ = leanh::lean_apply_1(v_h__2_362_, v___x_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_l_369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_371_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_364_);
            leanh::lean_dec(v_h__2_362_);
            leanh::lean_dec(v_h__1_361_);
            v_l_369_ = leanh::lean_ctor_get(v_x_360_, 0);
            leanh::lean_inc_ref(v_l_369_);
            leanh::lean_dec_ref_known(v_x_360_, 1);
            v_fst_370_ = leanh::lean_ctor_get(v_l_369_, 0);
            leanh::lean_inc(v_fst_370_);
            v_snd_371_ = leanh::lean_ctor_get(v_l_369_, 1);
            leanh::lean_inc(v_snd_371_);
            leanh::lean_dec_ref(v_l_369_);
            v___x_372_ = leanh::lean_apply_2(v_h__3_363_, v_fst_370_, v_snd_371_);
            return v___x_372_;
        }
        _ => {
            let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_363_);
            leanh::lean_dec(v_h__2_362_);
            leanh::lean_dec(v_h__1_361_);
            v___x_373_ = leanh::lean_box(0);
            v___x_374_ = leanh::lean_apply_1(v_h__4_364_, v___x_373_);
            return v___x_374_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(
    mut v_n_375_: *mut leanh::LeanObject,
    mut v_motive_376_: *mut leanh::LeanObject,
    mut v_x_377_: *mut leanh::LeanObject,
    mut v_h__1_378_: *mut leanh::LeanObject,
    mut v_h__2_379_: *mut leanh::LeanObject,
    mut v_h__3_380_: *mut leanh::LeanObject,
    mut v_h__4_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_375_, v_motive_376_, v_x_377_, v_h__1_378_, v_h__2_379_, v_h__3_380_, v_h__4_381_);
    leanh::lean_dec(v_n_375_);
    return v_res_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
}