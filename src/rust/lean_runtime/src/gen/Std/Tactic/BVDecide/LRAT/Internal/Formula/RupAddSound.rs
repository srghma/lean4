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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(
    mut v_a_192_: u8,
    mut v_h__1_193_: *mut LeanObject,
    mut v_h__2_194_: *mut LeanObject,
    mut v_h__3_195_: *mut LeanObject,
    mut v_h__4_196_: *mut LeanObject,
) -> *mut LeanObject {
    match v_a_192_ {
        0 => {
            let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_196_);
            lean_dec(v_h__3_195_);
            lean_dec(v_h__2_194_);
            v___x_197_ = lean_box(0);
            v___x_198_ = lean_apply_1(v_h__1_193_, v___x_197_);
            return v___x_198_;
        }
        1 => {
            let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_196_);
            lean_dec(v_h__3_195_);
            lean_dec(v_h__1_193_);
            v___x_199_ = lean_box(0);
            v___x_200_ = lean_apply_1(v_h__2_194_, v___x_199_);
            return v___x_200_;
        }
        2 => {
            let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_196_);
            lean_dec(v_h__2_194_);
            lean_dec(v_h__1_193_);
            v___x_201_ = lean_box(0);
            v___x_202_ = lean_apply_1(v_h__3_195_, v___x_201_);
            return v___x_202_;
        }
        _ => {
            let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_195_);
            lean_dec(v_h__2_194_);
            lean_dec(v_h__1_193_);
            v___x_203_ = lean_box(0);
            v___x_204_ = lean_apply_1(v_h__4_196_, v___x_203_);
            return v___x_204_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_205_: *mut LeanObject,
    mut v_h__1_206_: *mut LeanObject,
    mut v_h__2_207_: *mut LeanObject,
    mut v_h__3_208_: *mut LeanObject,
    mut v_h__4_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_46__boxed_210_: u8 = 0;
    let mut v_res_211_: *mut LeanObject = core::ptr::null_mut();
    v_a_46__boxed_210_ = (lean_unbox(v_a_205_) as u8);
    v_res_211_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_210_, v_h__1_206_, v_h__2_207_, v_h__3_208_, v_h__4_209_);
    return v_res_211_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_212_: *mut LeanObject,
    mut v_a_213_: u8,
    mut v_h__1_214_: *mut LeanObject,
    mut v_h__2_215_: *mut LeanObject,
    mut v_h__3_216_: *mut LeanObject,
    mut v_h__4_217_: *mut LeanObject,
) -> *mut LeanObject {
    match v_a_213_ {
        0 => {
            let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_217_);
            lean_dec(v_h__3_216_);
            lean_dec(v_h__2_215_);
            v___x_218_ = lean_box(0);
            v___x_219_ = lean_apply_1(v_h__1_214_, v___x_218_);
            return v___x_219_;
        }
        1 => {
            let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_217_);
            lean_dec(v_h__3_216_);
            lean_dec(v_h__1_214_);
            v___x_220_ = lean_box(0);
            v___x_221_ = lean_apply_1(v_h__2_215_, v___x_220_);
            return v___x_221_;
        }
        2 => {
            let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_217_);
            lean_dec(v_h__2_215_);
            lean_dec(v_h__1_214_);
            v___x_222_ = lean_box(0);
            v___x_223_ = lean_apply_1(v_h__3_216_, v___x_222_);
            return v___x_223_;
        }
        _ => {
            let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_216_);
            lean_dec(v_h__2_215_);
            lean_dec(v_h__1_214_);
            v___x_224_ = lean_box(0);
            v___x_225_ = lean_apply_1(v_h__4_217_, v___x_224_);
            return v___x_225_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_226_: *mut LeanObject,
    mut v_a_227_: *mut LeanObject,
    mut v_h__1_228_: *mut LeanObject,
    mut v_h__2_229_: *mut LeanObject,
    mut v_h__3_230_: *mut LeanObject,
    mut v_h__4_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_65__boxed_232_: u8 = 0;
    let mut v_res_233_: *mut LeanObject = core::ptr::null_mut();
    v_a_65__boxed_232_ = (lean_unbox(v_a_227_) as u8);
    v_res_233_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_226_, v_a_65__boxed_232_, v_h__1_228_, v_h__2_229_, v_h__3_230_, v_h__4_231_);
    return v_res_233_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(
    mut v_acc_234_: *mut LeanObject,
    mut v_h__1_235_: *mut LeanObject,
    mut v_h__2_236_: *mut LeanObject,
    mut v_h__3_237_: *mut LeanObject,
    mut v_h__4_238_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_acc_234_) {
        0 => {
            let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_238_);
            lean_dec(v_h__3_237_);
            lean_dec(v_h__2_236_);
            v___x_239_ = lean_box(0);
            v___x_240_ = lean_apply_1(v_h__1_235_, v___x_239_);
            return v___x_240_;
        }
        1 => {
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_238_);
            lean_dec(v_h__3_237_);
            lean_dec(v_h__1_235_);
            v___x_241_ = lean_box(0);
            v___x_242_ = lean_apply_1(v_h__2_236_, v___x_241_);
            return v___x_242_;
        }
        2 => {
            let mut v_l_243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_238_);
            lean_dec(v_h__2_236_);
            lean_dec(v_h__1_235_);
            v_l_243_ = lean_ctor_get(v_acc_234_, 0);
            lean_inc_ref(v_l_243_);
            lean_dec_ref_known(v_acc_234_, 1);
            v___x_244_ = lean_apply_1(v_h__3_237_, v_l_243_);
            return v___x_244_;
        }
        _ => {
            let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_237_);
            lean_dec(v_h__2_236_);
            lean_dec(v_h__1_235_);
            v___x_245_ = lean_box(0);
            v___x_246_ = lean_apply_1(v_h__4_238_, v___x_245_);
            return v___x_246_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(
    mut v_n_247_: *mut LeanObject,
    mut v_motive_248_: *mut LeanObject,
    mut v_acc_249_: *mut LeanObject,
    mut v_h__1_250_: *mut LeanObject,
    mut v_h__2_251_: *mut LeanObject,
    mut v_h__3_252_: *mut LeanObject,
    mut v_h__4_253_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_acc_249_) {
        0 => {
            let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_253_);
            lean_dec(v_h__3_252_);
            lean_dec(v_h__2_251_);
            v___x_254_ = lean_box(0);
            v___x_255_ = lean_apply_1(v_h__1_250_, v___x_254_);
            return v___x_255_;
        }
        1 => {
            let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_253_);
            lean_dec(v_h__3_252_);
            lean_dec(v_h__1_250_);
            v___x_256_ = lean_box(0);
            v___x_257_ = lean_apply_1(v_h__2_251_, v___x_256_);
            return v___x_257_;
        }
        2 => {
            let mut v_l_258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_253_);
            lean_dec(v_h__2_251_);
            lean_dec(v_h__1_250_);
            v_l_258_ = lean_ctor_get(v_acc_249_, 0);
            lean_inc_ref(v_l_258_);
            lean_dec_ref_known(v_acc_249_, 1);
            v___x_259_ = lean_apply_1(v_h__3_252_, v_l_258_);
            return v___x_259_;
        }
        _ => {
            let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_252_);
            lean_dec(v_h__2_251_);
            lean_dec(v_h__1_250_);
            v___x_260_ = lean_box(0);
            v___x_261_ = lean_apply_1(v_h__4_253_, v___x_260_);
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(
    mut v_n_262_: *mut LeanObject,
    mut v_motive_263_: *mut LeanObject,
    mut v_acc_264_: *mut LeanObject,
    mut v_h__1_265_: *mut LeanObject,
    mut v_h__2_266_: *mut LeanObject,
    mut v_h__3_267_: *mut LeanObject,
    mut v_h__4_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_269_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(v_n_262_, v_motive_263_, v_acc_264_, v_h__1_265_, v_h__2_266_, v_h__3_267_, v_h__4_268_);
    lean_dec(v_n_262_);
    return v_res_269_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(
    mut v_x_270_: u8,
    mut v_h__1_271_: *mut LeanObject,
    mut v_h__2_272_: *mut LeanObject,
    mut v_h__3_273_: *mut LeanObject,
    mut v_h__4_274_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_270_ {
        0 => {
            let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_274_);
            lean_dec(v_h__3_273_);
            lean_dec(v_h__2_272_);
            v___x_275_ = lean_box(0);
            v___x_276_ = lean_apply_1(v_h__1_271_, v___x_275_);
            return v___x_276_;
        }
        1 => {
            let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_274_);
            lean_dec(v_h__3_273_);
            lean_dec(v_h__1_271_);
            v___x_277_ = lean_box(0);
            v___x_278_ = lean_apply_1(v_h__2_272_, v___x_277_);
            return v___x_278_;
        }
        2 => {
            let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_274_);
            lean_dec(v_h__2_272_);
            lean_dec(v_h__1_271_);
            v___x_279_ = lean_box(0);
            v___x_280_ = lean_apply_1(v_h__3_273_, v___x_279_);
            return v___x_280_;
        }
        _ => {
            let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_273_);
            lean_dec(v_h__2_272_);
            lean_dec(v_h__1_271_);
            v___x_281_ = lean_box(0);
            v___x_282_ = lean_apply_1(v_h__4_274_, v___x_281_);
            return v___x_282_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(
    mut v_x_283_: *mut LeanObject,
    mut v_h__1_284_: *mut LeanObject,
    mut v_h__2_285_: *mut LeanObject,
    mut v_h__3_286_: *mut LeanObject,
    mut v_h__4_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_46__boxed_288_: u8 = 0;
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_x_46__boxed_288_ = (lean_unbox(v_x_283_) as u8);
    v_res_289_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_46__boxed_288_, v_h__1_284_, v_h__2_285_, v_h__3_286_, v_h__4_287_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(
    mut v_motive_290_: *mut LeanObject,
    mut v_x_291_: u8,
    mut v_h__1_292_: *mut LeanObject,
    mut v_h__2_293_: *mut LeanObject,
    mut v_h__3_294_: *mut LeanObject,
    mut v_h__4_295_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_291_ {
        0 => {
            let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_295_);
            lean_dec(v_h__3_294_);
            lean_dec(v_h__2_293_);
            v___x_296_ = lean_box(0);
            v___x_297_ = lean_apply_1(v_h__1_292_, v___x_296_);
            return v___x_297_;
        }
        1 => {
            let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_295_);
            lean_dec(v_h__3_294_);
            lean_dec(v_h__1_292_);
            v___x_298_ = lean_box(0);
            v___x_299_ = lean_apply_1(v_h__2_293_, v___x_298_);
            return v___x_299_;
        }
        2 => {
            let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_295_);
            lean_dec(v_h__2_293_);
            lean_dec(v_h__1_292_);
            v___x_300_ = lean_box(0);
            v___x_301_ = lean_apply_1(v_h__3_294_, v___x_300_);
            return v___x_301_;
        }
        _ => {
            let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_294_);
            lean_dec(v_h__2_293_);
            lean_dec(v_h__1_292_);
            v___x_302_ = lean_box(0);
            v___x_303_ = lean_apply_1(v_h__4_295_, v___x_302_);
            return v___x_303_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(
    mut v_motive_304_: *mut LeanObject,
    mut v_x_305_: *mut LeanObject,
    mut v_h__1_306_: *mut LeanObject,
    mut v_h__2_307_: *mut LeanObject,
    mut v_h__3_308_: *mut LeanObject,
    mut v_h__4_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_65__boxed_310_: u8 = 0;
    let mut v_res_311_: *mut LeanObject = core::ptr::null_mut();
    v_x_65__boxed_310_ = (lean_unbox(v_x_305_) as u8);
    v_res_311_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(v_motive_304_, v_x_65__boxed_310_, v_h__1_306_, v_h__2_307_, v_h__3_308_, v_h__4_309_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(
    mut v_x_312_: *mut LeanObject,
    mut v_h__1_313_: *mut LeanObject,
    mut v_h__2_314_: *mut LeanObject,
    mut v_h__3_315_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_312_) == 0 {
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_314_);
        lean_dec(v_h__1_313_);
        v___x_316_ = lean_box(0);
        v___x_317_ = lean_apply_1(v_h__3_315_, v___x_316_);
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_315_);
        v_val_318_ = lean_ctor_get(v_x_312_, 0);
        lean_inc(v_val_318_);
        lean_dec_ref_known(v_x_312_, 1);
        if lean_obj_tag(v_val_318_) == 0 {
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_313_);
            v___x_319_ = lean_box(0);
            v___x_320_ = lean_apply_1(v_h__2_314_, v___x_319_);
            return v___x_320_;
        } else {
            let mut v_val_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_314_);
            v_val_321_ = lean_ctor_get(v_val_318_, 0);
            lean_inc(v_val_321_);
            lean_dec_ref_known(v_val_318_, 1);
            v___x_322_ = lean_apply_1(v_h__1_313_, v_val_321_);
            return v___x_322_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(
    mut v_n_323_: *mut LeanObject,
    mut v_motive_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
    mut v_h__1_326_: *mut LeanObject,
    mut v_h__2_327_: *mut LeanObject,
    mut v_h__3_328_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_325_) == 0 {
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_327_);
        lean_dec(v_h__1_326_);
        v___x_329_ = lean_box(0);
        v___x_330_ = lean_apply_1(v_h__3_328_, v___x_329_);
        return v___x_330_;
    } else {
        let mut v_val_331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_328_);
        v_val_331_ = lean_ctor_get(v_x_325_, 0);
        lean_inc(v_val_331_);
        lean_dec_ref_known(v_x_325_, 1);
        if lean_obj_tag(v_val_331_) == 0 {
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_326_);
            v___x_332_ = lean_box(0);
            v___x_333_ = lean_apply_1(v_h__2_327_, v___x_332_);
            return v___x_333_;
        } else {
            let mut v_val_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_327_);
            v_val_334_ = lean_ctor_get(v_val_331_, 0);
            lean_inc(v_val_334_);
            lean_dec_ref_known(v_val_331_, 1);
            v___x_335_ = lean_apply_1(v_h__1_326_, v_val_334_);
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(
    mut v_n_336_: *mut LeanObject,
    mut v_motive_337_: *mut LeanObject,
    mut v_x_338_: *mut LeanObject,
    mut v_h__1_339_: *mut LeanObject,
    mut v_h__2_340_: *mut LeanObject,
    mut v_h__3_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_342_: *mut LeanObject = core::ptr::null_mut();
    v_res_342_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_336_, v_motive_337_, v_x_338_, v_h__1_339_, v_h__2_340_, v_h__3_341_);
    lean_dec(v_n_336_);
    return v_res_342_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(
    mut v_x_343_: *mut LeanObject,
    mut v_h__1_344_: *mut LeanObject,
    mut v_h__2_345_: *mut LeanObject,
    mut v_h__3_346_: *mut LeanObject,
    mut v_h__4_347_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_343_) {
        0 => {
            let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_347_);
            lean_dec(v_h__3_346_);
            lean_dec(v_h__2_345_);
            v___x_348_ = lean_box(0);
            v___x_349_ = lean_apply_1(v_h__1_344_, v___x_348_);
            return v___x_349_;
        }
        1 => {
            let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_347_);
            lean_dec(v_h__3_346_);
            lean_dec(v_h__1_344_);
            v___x_350_ = lean_box(0);
            v___x_351_ = lean_apply_1(v_h__2_345_, v___x_350_);
            return v___x_351_;
        }
        2 => {
            let mut v_l_352_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_353_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_354_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_347_);
            lean_dec(v_h__2_345_);
            lean_dec(v_h__1_344_);
            v_l_352_ = lean_ctor_get(v_x_343_, 0);
            lean_inc_ref(v_l_352_);
            lean_dec_ref_known(v_x_343_, 1);
            v_fst_353_ = lean_ctor_get(v_l_352_, 0);
            lean_inc(v_fst_353_);
            v_snd_354_ = lean_ctor_get(v_l_352_, 1);
            lean_inc(v_snd_354_);
            lean_dec_ref(v_l_352_);
            v___x_355_ = lean_apply_2(v_h__3_346_, v_fst_353_, v_snd_354_);
            return v___x_355_;
        }
        _ => {
            let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_346_);
            lean_dec(v_h__2_345_);
            lean_dec(v_h__1_344_);
            v___x_356_ = lean_box(0);
            v___x_357_ = lean_apply_1(v_h__4_347_, v___x_356_);
            return v___x_357_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(
    mut v_n_358_: *mut LeanObject,
    mut v_motive_359_: *mut LeanObject,
    mut v_x_360_: *mut LeanObject,
    mut v_h__1_361_: *mut LeanObject,
    mut v_h__2_362_: *mut LeanObject,
    mut v_h__3_363_: *mut LeanObject,
    mut v_h__4_364_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_360_) {
        0 => {
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_364_);
            lean_dec(v_h__3_363_);
            lean_dec(v_h__2_362_);
            v___x_365_ = lean_box(0);
            v___x_366_ = lean_apply_1(v_h__1_361_, v___x_365_);
            return v___x_366_;
        }
        1 => {
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_364_);
            lean_dec(v_h__3_363_);
            lean_dec(v_h__1_361_);
            v___x_367_ = lean_box(0);
            v___x_368_ = lean_apply_1(v_h__2_362_, v___x_367_);
            return v___x_368_;
        }
        2 => {
            let mut v_l_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_370_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_364_);
            lean_dec(v_h__2_362_);
            lean_dec(v_h__1_361_);
            v_l_369_ = lean_ctor_get(v_x_360_, 0);
            lean_inc_ref(v_l_369_);
            lean_dec_ref_known(v_x_360_, 1);
            v_fst_370_ = lean_ctor_get(v_l_369_, 0);
            lean_inc(v_fst_370_);
            v_snd_371_ = lean_ctor_get(v_l_369_, 1);
            lean_inc(v_snd_371_);
            lean_dec_ref(v_l_369_);
            v___x_372_ = lean_apply_2(v_h__3_363_, v_fst_370_, v_snd_371_);
            return v___x_372_;
        }
        _ => {
            let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_363_);
            lean_dec(v_h__2_362_);
            lean_dec(v_h__1_361_);
            v___x_373_ = lean_box(0);
            v___x_374_ = lean_apply_1(v_h__4_364_, v___x_373_);
            return v___x_374_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(
    mut v_n_375_: *mut LeanObject,
    mut v_motive_376_: *mut LeanObject,
    mut v_x_377_: *mut LeanObject,
    mut v_h__1_378_: *mut LeanObject,
    mut v_h__2_379_: *mut LeanObject,
    mut v_h__3_380_: *mut LeanObject,
    mut v_h__4_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_382_: *mut LeanObject = core::ptr::null_mut();
    v_res_382_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_375_, v_motive_376_, v_x_377_, v_h__1_378_, v_h__2_379_, v_h__3_380_, v_h__4_381_);
    lean_dec(v_n_375_);
    return v_res_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
}
