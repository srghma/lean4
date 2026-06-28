// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.TakeWhile
// Imports: Std.Data.Iterators.Combinators.TakeWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile Std.Data.Iterators.Lemmas.Consumers Init.Data.List.TakeDrop Init.Data.List.ToArray Init.Data.Option.Lemmas Init.Omega
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::Iterators::Combinators::TakeWhile::{
    initialize_Std_Data_Iterators_Combinators_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::TakeWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::{
    initialize_Std_Data_Iterators_Lemmas_Consumers,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___redArg(
    mut v_x_223_: *mut LeanObject,
    mut v_h__1_224_: *mut LeanObject,
    mut v_h__2_225_: *mut LeanObject,
    mut v_h__3_226_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_223_) {
        0 => {
            let mut v_it_227_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_226_);
            lean_dec(v_h__2_225_);
            v_it_227_ = lean_ctor_get(v_x_223_, 0);
            lean_inc(v_it_227_);
            v_out_228_ = lean_ctor_get(v_x_223_, 1);
            lean_inc(v_out_228_);
            lean_dec_ref_known(v_x_223_, 2);
            v___x_229_ = lean_apply_3(v_h__1_224_, v_it_227_, v_out_228_, lean_box(0));
            return v___x_229_;
        }
        1 => {
            let mut v_it_230_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_226_);
            lean_dec(v_h__1_224_);
            v_it_230_ = lean_ctor_get(v_x_223_, 0);
            lean_inc(v_it_230_);
            lean_dec_ref_known(v_x_223_, 1);
            v___x_231_ = lean_apply_2(v_h__2_225_, v_it_230_, lean_box(0));
            return v___x_231_;
        }
        _ => {
            let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_225_);
            lean_dec(v_h__1_224_);
            v___x_232_ = lean_apply_1(v_h__3_226_, lean_box(0));
            return v___x_232_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_233_: *mut LeanObject,
    mut v_m_234_: *mut LeanObject,
    mut v_00_u03b2_235_: *mut LeanObject,
    mut v_inst_236_: *mut LeanObject,
    mut v_it_237_: *mut LeanObject,
    mut v_motive_238_: *mut LeanObject,
    mut v_x_239_: *mut LeanObject,
    mut v_h__1_240_: *mut LeanObject,
    mut v_h__2_241_: *mut LeanObject,
    mut v_h__3_242_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_239_) {
        0 => {
            let mut v_it_243_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_242_);
            lean_dec(v_h__2_241_);
            v_it_243_ = lean_ctor_get(v_x_239_, 0);
            lean_inc(v_it_243_);
            v_out_244_ = lean_ctor_get(v_x_239_, 1);
            lean_inc(v_out_244_);
            lean_dec_ref_known(v_x_239_, 2);
            v___x_245_ = lean_apply_3(v_h__1_240_, v_it_243_, v_out_244_, lean_box(0));
            return v___x_245_;
        }
        1 => {
            let mut v_it_246_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_242_);
            lean_dec(v_h__1_240_);
            v_it_246_ = lean_ctor_get(v_x_239_, 0);
            lean_inc(v_it_246_);
            lean_dec_ref_known(v_x_239_, 1);
            v___x_247_ = lean_apply_2(v_h__2_241_, v_it_246_, lean_box(0));
            return v___x_247_;
        }
        _ => {
            let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_241_);
            lean_dec(v_h__1_240_);
            v___x_248_ = lean_apply_1(v_h__3_242_, lean_box(0));
            return v___x_248_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_249_: *mut LeanObject,
    mut v_m_250_: *mut LeanObject,
    mut v_00_u03b2_251_: *mut LeanObject,
    mut v_inst_252_: *mut LeanObject,
    mut v_it_253_: *mut LeanObject,
    mut v_motive_254_: *mut LeanObject,
    mut v_x_255_: *mut LeanObject,
    mut v_h__1_256_: *mut LeanObject,
    mut v_h__2_257_: *mut LeanObject,
    mut v_h__3_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_259_: *mut LeanObject = core::ptr::null_mut();
    v_res_259_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(v_00_u03b1_249_, v_m_250_, v_00_u03b2_251_, v_inst_252_, v_it_253_, v_motive_254_, v_x_255_, v_h__1_256_, v_h__2_257_, v_h__3_258_);
    lean_dec(v_it_253_);
    lean_dec(v_inst_252_);
    return v_res_259_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(
    mut v_x_260_: u8,
    mut v_h__1_261_: *mut LeanObject,
    mut v_h__2_262_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_260_ == 0 {
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_261_);
        v___x_263_ = lean_apply_1(v_h__2_262_, lean_box(0));
        return v___x_263_;
    } else {
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_262_);
        v___x_264_ = lean_apply_1(v_h__1_261_, lean_box(0));
        return v___x_264_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_268_: u8 = 0;
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_268_ = (lean_unbox(v_x_265_) as u8);
    v_res_269_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_268_, v_h__1_266_, v_h__2_267_);
    return v_res_269_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(
    mut v_motive_270_: *mut LeanObject,
    mut v_x_271_: u8,
    mut v_h__1_272_: *mut LeanObject,
    mut v_h__2_273_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_271_ == 0 {
        let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_272_);
        v___x_274_ = lean_apply_1(v_h__2_273_, lean_box(0));
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_273_);
        v___x_275_ = lean_apply_1(v_h__1_272_, lean_box(0));
        return v___x_275_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___boxed(
    mut v_motive_276_: *mut LeanObject,
    mut v_x_277_: *mut LeanObject,
    mut v_h__1_278_: *mut LeanObject,
    mut v_h__2_279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_280_: u8 = 0;
    let mut v_res_281_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_280_ = (lean_unbox(v_x_277_) as u8);
    v_res_281_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(v_motive_276_, v_x_33__boxed_280_, v_h__1_278_, v_h__2_279_);
    return v_res_281_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___redArg(
    mut v_x_282_: *mut LeanObject,
    mut v_h__1_283_: *mut LeanObject,
    mut v_h__2_284_: *mut LeanObject,
    mut v_h__3_285_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_282_) {
        0 => {
            let mut v_it_286_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_287_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_285_);
            lean_dec(v_h__2_284_);
            v_it_286_ = lean_ctor_get(v_x_282_, 0);
            lean_inc(v_it_286_);
            v_out_287_ = lean_ctor_get(v_x_282_, 1);
            lean_inc(v_out_287_);
            lean_dec_ref_known(v_x_282_, 2);
            v___x_288_ = lean_apply_3(v_h__1_283_, v_it_286_, v_out_287_, lean_box(0));
            return v___x_288_;
        }
        1 => {
            let mut v_it_289_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_285_);
            lean_dec(v_h__1_283_);
            v_it_289_ = lean_ctor_get(v_x_282_, 0);
            lean_inc(v_it_289_);
            lean_dec_ref_known(v_x_282_, 1);
            v___x_290_ = lean_apply_2(v_h__2_284_, v_it_289_, lean_box(0));
            return v___x_290_;
        }
        _ => {
            let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_284_);
            lean_dec(v_h__1_283_);
            v___x_291_ = lean_apply_1(v_h__3_285_, lean_box(0));
            return v___x_291_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_00_u03b2_293_: *mut LeanObject,
    mut v_inst_294_: *mut LeanObject,
    mut v_it_295_: *mut LeanObject,
    mut v_motive_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
    mut v_h__1_298_: *mut LeanObject,
    mut v_h__2_299_: *mut LeanObject,
    mut v_h__3_300_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_297_) {
        0 => {
            let mut v_it_301_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_300_);
            lean_dec(v_h__2_299_);
            v_it_301_ = lean_ctor_get(v_x_297_, 0);
            lean_inc(v_it_301_);
            v_out_302_ = lean_ctor_get(v_x_297_, 1);
            lean_inc(v_out_302_);
            lean_dec_ref_known(v_x_297_, 2);
            v___x_303_ = lean_apply_3(v_h__1_298_, v_it_301_, v_out_302_, lean_box(0));
            return v___x_303_;
        }
        1 => {
            let mut v_it_304_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_300_);
            lean_dec(v_h__1_298_);
            v_it_304_ = lean_ctor_get(v_x_297_, 0);
            lean_inc(v_it_304_);
            lean_dec_ref_known(v_x_297_, 1);
            v___x_305_ = lean_apply_2(v_h__2_299_, v_it_304_, lean_box(0));
            return v___x_305_;
        }
        _ => {
            let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_299_);
            lean_dec(v_h__1_298_);
            v___x_306_ = lean_apply_1(v_h__3_300_, lean_box(0));
            return v___x_306_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter___boxed(
    mut v_00_u03b1_307_: *mut LeanObject,
    mut v_00_u03b2_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
    mut v_it_310_: *mut LeanObject,
    mut v_motive_311_: *mut LeanObject,
    mut v_x_312_: *mut LeanObject,
    mut v_h__1_313_: *mut LeanObject,
    mut v_h__2_314_: *mut LeanObject,
    mut v_h__3_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__3_splitter(v_00_u03b1_307_, v_00_u03b2_308_, v_inst_309_, v_it_310_, v_motive_311_, v_x_312_, v_h__1_313_, v_h__2_314_, v_h__3_315_);
    lean_dec(v_it_310_);
    lean_dec(v_inst_309_);
    return v_res_316_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(
    mut v_x_317_: u8,
    mut v_h__1_318_: *mut LeanObject,
    mut v_h__2_319_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_317_ == 0 {
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_318_);
        v___x_320_ = lean_apply_1(v_h__2_319_, lean_box(0));
        return v___x_320_;
    } else {
        let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_319_);
        v___x_321_ = lean_apply_1(v_h__1_318_, lean_box(0));
        return v___x_321_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_322_: *mut LeanObject,
    mut v_h__1_323_: *mut LeanObject,
    mut v_h__2_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_325_: u8 = 0;
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_325_ = (lean_unbox(v_x_322_) as u8);
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_325_, v_h__1_323_, v_h__2_324_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(
    mut v_motive_327_: *mut LeanObject,
    mut v_x_328_: u8,
    mut v_h__1_329_: *mut LeanObject,
    mut v_h__2_330_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_328_ == 0 {
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_329_);
        v___x_331_ = lean_apply_1(v_h__2_330_, lean_box(0));
        return v___x_331_;
    } else {
        let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_330_);
        v___x_332_ = lean_apply_1(v_h__1_329_, lean_box(0));
        return v___x_332_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter___boxed(
    mut v_motive_333_: *mut LeanObject,
    mut v_x_334_: *mut LeanObject,
    mut v_h__1_335_: *mut LeanObject,
    mut v_h__2_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_337_: u8 = 0;
    let mut v_res_338_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_337_ = (lean_unbox(v_x_334_) as u8);
    v_res_338_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_step__takeWhile_match__1_splitter(v_motive_333_, v_x_33__boxed_337_, v_h__1_335_, v_h__2_336_);
    return v_res_338_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter___redArg(
    mut v_x_339_: *mut LeanObject,
    mut v_h__1_340_: *mut LeanObject,
    mut v_h__2_341_: *mut LeanObject,
    mut v_h__3_342_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_339_) {
        0 => {
            let mut v_it_343_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_342_);
            lean_dec(v_h__2_341_);
            v_it_343_ = lean_ctor_get(v_x_339_, 0);
            lean_inc(v_it_343_);
            v_out_344_ = lean_ctor_get(v_x_339_, 1);
            lean_inc(v_out_344_);
            lean_dec_ref_known(v_x_339_, 2);
            v___x_345_ = lean_apply_2(v_h__1_340_, v_it_343_, v_out_344_);
            return v___x_345_;
        }
        1 => {
            let mut v_it_346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_342_);
            lean_dec(v_h__1_340_);
            v_it_346_ = lean_ctor_get(v_x_339_, 0);
            lean_inc(v_it_346_);
            lean_dec_ref_known(v_x_339_, 1);
            v___x_347_ = lean_apply_1(v_h__2_341_, v_it_346_);
            return v___x_347_;
        }
        _ => {
            let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_341_);
            lean_dec(v_h__1_340_);
            v___x_348_ = lean_box(0);
            v___x_349_ = lean_apply_1(v_h__3_342_, v___x_348_);
            return v___x_349_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__3_splitter(
    mut v_00_u03b1_350_: *mut LeanObject,
    mut v_00_u03b2_351_: *mut LeanObject,
    mut v_motive_352_: *mut LeanObject,
    mut v_x_353_: *mut LeanObject,
    mut v_h__1_354_: *mut LeanObject,
    mut v_h__2_355_: *mut LeanObject,
    mut v_h__3_356_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_353_) {
        0 => {
            let mut v_it_357_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_356_);
            lean_dec(v_h__2_355_);
            v_it_357_ = lean_ctor_get(v_x_353_, 0);
            lean_inc(v_it_357_);
            v_out_358_ = lean_ctor_get(v_x_353_, 1);
            lean_inc(v_out_358_);
            lean_dec_ref_known(v_x_353_, 2);
            v___x_359_ = lean_apply_2(v_h__1_354_, v_it_357_, v_out_358_);
            return v___x_359_;
        }
        1 => {
            let mut v_it_360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_356_);
            lean_dec(v_h__1_354_);
            v_it_360_ = lean_ctor_get(v_x_353_, 0);
            lean_inc(v_it_360_);
            lean_dec_ref_known(v_x_353_, 1);
            v___x_361_ = lean_apply_1(v_h__2_355_, v_it_360_);
            return v___x_361_;
        }
        _ => {
            let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_355_);
            lean_dec(v_h__1_354_);
            v___x_362_ = lean_box(0);
            v___x_363_ = lean_apply_1(v_h__3_356_, v___x_362_);
            return v___x_363_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(
    mut v_x_364_: u8,
    mut v_h__1_365_: *mut LeanObject,
    mut v_h__2_366_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_364_ == 0 {
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_365_);
        v___x_367_ = lean_box(0);
        v___x_368_ = lean_apply_1(v_h__2_366_, v___x_367_);
        return v___x_368_;
    } else {
        let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_366_);
        v___x_369_ = lean_box(0);
        v___x_370_ = lean_apply_1(v_h__1_365_, v___x_369_);
        return v___x_370_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_371_: *mut LeanObject,
    mut v_h__1_372_: *mut LeanObject,
    mut v_h__2_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_374_: u8 = 0;
    let mut v_res_375_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_374_ = (lean_unbox(v_x_371_) as u8);
    v_res_375_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_374_, v_h__1_372_, v_h__2_373_);
    return v_res_375_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(
    mut v_motive_376_: *mut LeanObject,
    mut v_x_377_: u8,
    mut v_h__1_378_: *mut LeanObject,
    mut v_h__2_379_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_377_ == 0 {
        let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_378_);
        v___x_380_ = lean_box(0);
        v___x_381_ = lean_apply_1(v_h__2_379_, v___x_380_);
        return v___x_381_;
    } else {
        let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_379_);
        v___x_382_ = lean_box(0);
        v___x_383_ = lean_apply_1(v_h__1_378_, v___x_382_);
        return v___x_383_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter___boxed(
    mut v_motive_384_: *mut LeanObject,
    mut v_x_385_: *mut LeanObject,
    mut v_h__1_386_: *mut LeanObject,
    mut v_h__2_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_388_: u8 = 0;
    let mut v_res_389_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_388_ = (lean_unbox(v_x_385_) as u8);
    v_res_389_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_val__step__takeWhile_match__1_splitter(v_motive_384_, v_x_37__boxed_388_, v_h__1_386_, v_h__2_387_);
    return v_res_389_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(
    mut v_x_390_: *mut LeanObject,
    mut v_h__1_391_: *mut LeanObject,
    mut v_h__2_392_: *mut LeanObject,
    mut v_h__3_393_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_390_) {
        0 => {
            let mut v_it_394_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_393_);
            lean_dec(v_h__2_392_);
            v_it_394_ = lean_ctor_get(v_x_390_, 0);
            lean_inc(v_it_394_);
            v_out_395_ = lean_ctor_get(v_x_390_, 1);
            lean_inc(v_out_395_);
            lean_dec_ref_known(v_x_390_, 2);
            v___x_396_ = lean_apply_2(v_h__1_391_, v_it_394_, v_out_395_);
            return v___x_396_;
        }
        1 => {
            let mut v_it_397_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_393_);
            lean_dec(v_h__1_391_);
            v_it_397_ = lean_ctor_get(v_x_390_, 0);
            lean_inc(v_it_397_);
            lean_dec_ref_known(v_x_390_, 1);
            v___x_398_ = lean_apply_1(v_h__2_392_, v_it_397_);
            return v___x_398_;
        }
        _ => {
            let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_392_);
            lean_dec(v_h__1_391_);
            v___x_399_ = lean_box(0);
            v___x_400_ = lean_apply_1(v_h__3_393_, v___x_399_);
            return v___x_400_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(
    mut v_00_u03b1_401_: *mut LeanObject,
    mut v_00_u03b2_402_: *mut LeanObject,
    mut v_motive_403_: *mut LeanObject,
    mut v_x_404_: *mut LeanObject,
    mut v_h__1_405_: *mut LeanObject,
    mut v_h__2_406_: *mut LeanObject,
    mut v_h__3_407_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_404_) {
        0 => {
            let mut v_it_408_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_409_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_407_);
            lean_dec(v_h__2_406_);
            v_it_408_ = lean_ctor_get(v_x_404_, 0);
            lean_inc(v_it_408_);
            v_out_409_ = lean_ctor_get(v_x_404_, 1);
            lean_inc(v_out_409_);
            lean_dec_ref_known(v_x_404_, 2);
            v___x_410_ = lean_apply_2(v_h__1_405_, v_it_408_, v_out_409_);
            return v___x_410_;
        }
        1 => {
            let mut v_it_411_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_407_);
            lean_dec(v_h__1_405_);
            v_it_411_ = lean_ctor_get(v_x_404_, 0);
            lean_inc(v_it_411_);
            lean_dec_ref_known(v_x_404_, 1);
            v___x_412_ = lean_apply_1(v_h__2_406_, v_it_411_);
            return v___x_412_;
        }
        _ => {
            let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_406_);
            lean_dec(v_h__1_405_);
            v___x_413_ = lean_box(0);
            v___x_414_ = lean_apply_1(v_h__3_407_, v___x_413_);
            return v___x_414_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_415_: *mut LeanObject,
    mut v_h__1_416_: *mut LeanObject,
    mut v_h__2_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_419_: u8 = 0;
    v_zero_418_ = lean_unsigned_to_nat(0);
    v_isZero_419_ = lean_nat_dec_eq(v_n_415_, v_zero_418_);
    if v_isZero_419_ == 1 {
        let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_417_);
        v___x_420_ = lean_box(0);
        v___x_421_ = lean_apply_1(v_h__1_416_, v___x_420_);
        return v___x_421_;
    } else {
        let mut v_one_422_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_416_);
        v_one_422_ = lean_unsigned_to_nat(1);
        v_n_423_ = lean_nat_sub(v_n_415_, v_one_422_);
        v___x_424_ = lean_apply_1(v_h__2_417_, v_n_423_);
        return v___x_424_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_425_: *mut LeanObject,
    mut v_h__1_426_: *mut LeanObject,
    mut v_h__2_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_428_: *mut LeanObject = core::ptr::null_mut();
    v_res_428_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_425_, v_h__1_426_, v_h__2_427_);
    lean_dec(v_n_425_);
    return v_res_428_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_429_: *mut LeanObject,
    mut v_n_430_: *mut LeanObject,
    mut v_h__1_431_: *mut LeanObject,
    mut v_h__2_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_434_: u8 = 0;
    v_zero_433_ = lean_unsigned_to_nat(0);
    v_isZero_434_ = lean_nat_dec_eq(v_n_430_, v_zero_433_);
    if v_isZero_434_ == 1 {
        let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_432_);
        v___x_435_ = lean_box(0);
        v___x_436_ = lean_apply_1(v_h__1_431_, v___x_435_);
        return v___x_436_;
    } else {
        let mut v_one_437_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_431_);
        v_one_437_ = lean_unsigned_to_nat(1);
        v_n_438_ = lean_nat_sub(v_n_430_, v_one_437_);
        v___x_439_ = lean_apply_1(v_h__2_432_, v_n_438_);
        return v___x_439_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_440_: *mut LeanObject,
    mut v_n_441_: *mut LeanObject,
    mut v_h__1_442_: *mut LeanObject,
    mut v_h__2_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_444_: *mut LeanObject = core::ptr::null_mut();
    v_res_444_ = l___private_Std_Data_Iterators_Lemmas_Combinators_TakeWhile_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_440_, v_n_441_, v_h__1_442_, v_h__2_443_);
    lean_dec(v_n_441_);
    return v_res_444_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
}
