// Lean compiler output
// Module: Init.PropLemmas
// Imports: Init.NotationExtra
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_Or_by__cases___redArg(
    mut v_inst_211_: u8,
    mut v_h_u2081_212_: *mut LeanObject,
    mut v_h_u2082_213_: *mut LeanObject,
) -> *mut LeanObject {
    if v_inst_211_ == 0 {
        let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h_u2081_212_);
        v___x_214_ = lean_apply_1(v_h_u2082_213_, lean_box(0));
        return v___x_214_;
    } else {
        let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h_u2082_213_);
        v___x_215_ = lean_apply_1(v_h_u2081_212_, lean_box(0));
        return v___x_215_;
    }
}
pub unsafe fn l_Or_by__cases___redArg___boxed(
    mut v_inst_216_: *mut LeanObject,
    mut v_h_u2081_217_: *mut LeanObject,
    mut v_h_u2082_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_219_: u8 = 0;
    let mut v_res_220_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_219_ = (lean_unbox(v_inst_216_) as u8);
    v_res_220_ = l_Or_by__cases___redArg(v_inst_8__boxed_219_, v_h_u2081_217_, v_h_u2082_218_);
    return v_res_220_;
}
pub unsafe fn l_Or_by__cases(
    mut v_p_221_: *mut LeanObject,
    mut v_q_222_: *mut LeanObject,
    mut v_inst_223_: u8,
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_h_225_: *mut LeanObject,
    mut v_h_u2081_226_: *mut LeanObject,
    mut v_h_u2082_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_228_ = l_Or_by__cases___redArg(v_inst_223_, v_h_u2081_226_, v_h_u2082_227_);
    return v___x_228_;
}
pub unsafe fn l_Or_by__cases___boxed(
    mut v_p_229_: *mut LeanObject,
    mut v_q_230_: *mut LeanObject,
    mut v_inst_231_: *mut LeanObject,
    mut v_00_u03b1_232_: *mut LeanObject,
    mut v_h_233_: *mut LeanObject,
    mut v_h_u2081_234_: *mut LeanObject,
    mut v_h_u2082_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_15__boxed_236_: u8 = 0;
    let mut v_res_237_: *mut LeanObject = core::ptr::null_mut();
    v_inst_15__boxed_236_ = (lean_unbox(v_inst_231_) as u8);
    v_res_237_ = l_Or_by__cases(
        v_p_229_,
        v_q_230_,
        v_inst_15__boxed_236_,
        v_00_u03b1_232_,
        v_h_233_,
        v_h_u2081_234_,
        v_h_u2082_235_,
    );
    return v_res_237_;
}
pub unsafe fn l_Or_by__cases_x27___redArg(
    mut v_inst_238_: u8,
    mut v_h_u2081_239_: *mut LeanObject,
    mut v_h_u2082_240_: *mut LeanObject,
) -> *mut LeanObject {
    if v_inst_238_ == 0 {
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h_u2082_240_);
        v___x_241_ = lean_apply_1(v_h_u2081_239_, lean_box(0));
        return v___x_241_;
    } else {
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h_u2081_239_);
        v___x_242_ = lean_apply_1(v_h_u2082_240_, lean_box(0));
        return v___x_242_;
    }
}
pub unsafe fn l_Or_by__cases_x27___redArg___boxed(
    mut v_inst_243_: *mut LeanObject,
    mut v_h_u2081_244_: *mut LeanObject,
    mut v_h_u2082_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_246_: u8 = 0;
    let mut v_res_247_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_246_ = (lean_unbox(v_inst_243_) as u8);
    v_res_247_ = l_Or_by__cases_x27___redArg(v_inst_8__boxed_246_, v_h_u2081_244_, v_h_u2082_245_);
    return v_res_247_;
}
pub unsafe fn l_Or_by__cases_x27(
    mut v_q_248_: *mut LeanObject,
    mut v_p_249_: *mut LeanObject,
    mut v_inst_250_: u8,
    mut v_00_u03b1_251_: *mut LeanObject,
    mut v_h_252_: *mut LeanObject,
    mut v_h_u2081_253_: *mut LeanObject,
    mut v_h_u2082_254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Or_by__cases_x27___redArg(v_inst_250_, v_h_u2081_253_, v_h_u2082_254_);
    return v___x_255_;
}
pub unsafe fn l_Or_by__cases_x27___boxed(
    mut v_q_256_: *mut LeanObject,
    mut v_p_257_: *mut LeanObject,
    mut v_inst_258_: *mut LeanObject,
    mut v_00_u03b1_259_: *mut LeanObject,
    mut v_h_260_: *mut LeanObject,
    mut v_h_u2081_261_: *mut LeanObject,
    mut v_h_u2082_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_15__boxed_263_: u8 = 0;
    let mut v_res_264_: *mut LeanObject = core::ptr::null_mut();
    v_inst_15__boxed_263_ = (lean_unbox(v_inst_258_) as u8);
    v_res_264_ = l_Or_by__cases_x27(
        v_q_256_,
        v_p_257_,
        v_inst_15__boxed_263_,
        v_00_u03b1_259_,
        v_h_260_,
        v_h_u2081_261_,
        v_h_u2082_262_,
    );
    return v_res_264_;
}
pub unsafe fn l_exists__prop__decidable___redArg(
    mut v_inst_265_: u8,
    mut v_inst_266_: *mut LeanObject,
) -> u8 {
    if v_inst_265_ == 0 {
        lean_dec_ref(v_inst_266_);
        return v_inst_265_;
    } else {
        let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_268_: u8 = 0;
        v___x_267_ = lean_apply_1(v_inst_266_, lean_box(0));
        v___x_268_ = (lean_unbox(v___x_267_) as u8);
        return v___x_268_;
    }
}
pub unsafe fn l_exists__prop__decidable___redArg___boxed(
    mut v_inst_269_: *mut LeanObject,
    mut v_inst_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_14__boxed_271_: u8 = 0;
    let mut v_res_272_: u8 = 0;
    let mut v_r_273_: *mut LeanObject = core::ptr::null_mut();
    v_inst_14__boxed_271_ = (lean_unbox(v_inst_269_) as u8);
    v_res_272_ = l_exists__prop__decidable___redArg(v_inst_14__boxed_271_, v_inst_270_);
    v_r_273_ = lean_box((v_res_272_) as usize);
    return v_r_273_;
}
pub unsafe fn l_exists__prop__decidable(
    mut v_p_274_: *mut LeanObject,
    mut v_P_275_: *mut LeanObject,
    mut v_inst_276_: u8,
    mut v_inst_277_: *mut LeanObject,
) -> u8 {
    if v_inst_276_ == 0 {
        lean_dec_ref(v_inst_277_);
        return v_inst_276_;
    } else {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: u8 = 0;
        v___x_278_ = lean_apply_1(v_inst_277_, lean_box(0));
        v___x_279_ = (lean_unbox(v___x_278_) as u8);
        return v___x_279_;
    }
}
pub unsafe fn l_exists__prop__decidable___boxed(
    mut v_p_280_: *mut LeanObject,
    mut v_P_281_: *mut LeanObject,
    mut v_inst_282_: *mut LeanObject,
    mut v_inst_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_24__boxed_284_: u8 = 0;
    let mut v_res_285_: u8 = 0;
    let mut v_r_286_: *mut LeanObject = core::ptr::null_mut();
    v_inst_24__boxed_284_ = (lean_unbox(v_inst_282_) as u8);
    v_res_285_ = l_exists__prop__decidable(v_p_280_, v_P_281_, v_inst_24__boxed_284_, v_inst_283_);
    v_r_286_ = lean_box((v_res_285_) as usize);
    return v_r_286_;
}
pub unsafe fn l_forall__prop__decidable___redArg(
    mut v_inst_287_: u8,
    mut v_inst_288_: *mut LeanObject,
) -> u8 {
    if v_inst_287_ == 0 {
        let mut v___x_289_: u8 = 0;
        lean_dec_ref(v_inst_288_);
        v___x_289_ = 1;
        return v___x_289_;
    } else {
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: u8 = 0;
        v___x_290_ = lean_apply_1(v_inst_288_, lean_box(0));
        v___x_291_ = (lean_unbox(v___x_290_) as u8);
        return v___x_291_;
    }
}
pub unsafe fn l_forall__prop__decidable___redArg___boxed(
    mut v_inst_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_15__boxed_294_: u8 = 0;
    let mut v_res_295_: u8 = 0;
    let mut v_r_296_: *mut LeanObject = core::ptr::null_mut();
    v_inst_15__boxed_294_ = (lean_unbox(v_inst_292_) as u8);
    v_res_295_ = l_forall__prop__decidable___redArg(v_inst_15__boxed_294_, v_inst_293_);
    v_r_296_ = lean_box((v_res_295_) as usize);
    return v_r_296_;
}
pub unsafe fn l_forall__prop__decidable(
    mut v_p_297_: *mut LeanObject,
    mut v_P_298_: *mut LeanObject,
    mut v_inst_299_: u8,
    mut v_inst_300_: *mut LeanObject,
) -> u8 {
    if v_inst_299_ == 0 {
        let mut v___x_301_: u8 = 0;
        lean_dec_ref(v_inst_300_);
        v___x_301_ = 1;
        return v___x_301_;
    } else {
        let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_303_: u8 = 0;
        v___x_302_ = lean_apply_1(v_inst_300_, lean_box(0));
        v___x_303_ = (lean_unbox(v___x_302_) as u8);
        return v___x_303_;
    }
}
pub unsafe fn l_forall__prop__decidable___boxed(
    mut v_p_304_: *mut LeanObject,
    mut v_P_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_27__boxed_308_: u8 = 0;
    let mut v_res_309_: u8 = 0;
    let mut v_r_310_: *mut LeanObject = core::ptr::null_mut();
    v_inst_27__boxed_308_ = (lean_unbox(v_inst_306_) as u8);
    v_res_309_ = l_forall__prop__decidable(v_p_304_, v_P_305_, v_inst_27__boxed_308_, v_inst_307_);
    v_r_310_ = lean_box((v_res_309_) as usize);
    return v_r_310_;
}
pub unsafe fn l_decidable__of__iff___redArg(mut v_inst_311_: u8) -> u8 {
    return v_inst_311_;
}
pub unsafe fn l_decidable__of__iff___redArg___boxed(
    mut v_inst_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_313_: u8 = 0;
    let mut v_res_314_: u8 = 0;
    let mut v_r_315_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_313_ = (lean_unbox(v_inst_312_) as u8);
    v_res_314_ = l_decidable__of__iff___redArg(v_inst_8__boxed_313_);
    v_r_315_ = lean_box((v_res_314_) as usize);
    return v_r_315_;
}
pub unsafe fn l_decidable__of__iff(
    mut v_b_316_: *mut LeanObject,
    mut v_a_317_: *mut LeanObject,
    mut v_h_318_: *mut LeanObject,
    mut v_inst_319_: u8,
) -> u8 {
    return v_inst_319_;
}
pub unsafe fn l_decidable__of__iff___boxed(
    mut v_b_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
    mut v_h_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_11__boxed_324_: u8 = 0;
    let mut v_res_325_: u8 = 0;
    let mut v_r_326_: *mut LeanObject = core::ptr::null_mut();
    v_inst_11__boxed_324_ = (lean_unbox(v_inst_323_) as u8);
    v_res_325_ = l_decidable__of__iff(v_b_320_, v_a_321_, v_h_322_, v_inst_11__boxed_324_);
    v_r_326_ = lean_box((v_res_325_) as usize);
    return v_r_326_;
}
pub unsafe fn l_decidable__of__iff_x27___redArg(mut v_inst_327_: u8) -> u8 {
    return v_inst_327_;
}
pub unsafe fn l_decidable__of__iff_x27___redArg___boxed(
    mut v_inst_328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_329_: u8 = 0;
    let mut v_res_330_: u8 = 0;
    let mut v_r_331_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_329_ = (lean_unbox(v_inst_328_) as u8);
    v_res_330_ = l_decidable__of__iff_x27___redArg(v_inst_8__boxed_329_);
    v_r_331_ = lean_box((v_res_330_) as usize);
    return v_r_331_;
}
pub unsafe fn l_decidable__of__iff_x27(
    mut v_a_332_: *mut LeanObject,
    mut v_b_333_: *mut LeanObject,
    mut v_h_334_: *mut LeanObject,
    mut v_inst_335_: u8,
) -> u8 {
    return v_inst_335_;
}
pub unsafe fn l_decidable__of__iff_x27___boxed(
    mut v_a_336_: *mut LeanObject,
    mut v_b_337_: *mut LeanObject,
    mut v_h_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_11__boxed_340_: u8 = 0;
    let mut v_res_341_: u8 = 0;
    let mut v_r_342_: *mut LeanObject = core::ptr::null_mut();
    v_inst_11__boxed_340_ = (lean_unbox(v_inst_339_) as u8);
    v_res_341_ = l_decidable__of__iff_x27(v_a_336_, v_b_337_, v_h_338_, v_inst_11__boxed_340_);
    v_r_342_ = lean_box((v_res_341_) as usize);
    return v_r_342_;
}
pub unsafe fn l_Decidable_predToBool___redArg___lam__0(
    mut v_inst_343_: *mut LeanObject,
    mut v_b_344_: *mut LeanObject,
) -> u8 {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: u8 = 0;
    v___x_345_ = lean_apply_1(v_inst_343_, v_b_344_);
    v___x_346_ = (lean_unbox(v___x_345_) as u8);
    return v___x_346_;
}
pub unsafe fn l_Decidable_predToBool___redArg___lam__0___boxed(
    mut v_inst_347_: *mut LeanObject,
    mut v_b_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: u8 = 0;
    let mut v_r_350_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Decidable_predToBool___redArg___lam__0(v_inst_347_, v_b_348_);
    v_r_350_ = lean_box((v_res_349_) as usize);
    return v_r_350_;
}
pub unsafe fn l_Decidable_predToBool___redArg(mut v_inst_351_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_352_: *mut LeanObject = core::ptr::null_mut();
    v___f_352_ = lean_alloc_closure(
        l_Decidable_predToBool___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_352_, 0, v_inst_351_);
    return v___f_352_;
}
pub unsafe fn l_Decidable_predToBool(
    mut v_00_u03b1_353_: *mut LeanObject,
    mut v_p_354_: *mut LeanObject,
    mut v_inst_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_356_: *mut LeanObject = core::ptr::null_mut();
    v___f_356_ = lean_alloc_closure(
        l_Decidable_predToBool___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_356_, 0, v_inst_355_);
    return v___f_356_;
}
pub unsafe fn l_instDecidablePredComp___aux__1___redArg(
    mut v_f_357_: *mut LeanObject,
    mut v_inst_358_: *mut LeanObject,
    mut v_x_359_: *mut LeanObject,
) -> u8 {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: u8 = 0;
    v___x_360_ = lean_apply_1(v_f_357_, v_x_359_);
    v___x_361_ = lean_apply_1(v_inst_358_, v___x_360_);
    v___x_362_ = (lean_unbox(v___x_361_) as u8);
    return v___x_362_;
}
pub unsafe fn l_instDecidablePredComp___aux__1___redArg___boxed(
    mut v_f_363_: *mut LeanObject,
    mut v_inst_364_: *mut LeanObject,
    mut v_x_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_366_: u8 = 0;
    let mut v_r_367_: *mut LeanObject = core::ptr::null_mut();
    v_res_366_ = l_instDecidablePredComp___aux__1___redArg(v_f_363_, v_inst_364_, v_x_365_);
    v_r_367_ = lean_box((v_res_366_) as usize);
    return v_r_367_;
}
pub unsafe fn l_instDecidablePredComp___aux__1(
    mut v_00_u03b1_368_: *mut LeanObject,
    mut v_p_369_: *mut LeanObject,
    mut v_00_u03b1_370_: *mut LeanObject,
    mut v_f_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
    mut v_x_373_: *mut LeanObject,
) -> u8 {
    let mut v___x_374_: u8 = 0;
    v___x_374_ = l_instDecidablePredComp___aux__1___redArg(v_f_371_, v_inst_372_, v_x_373_);
    return v___x_374_;
}
pub unsafe fn l_instDecidablePredComp___aux__1___boxed(
    mut v_00_u03b1_375_: *mut LeanObject,
    mut v_p_376_: *mut LeanObject,
    mut v_00_u03b1_377_: *mut LeanObject,
    mut v_f_378_: *mut LeanObject,
    mut v_inst_379_: *mut LeanObject,
    mut v_x_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_381_: u8 = 0;
    let mut v_r_382_: *mut LeanObject = core::ptr::null_mut();
    v_res_381_ = l_instDecidablePredComp___aux__1(
        v_00_u03b1_375_,
        v_p_376_,
        v_00_u03b1_377_,
        v_f_378_,
        v_inst_379_,
        v_x_380_,
    );
    v_r_382_ = lean_box((v_res_381_) as usize);
    return v_r_382_;
}
pub unsafe fn l_instDecidablePredComp___redArg(
    mut v_f_383_: *mut LeanObject,
    mut v_inst_384_: *mut LeanObject,
    mut v_x_385_: *mut LeanObject,
) -> u8 {
    let mut v___x_386_: u8 = 0;
    v___x_386_ = l_instDecidablePredComp___aux__1___redArg(v_f_383_, v_inst_384_, v_x_385_);
    return v___x_386_;
}
pub unsafe fn l_instDecidablePredComp___redArg___boxed(
    mut v_f_387_: *mut LeanObject,
    mut v_inst_388_: *mut LeanObject,
    mut v_x_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_390_: u8 = 0;
    let mut v_r_391_: *mut LeanObject = core::ptr::null_mut();
    v_res_390_ = l_instDecidablePredComp___redArg(v_f_387_, v_inst_388_, v_x_389_);
    v_r_391_ = lean_box((v_res_390_) as usize);
    return v_r_391_;
}
pub unsafe fn l_instDecidablePredComp(
    mut v_00_u03b1_392_: *mut LeanObject,
    mut v_p_393_: *mut LeanObject,
    mut v_00_u03b1_394_: *mut LeanObject,
    mut v_f_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
    mut v_x_397_: *mut LeanObject,
) -> u8 {
    let mut v___x_398_: u8 = 0;
    v___x_398_ = l_instDecidablePredComp___aux__1___redArg(v_f_395_, v_inst_396_, v_x_397_);
    return v___x_398_;
}
pub unsafe fn l_instDecidablePredComp___boxed(
    mut v_00_u03b1_399_: *mut LeanObject,
    mut v_p_400_: *mut LeanObject,
    mut v_00_u03b1_401_: *mut LeanObject,
    mut v_f_402_: *mut LeanObject,
    mut v_inst_403_: *mut LeanObject,
    mut v_x_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_405_: u8 = 0;
    let mut v_r_406_: *mut LeanObject = core::ptr::null_mut();
    v_res_405_ = l_instDecidablePredComp(
        v_00_u03b1_399_,
        v_p_400_,
        v_00_u03b1_401_,
        v_f_402_,
        v_inst_403_,
        v_x_404_,
    );
    v_r_406_ = lean_box((v_res_405_) as usize);
    return v_r_406_;
}
pub unsafe fn l_decidable__of__bool___redArg(mut v_x_407_: u8) -> u8 {
    return v_x_407_;
}
pub unsafe fn l_decidable__of__bool___redArg___boxed(
    mut v_x_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_409_: u8 = 0;
    let mut v_res_410_: u8 = 0;
    let mut v_r_411_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_409_ = (lean_unbox(v_x_408_) as u8);
    v_res_410_ = l_decidable__of__bool___redArg(v_x_36__boxed_409_);
    v_r_411_ = lean_box((v_res_410_) as usize);
    return v_r_411_;
}
pub unsafe fn l_decidable__of__bool(
    mut v_a_412_: *mut LeanObject,
    mut v_x_413_: u8,
    mut v_x_414_: *mut LeanObject,
) -> u8 {
    return v_x_413_;
}
pub unsafe fn l_decidable__of__bool___boxed(
    mut v_a_415_: *mut LeanObject,
    mut v_x_416_: *mut LeanObject,
    mut v_x_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_39__boxed_418_: u8 = 0;
    let mut v_res_419_: u8 = 0;
    let mut v_r_420_: *mut LeanObject = core::ptr::null_mut();
    v_x_39__boxed_418_ = (lean_unbox(v_x_416_) as u8);
    v_res_419_ = l_decidable__of__bool(v_a_415_, v_x_39__boxed_418_, v_x_417_);
    v_r_420_ = lean_box((v_res_419_) as usize);
    return v_r_420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_PropLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_PropLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_PropLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_PropLemmas(builtin);
}
