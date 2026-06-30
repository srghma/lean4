// Lean compiler output
// Module: Std.Internal.Do.WP.Basic
// Imports: Std.Internal.Do.PredTrans
use crate::r#gen::Std::Internal::Do::PredTrans::{
    initialize_Std_Internal_Do_PredTrans, l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1,
    l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1,
    l_Std_Internal_Do_pushArg___redArg___lam__1, runtime_initialize_Std_Internal_Do_PredTrans,
};
pub static mut l_Std_Internal_Do_Id_instWPMonad: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_Do_Option_instWPMonad: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Internal_Do_wp___redArg(
    mut v_inst_218_: *mut leanh::LeanObject,
    mut v_x_219_: *mut leanh::LeanObject,
    mut v_post_220_: *mut leanh::LeanObject,
    mut v_epost_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = leanh::lean_apply_4(
        v_inst_218_,
        leanh::lean_box(0),
        v_x_219_,
        v_post_220_,
        v_epost_221_,
    );
    return v___x_222_;
}
pub unsafe fn l_Std_Internal_Do_wp(
    mut v_m_223_: *mut leanh::LeanObject,
    mut v_Pred_224_: *mut leanh::LeanObject,
    mut v_EPred_225_: *mut leanh::LeanObject,
    mut v_inst_226_: *mut leanh::LeanObject,
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_inst_228_: *mut leanh::LeanObject,
    mut v_inst_229_: *mut leanh::LeanObject,
    mut v_00_u03b1_230_: *mut leanh::LeanObject,
    mut v_x_231_: *mut leanh::LeanObject,
    mut v_post_232_: *mut leanh::LeanObject,
    mut v_epost_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = leanh::lean_apply_4(
        v_inst_229_,
        leanh::lean_box(0),
        v_x_231_,
        v_post_232_,
        v_epost_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Std_Internal_Do_wp___boxed(
    mut v_m_235_: *mut leanh::LeanObject,
    mut v_Pred_236_: *mut leanh::LeanObject,
    mut v_EPred_237_: *mut leanh::LeanObject,
    mut v_inst_238_: *mut leanh::LeanObject,
    mut v_inst_239_: *mut leanh::LeanObject,
    mut v_inst_240_: *mut leanh::LeanObject,
    mut v_inst_241_: *mut leanh::LeanObject,
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_x_243_: *mut leanh::LeanObject,
    mut v_post_244_: *mut leanh::LeanObject,
    mut v_epost_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Std_Internal_Do_wp(
        v_m_235_,
        v_Pred_236_,
        v_EPred_237_,
        v_inst_238_,
        v_inst_239_,
        v_inst_240_,
        v_inst_241_,
        v_00_u03b1_242_,
        v_x_243_,
        v_post_244_,
        v_epost_245_,
    );
    leanh::lean_dec_ref(v_inst_238_);
    return v_res_246_;
}
pub unsafe fn _init_l_Std_Internal_Do_Id_instWPMonad() -> *mut leanh::LeanObject {
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = leanh::lean_box(0);
    return v___x_247_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_248_: *mut leanh::LeanObject,
    mut v_h__1_249_: *mut leanh::LeanObject,
    mut v_h__2_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_248_) == 0 {
        let mut v_a_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_249_);
        v_a_251_ = leanh::lean_ctor_get(v_x_248_, 0);
        leanh::lean_inc(v_a_251_);
        leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_252_ = leanh::lean_apply_1(v_h__2_250_, v_a_251_);
        return v___x_252_;
    } else {
        let mut v_a_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_250_);
        v_a_253_ = leanh::lean_ctor_get(v_x_248_, 0);
        leanh::lean_inc(v_a_253_);
        leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = leanh::lean_apply_1(v_h__1_249_, v_a_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_255_: *mut leanh::LeanObject,
    mut v_00_u03b1_256_: *mut leanh::LeanObject,
    mut v_motive_257_: *mut leanh::LeanObject,
    mut v_x_258_: *mut leanh::LeanObject,
    mut v_h__1_259_: *mut leanh::LeanObject,
    mut v_h__2_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_258_) == 0 {
        let mut v_a_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_259_);
        v_a_261_ = leanh::lean_ctor_get(v_x_258_, 0);
        leanh::lean_inc(v_a_261_);
        leanh::lean_dec_ref_known(v_x_258_, 1);
        v___x_262_ = leanh::lean_apply_1(v_h__2_260_, v_a_261_);
        return v___x_262_;
    } else {
        let mut v_a_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_260_);
        v_a_263_ = leanh::lean_ctor_get(v_x_258_, 0);
        leanh::lean_inc(v_a_263_);
        leanh::lean_dec_ref_known(v_x_258_, 1);
        v___x_264_ = leanh::lean_apply_1(v_h__1_259_, v_a_263_);
        return v___x_264_;
    }
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0(
    mut v_inst_265_: *mut leanh::LeanObject,
    mut v_00_u03b1_266_: *mut leanh::LeanObject,
    mut v_x_267_: *mut leanh::LeanObject,
    mut v___y_268_: *mut leanh::LeanObject,
    mut v___y_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = leanh::lean_apply_2(v_inst_265_, leanh::lean_box(0), v_x_267_);
    v___x_271_ = l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(
        v___x_270_, v___y_268_, v___y_269_,
    );
    return v___x_271_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg(
    mut v_inst_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_273_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_273_, 0, v_inst_272_);
    return v___f_273_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad(
    mut v_m_274_: *mut leanh::LeanObject,
    mut v_EPred_275_: *mut leanh::LeanObject,
    mut v_00_u03b5_276_: *mut leanh::LeanObject,
    mut v_Pred_277_: *mut leanh::LeanObject,
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_inst_279_: *mut leanh::LeanObject,
    mut v_inst_280_: *mut leanh::LeanObject,
    mut v_inst_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_282_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_282_, 0, v_inst_281_);
    return v___f_282_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___boxed(
    mut v_m_283_: *mut leanh::LeanObject,
    mut v_EPred_284_: *mut leanh::LeanObject,
    mut v_00_u03b5_285_: *mut leanh::LeanObject,
    mut v_Pred_286_: *mut leanh::LeanObject,
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_inst_288_: *mut leanh::LeanObject,
    mut v_inst_289_: *mut leanh::LeanObject,
    mut v_inst_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Std_Internal_Do_ExceptT_instWPMonad(
        v_m_283_,
        v_EPred_284_,
        v_00_u03b5_285_,
        v_Pred_286_,
        v_inst_287_,
        v_inst_288_,
        v_inst_289_,
        v_inst_290_,
    );
    leanh::lean_dec_ref(v_inst_287_);
    return v_res_291_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0(
    mut v_inst_292_: *mut leanh::LeanObject,
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
    mut v___y_295_: *mut leanh::LeanObject,
    mut v___y_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = leanh::lean_apply_2(v_inst_292_, leanh::lean_box(0), v_x_294_);
    v___x_298_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(
        v___x_297_, v___y_295_, v___y_296_,
    );
    return v___x_298_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg(
    mut v_inst_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_300_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_300_, 0, v_inst_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad(
    mut v_m_301_: *mut leanh::LeanObject,
    mut v_EPred_302_: *mut leanh::LeanObject,
    mut v_Pred_303_: *mut leanh::LeanObject,
    mut v_inst_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_inst_306_: *mut leanh::LeanObject,
    mut v_inst_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_308_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_308_, 0, v_inst_307_);
    return v___f_308_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___boxed(
    mut v_m_309_: *mut leanh::LeanObject,
    mut v_EPred_310_: *mut leanh::LeanObject,
    mut v_Pred_311_: *mut leanh::LeanObject,
    mut v_inst_312_: *mut leanh::LeanObject,
    mut v_inst_313_: *mut leanh::LeanObject,
    mut v_inst_314_: *mut leanh::LeanObject,
    mut v_inst_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Std_Internal_Do_OptionT_instWPMonad(
        v_m_309_,
        v_EPred_310_,
        v_Pred_311_,
        v_inst_312_,
        v_inst_313_,
        v_inst_314_,
        v_inst_315_,
    );
    leanh::lean_dec_ref(v_inst_312_);
    return v_res_316_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0(
    mut v_x_317_: *mut leanh::LeanObject,
    mut v_inst_318_: *mut leanh::LeanObject,
    mut v_x_319_: *mut leanh::LeanObject,
    mut v___y_320_: *mut leanh::LeanObject,
    mut v___y_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = leanh::lean_apply_1(v_x_317_, v_x_319_);
    v___x_323_ = leanh::lean_apply_4(
        v_inst_318_,
        leanh::lean_box(0),
        v___x_322_,
        v___y_320_,
        v___y_321_,
    );
    return v___x_323_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1(
    mut v_inst_324_: *mut leanh::LeanObject,
    mut v_00_u03b1_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
    mut v___y_327_: *mut leanh::LeanObject,
    mut v___y_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_330_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_330_, 0, v_x_326_);
    leanh::lean_closure_set(v___f_330_, 1, v_inst_324_);
    v___x_331_ =
        l_Std_Internal_Do_pushArg___redArg___lam__1(v___f_330_, v___y_327_, v___y_328_, v___y_329_);
    return v___x_331_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg(
    mut v_inst_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_333_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_333_, 0, v_inst_332_);
    return v___f_333_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad(
    mut v_m_334_: *mut leanh::LeanObject,
    mut v_EPred_335_: *mut leanh::LeanObject,
    mut v_00_u03c3_336_: *mut leanh::LeanObject,
    mut v_Pred_337_: *mut leanh::LeanObject,
    mut v_inst_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
    mut v_inst_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_342_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_342_, 0, v_inst_341_);
    return v___f_342_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___boxed(
    mut v_m_343_: *mut leanh::LeanObject,
    mut v_EPred_344_: *mut leanh::LeanObject,
    mut v_00_u03c3_345_: *mut leanh::LeanObject,
    mut v_Pred_346_: *mut leanh::LeanObject,
    mut v_inst_347_: *mut leanh::LeanObject,
    mut v_inst_348_: *mut leanh::LeanObject,
    mut v_inst_349_: *mut leanh::LeanObject,
    mut v_inst_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Std_Internal_Do_StateT_instWPMonad(
        v_m_343_,
        v_EPred_344_,
        v_00_u03c3_345_,
        v_Pred_346_,
        v_inst_347_,
        v_inst_348_,
        v_inst_349_,
        v_inst_350_,
    );
    leanh::lean_dec_ref(v_inst_347_);
    return v_res_351_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0(
    mut v___y_352_: *mut leanh::LeanObject,
    mut v___y_353_: *mut leanh::LeanObject,
    mut v_a_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = leanh::lean_apply_2(v___y_352_, v_a_354_, v___y_353_);
    return v___x_355_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1(
    mut v_inst_356_: *mut leanh::LeanObject,
    mut v_00_u03b1_357_: *mut leanh::LeanObject,
    mut v_x_358_: *mut leanh::LeanObject,
    mut v___y_359_: *mut leanh::LeanObject,
    mut v___y_360_: *mut leanh::LeanObject,
    mut v___y_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_361_);
    v___f_362_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_362_, 0, v___y_359_);
    leanh::lean_closure_set(v___f_362_, 1, v___y_361_);
    v___x_363_ = leanh::lean_apply_1(v_x_358_, v___y_361_);
    v___x_364_ = leanh::lean_apply_4(
        v_inst_356_,
        leanh::lean_box(0),
        v___x_363_,
        v___f_362_,
        v___y_360_,
    );
    return v___x_364_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg(
    mut v_inst_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_366_, 0, v_inst_365_);
    return v___f_366_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad(
    mut v_m_367_: *mut leanh::LeanObject,
    mut v_EPred_368_: *mut leanh::LeanObject,
    mut v_00_u03c1_369_: *mut leanh::LeanObject,
    mut v_Pred_370_: *mut leanh::LeanObject,
    mut v_inst_371_: *mut leanh::LeanObject,
    mut v_inst_372_: *mut leanh::LeanObject,
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_375_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_375_, 0, v_inst_374_);
    return v___f_375_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___boxed(
    mut v_m_376_: *mut leanh::LeanObject,
    mut v_EPred_377_: *mut leanh::LeanObject,
    mut v_00_u03c1_378_: *mut leanh::LeanObject,
    mut v_Pred_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_inst_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_Internal_Do_ReaderT_instWPMonad(
        v_m_376_,
        v_EPred_377_,
        v_00_u03c1_378_,
        v_Pred_379_,
        v_inst_380_,
        v_inst_381_,
        v_inst_382_,
        v_inst_383_,
    );
    leanh::lean_dec_ref(v_inst_380_);
    return v_res_384_;
}
pub unsafe fn _init_l_Std_Internal_Do_Option_instWPMonad() -> *mut leanh::LeanObject {
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = leanh::lean_box(0);
    return v___x_385_;
}
pub unsafe fn l_Std_Internal_Do_Except_instWPMonad(
    mut v_00_u03b5_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = leanh::lean_box(0);
    return v___x_387_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(
    mut v_x_388_: *mut leanh::LeanObject,
    mut v_h__1_389_: *mut leanh::LeanObject,
    mut v_h__2_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_388_) == 0 {
        let mut v_a_391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_390_);
        v_a_391_ = leanh::lean_ctor_get(v_x_388_, 0);
        leanh::lean_inc(v_a_391_);
        v_a_392_ = leanh::lean_ctor_get(v_x_388_, 1);
        leanh::lean_inc(v_a_392_);
        leanh::lean_dec_ref_known(v_x_388_, 2);
        v___x_393_ = leanh::lean_apply_2(v_h__1_389_, v_a_391_, v_a_392_);
        return v___x_393_;
    } else {
        let mut v_a_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_389_);
        v_a_394_ = leanh::lean_ctor_get(v_x_388_, 0);
        leanh::lean_inc(v_a_394_);
        v_a_395_ = leanh::lean_ctor_get(v_x_388_, 1);
        leanh::lean_inc(v_a_395_);
        leanh::lean_dec_ref_known(v_x_388_, 2);
        v___x_396_ = leanh::lean_apply_2(v_h__2_390_, v_a_394_, v_a_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(
    mut v_00_u03b5_397_: *mut leanh::LeanObject,
    mut v_00_u03c3_398_: *mut leanh::LeanObject,
    mut v_00_u03b1_399_: *mut leanh::LeanObject,
    mut v_motive_400_: *mut leanh::LeanObject,
    mut v_x_401_: *mut leanh::LeanObject,
    mut v_h__1_402_: *mut leanh::LeanObject,
    mut v_h__2_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_401_) == 0 {
        let mut v_a_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_403_);
        v_a_404_ = leanh::lean_ctor_get(v_x_401_, 0);
        leanh::lean_inc(v_a_404_);
        v_a_405_ = leanh::lean_ctor_get(v_x_401_, 1);
        leanh::lean_inc(v_a_405_);
        leanh::lean_dec_ref_known(v_x_401_, 2);
        v___x_406_ = leanh::lean_apply_2(v_h__1_402_, v_a_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_402_);
        v_a_407_ = leanh::lean_ctor_get(v_x_401_, 0);
        leanh::lean_inc(v_a_407_);
        v_a_408_ = leanh::lean_ctor_get(v_x_401_, 1);
        leanh::lean_inc(v_a_408_);
        leanh::lean_dec_ref_known(v_x_401_, 2);
        v___x_409_ = leanh::lean_apply_2(v_h__2_403_, v_a_407_, v_a_408_);
        return v___x_409_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter___redArg(
    mut v_x_410_: *mut leanh::LeanObject,
    mut v_h__1_411_: *mut leanh::LeanObject,
    mut v_h__2_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_410_) == 0 {
        let mut v_a_413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_412_);
        v_a_413_ = leanh::lean_ctor_get(v_x_410_, 0);
        leanh::lean_inc(v_a_413_);
        v_a_414_ = leanh::lean_ctor_get(v_x_410_, 1);
        leanh::lean_inc(v_a_414_);
        leanh::lean_dec_ref_known(v_x_410_, 2);
        v___x_415_ = leanh::lean_apply_2(v_h__1_411_, v_a_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_411_);
        v_a_416_ = leanh::lean_ctor_get(v_x_410_, 0);
        leanh::lean_inc(v_a_416_);
        v_a_417_ = leanh::lean_ctor_get(v_x_410_, 1);
        leanh::lean_inc(v_a_417_);
        leanh::lean_dec_ref_known(v_x_410_, 2);
        v___x_418_ = leanh::lean_apply_2(v_h__2_412_, v_a_416_, v_a_417_);
        return v___x_418_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter(
    mut v_00_u03b5_419_: *mut leanh::LeanObject,
    mut v_00_u03c3_420_: *mut leanh::LeanObject,
    mut v_00_u03b1_421_: *mut leanh::LeanObject,
    mut v_motive_422_: *mut leanh::LeanObject,
    mut v_x_423_: *mut leanh::LeanObject,
    mut v_h__1_424_: *mut leanh::LeanObject,
    mut v_h__2_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_423_) == 0 {
        let mut v_a_426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_425_);
        v_a_426_ = leanh::lean_ctor_get(v_x_423_, 0);
        leanh::lean_inc(v_a_426_);
        v_a_427_ = leanh::lean_ctor_get(v_x_423_, 1);
        leanh::lean_inc(v_a_427_);
        leanh::lean_dec_ref_known(v_x_423_, 2);
        v___x_428_ = leanh::lean_apply_2(v_h__1_424_, v_a_426_, v_a_427_);
        return v___x_428_;
    } else {
        let mut v_a_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_424_);
        v_a_429_ = leanh::lean_ctor_get(v_x_423_, 0);
        leanh::lean_inc(v_a_429_);
        v_a_430_ = leanh::lean_ctor_get(v_x_423_, 1);
        leanh::lean_inc(v_a_430_);
        leanh::lean_dec_ref_known(v_x_423_, 2);
        v___x_431_ = leanh::lean_apply_2(v_h__2_425_, v_a_429_, v_a_430_);
        return v___x_431_;
    }
}
pub unsafe fn l_Std_Internal_Do_EStateM_instWPMonad(
    mut v_00_u03b5_432_: *mut leanh::LeanObject,
    mut v_00_u03c3_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = leanh::lean_box(0);
    return v___x_434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_WP_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Internal_Do_Id_instWPMonad = _init_l_Std_Internal_Do_Id_instWPMonad();
    l_Std_Internal_Do_Option_instWPMonad = _init_l_Std_Internal_Do_Option_instWPMonad();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_WP_Basic(
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
pub unsafe fn initialize_Std_Internal_Do_WP_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_WP_Basic(builtin);
}