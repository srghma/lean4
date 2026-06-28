// Lean compiler output
// Module: Std.Internal.Do.WP.Basic
// Imports: Std.Internal.Do.PredTrans
use crate::r#gen::Std::Internal::Do::PredTrans::{
    initialize_Std_Internal_Do_PredTrans, l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1,
    l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1,
    l_Std_Internal_Do_pushArg___redArg___lam__1, runtime_initialize_Std_Internal_Do_PredTrans,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static mut l_Std_Internal_Do_Id_instWPMonad: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Internal_Do_Option_instWPMonad: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Internal_Do_wp___redArg(
    mut v_inst_218_: *mut LeanObject,
    mut v_x_219_: *mut LeanObject,
    mut v_post_220_: *mut LeanObject,
    mut v_epost_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    v___x_222_ = lean_apply_4(
        v_inst_218_,
        lean_box(0),
        v_x_219_,
        v_post_220_,
        v_epost_221_,
    );
    return v___x_222_;
}
pub unsafe fn l_Std_Internal_Do_wp(
    mut v_m_223_: *mut LeanObject,
    mut v_Pred_224_: *mut LeanObject,
    mut v_EPred_225_: *mut LeanObject,
    mut v_inst_226_: *mut LeanObject,
    mut v_inst_227_: *mut LeanObject,
    mut v_inst_228_: *mut LeanObject,
    mut v_inst_229_: *mut LeanObject,
    mut v_00_u03b1_230_: *mut LeanObject,
    mut v_x_231_: *mut LeanObject,
    mut v_post_232_: *mut LeanObject,
    mut v_epost_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    v___x_234_ = lean_apply_4(
        v_inst_229_,
        lean_box(0),
        v_x_231_,
        v_post_232_,
        v_epost_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Std_Internal_Do_wp___boxed(
    mut v_m_235_: *mut LeanObject,
    mut v_Pred_236_: *mut LeanObject,
    mut v_EPred_237_: *mut LeanObject,
    mut v_inst_238_: *mut LeanObject,
    mut v_inst_239_: *mut LeanObject,
    mut v_inst_240_: *mut LeanObject,
    mut v_inst_241_: *mut LeanObject,
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_x_243_: *mut LeanObject,
    mut v_post_244_: *mut LeanObject,
    mut v_epost_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_246_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_238_);
    return v_res_246_;
}
pub unsafe fn _init_l_Std_Internal_Do_Id_instWPMonad() -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = lean_box(0);
    return v___x_247_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_248_: *mut LeanObject,
    mut v_h__1_249_: *mut LeanObject,
    mut v_h__2_250_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_248_) == 0 {
        let mut v_a_251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_249_);
        v_a_251_ = lean_ctor_get(v_x_248_, 0);
        lean_inc(v_a_251_);
        lean_dec_ref_known(v_x_248_, 1);
        v___x_252_ = lean_apply_1(v_h__2_250_, v_a_251_);
        return v___x_252_;
    } else {
        let mut v_a_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_250_);
        v_a_253_ = lean_ctor_get(v_x_248_, 0);
        lean_inc(v_a_253_);
        lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = lean_apply_1(v_h__1_249_, v_a_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_255_: *mut LeanObject,
    mut v_00_u03b1_256_: *mut LeanObject,
    mut v_motive_257_: *mut LeanObject,
    mut v_x_258_: *mut LeanObject,
    mut v_h__1_259_: *mut LeanObject,
    mut v_h__2_260_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_258_) == 0 {
        let mut v_a_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_259_);
        v_a_261_ = lean_ctor_get(v_x_258_, 0);
        lean_inc(v_a_261_);
        lean_dec_ref_known(v_x_258_, 1);
        v___x_262_ = lean_apply_1(v_h__2_260_, v_a_261_);
        return v___x_262_;
    } else {
        let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_260_);
        v_a_263_ = lean_ctor_get(v_x_258_, 0);
        lean_inc(v_a_263_);
        lean_dec_ref_known(v_x_258_, 1);
        v___x_264_ = lean_apply_1(v_h__1_259_, v_a_263_);
        return v___x_264_;
    }
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0(
    mut v_inst_265_: *mut LeanObject,
    mut v_00_u03b1_266_: *mut LeanObject,
    mut v_x_267_: *mut LeanObject,
    mut v___y_268_: *mut LeanObject,
    mut v___y_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = lean_apply_2(v_inst_265_, lean_box(0), v_x_267_);
    v___x_271_ = l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(
        v___x_270_, v___y_268_, v___y_269_,
    );
    return v___x_271_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg(
    mut v_inst_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_273_: *mut LeanObject = core::ptr::null_mut();
    v___f_273_ = lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_273_, 0, v_inst_272_);
    return v___f_273_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad(
    mut v_m_274_: *mut LeanObject,
    mut v_EPred_275_: *mut LeanObject,
    mut v_00_u03b5_276_: *mut LeanObject,
    mut v_Pred_277_: *mut LeanObject,
    mut v_inst_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_inst_280_: *mut LeanObject,
    mut v_inst_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_282_: *mut LeanObject = core::ptr::null_mut();
    v___f_282_ = lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_282_, 0, v_inst_281_);
    return v___f_282_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___boxed(
    mut v_m_283_: *mut LeanObject,
    mut v_EPred_284_: *mut LeanObject,
    mut v_00_u03b5_285_: *mut LeanObject,
    mut v_Pred_286_: *mut LeanObject,
    mut v_inst_287_: *mut LeanObject,
    mut v_inst_288_: *mut LeanObject,
    mut v_inst_289_: *mut LeanObject,
    mut v_inst_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_291_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_287_);
    return v_res_291_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0(
    mut v_inst_292_: *mut LeanObject,
    mut v_00_u03b1_293_: *mut LeanObject,
    mut v_x_294_: *mut LeanObject,
    mut v___y_295_: *mut LeanObject,
    mut v___y_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_apply_2(v_inst_292_, lean_box(0), v_x_294_);
    v___x_298_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(
        v___x_297_, v___y_295_, v___y_296_,
    );
    return v___x_298_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg(
    mut v_inst_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_300_: *mut LeanObject = core::ptr::null_mut();
    v___f_300_ = lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_300_, 0, v_inst_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad(
    mut v_m_301_: *mut LeanObject,
    mut v_EPred_302_: *mut LeanObject,
    mut v_Pred_303_: *mut LeanObject,
    mut v_inst_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_308_: *mut LeanObject = core::ptr::null_mut();
    v___f_308_ = lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_308_, 0, v_inst_307_);
    return v___f_308_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___boxed(
    mut v_m_309_: *mut LeanObject,
    mut v_EPred_310_: *mut LeanObject,
    mut v_Pred_311_: *mut LeanObject,
    mut v_inst_312_: *mut LeanObject,
    mut v_inst_313_: *mut LeanObject,
    mut v_inst_314_: *mut LeanObject,
    mut v_inst_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Std_Internal_Do_OptionT_instWPMonad(
        v_m_309_,
        v_EPred_310_,
        v_Pred_311_,
        v_inst_312_,
        v_inst_313_,
        v_inst_314_,
        v_inst_315_,
    );
    lean_dec_ref(v_inst_312_);
    return v_res_316_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0(
    mut v_x_317_: *mut LeanObject,
    mut v_inst_318_: *mut LeanObject,
    mut v_x_319_: *mut LeanObject,
    mut v___y_320_: *mut LeanObject,
    mut v___y_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_apply_1(v_x_317_, v_x_319_);
    v___x_323_ = lean_apply_4(v_inst_318_, lean_box(0), v___x_322_, v___y_320_, v___y_321_);
    return v___x_323_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1(
    mut v_inst_324_: *mut LeanObject,
    mut v_00_u03b1_325_: *mut LeanObject,
    mut v_x_326_: *mut LeanObject,
    mut v___y_327_: *mut LeanObject,
    mut v___y_328_: *mut LeanObject,
    mut v___y_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v___f_330_ = lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_330_, 0, v_x_326_);
    lean_closure_set(v___f_330_, 1, v_inst_324_);
    v___x_331_ =
        l_Std_Internal_Do_pushArg___redArg___lam__1(v___f_330_, v___y_327_, v___y_328_, v___y_329_);
    return v___x_331_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg(
    mut v_inst_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_333_: *mut LeanObject = core::ptr::null_mut();
    v___f_333_ = lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_333_, 0, v_inst_332_);
    return v___f_333_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad(
    mut v_m_334_: *mut LeanObject,
    mut v_EPred_335_: *mut LeanObject,
    mut v_00_u03c3_336_: *mut LeanObject,
    mut v_Pred_337_: *mut LeanObject,
    mut v_inst_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
    mut v_inst_340_: *mut LeanObject,
    mut v_inst_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_342_: *mut LeanObject = core::ptr::null_mut();
    v___f_342_ = lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_342_, 0, v_inst_341_);
    return v___f_342_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___boxed(
    mut v_m_343_: *mut LeanObject,
    mut v_EPred_344_: *mut LeanObject,
    mut v_00_u03c3_345_: *mut LeanObject,
    mut v_Pred_346_: *mut LeanObject,
    mut v_inst_347_: *mut LeanObject,
    mut v_inst_348_: *mut LeanObject,
    mut v_inst_349_: *mut LeanObject,
    mut v_inst_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_347_);
    return v_res_351_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0(
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v_a_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = lean_apply_2(v___y_352_, v_a_354_, v___y_353_);
    return v___x_355_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1(
    mut v_inst_356_: *mut LeanObject,
    mut v_00_u03b1_357_: *mut LeanObject,
    mut v_x_358_: *mut LeanObject,
    mut v___y_359_: *mut LeanObject,
    mut v___y_360_: *mut LeanObject,
    mut v___y_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_361_);
    v___f_362_ = lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_362_, 0, v___y_359_);
    lean_closure_set(v___f_362_, 1, v___y_361_);
    v___x_363_ = lean_apply_1(v_x_358_, v___y_361_);
    v___x_364_ = lean_apply_4(v_inst_356_, lean_box(0), v___x_363_, v___f_362_, v___y_360_);
    return v___x_364_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg(
    mut v_inst_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_366_: *mut LeanObject = core::ptr::null_mut();
    v___f_366_ = lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_366_, 0, v_inst_365_);
    return v___f_366_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad(
    mut v_m_367_: *mut LeanObject,
    mut v_EPred_368_: *mut LeanObject,
    mut v_00_u03c1_369_: *mut LeanObject,
    mut v_Pred_370_: *mut LeanObject,
    mut v_inst_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_375_: *mut LeanObject = core::ptr::null_mut();
    v___f_375_ = lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_375_, 0, v_inst_374_);
    return v___f_375_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___boxed(
    mut v_m_376_: *mut LeanObject,
    mut v_EPred_377_: *mut LeanObject,
    mut v_00_u03c1_378_: *mut LeanObject,
    mut v_Pred_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_inst_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_380_);
    return v_res_384_;
}
pub unsafe fn _init_l_Std_Internal_Do_Option_instWPMonad() -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = lean_box(0);
    return v___x_385_;
}
pub unsafe fn l_Std_Internal_Do_Except_instWPMonad(
    mut v_00_u03b5_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_box(0);
    return v___x_387_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(
    mut v_x_388_: *mut LeanObject,
    mut v_h__1_389_: *mut LeanObject,
    mut v_h__2_390_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_388_) == 0 {
        let mut v_a_391_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_390_);
        v_a_391_ = lean_ctor_get(v_x_388_, 0);
        lean_inc(v_a_391_);
        v_a_392_ = lean_ctor_get(v_x_388_, 1);
        lean_inc(v_a_392_);
        lean_dec_ref_known(v_x_388_, 2);
        v___x_393_ = lean_apply_2(v_h__1_389_, v_a_391_, v_a_392_);
        return v___x_393_;
    } else {
        let mut v_a_394_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_389_);
        v_a_394_ = lean_ctor_get(v_x_388_, 0);
        lean_inc(v_a_394_);
        v_a_395_ = lean_ctor_get(v_x_388_, 1);
        lean_inc(v_a_395_);
        lean_dec_ref_known(v_x_388_, 2);
        v___x_396_ = lean_apply_2(v_h__2_390_, v_a_394_, v_a_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(
    mut v_00_u03b5_397_: *mut LeanObject,
    mut v_00_u03c3_398_: *mut LeanObject,
    mut v_00_u03b1_399_: *mut LeanObject,
    mut v_motive_400_: *mut LeanObject,
    mut v_x_401_: *mut LeanObject,
    mut v_h__1_402_: *mut LeanObject,
    mut v_h__2_403_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_401_) == 0 {
        let mut v_a_404_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_403_);
        v_a_404_ = lean_ctor_get(v_x_401_, 0);
        lean_inc(v_a_404_);
        v_a_405_ = lean_ctor_get(v_x_401_, 1);
        lean_inc(v_a_405_);
        lean_dec_ref_known(v_x_401_, 2);
        v___x_406_ = lean_apply_2(v_h__1_402_, v_a_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_402_);
        v_a_407_ = lean_ctor_get(v_x_401_, 0);
        lean_inc(v_a_407_);
        v_a_408_ = lean_ctor_get(v_x_401_, 1);
        lean_inc(v_a_408_);
        lean_dec_ref_known(v_x_401_, 2);
        v___x_409_ = lean_apply_2(v_h__2_403_, v_a_407_, v_a_408_);
        return v___x_409_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter___redArg(
    mut v_x_410_: *mut LeanObject,
    mut v_h__1_411_: *mut LeanObject,
    mut v_h__2_412_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_410_) == 0 {
        let mut v_a_413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_412_);
        v_a_413_ = lean_ctor_get(v_x_410_, 0);
        lean_inc(v_a_413_);
        v_a_414_ = lean_ctor_get(v_x_410_, 1);
        lean_inc(v_a_414_);
        lean_dec_ref_known(v_x_410_, 2);
        v___x_415_ = lean_apply_2(v_h__1_411_, v_a_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_411_);
        v_a_416_ = lean_ctor_get(v_x_410_, 0);
        lean_inc(v_a_416_);
        v_a_417_ = lean_ctor_get(v_x_410_, 1);
        lean_inc(v_a_417_);
        lean_dec_ref_known(v_x_410_, 2);
        v___x_418_ = lean_apply_2(v_h__2_412_, v_a_416_, v_a_417_);
        return v___x_418_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter(
    mut v_00_u03b5_419_: *mut LeanObject,
    mut v_00_u03c3_420_: *mut LeanObject,
    mut v_00_u03b1_421_: *mut LeanObject,
    mut v_motive_422_: *mut LeanObject,
    mut v_x_423_: *mut LeanObject,
    mut v_h__1_424_: *mut LeanObject,
    mut v_h__2_425_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_423_) == 0 {
        let mut v_a_426_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_425_);
        v_a_426_ = lean_ctor_get(v_x_423_, 0);
        lean_inc(v_a_426_);
        v_a_427_ = lean_ctor_get(v_x_423_, 1);
        lean_inc(v_a_427_);
        lean_dec_ref_known(v_x_423_, 2);
        v___x_428_ = lean_apply_2(v_h__1_424_, v_a_426_, v_a_427_);
        return v___x_428_;
    } else {
        let mut v_a_429_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_424_);
        v_a_429_ = lean_ctor_get(v_x_423_, 0);
        lean_inc(v_a_429_);
        v_a_430_ = lean_ctor_get(v_x_423_, 1);
        lean_inc(v_a_430_);
        lean_dec_ref_known(v_x_423_, 2);
        v___x_431_ = lean_apply_2(v_h__2_425_, v_a_429_, v_a_430_);
        return v___x_431_;
    }
}
pub unsafe fn l_Std_Internal_Do_EStateM_instWPMonad(
    mut v_00_u03b5_432_: *mut LeanObject,
    mut v_00_u03c3_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_box(0);
    return v___x_434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Internal_Do_Id_instWPMonad = _init_l_Std_Internal_Do_Id_instWPMonad();
    l_Std_Internal_Do_Option_instWPMonad = _init_l_Std_Internal_Do_Option_instWPMonad();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_Do_WP_Basic(builtin);
}
