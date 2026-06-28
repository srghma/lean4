// Lean compiler output
// Module: Lean.Meta.Match.Value
// Imports: Lean.Meta.LitValues
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getBitVecValue_x3f, l_Lean_Meta_getCharValue_x3f,
    l_Lean_Meta_getFinValue_x3f, l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
    l_Lean_Meta_getStringValue_x3f, l_Lean_Meta_getUInt8Value_x3f, l_Lean_Meta_getUInt16Value_x3f,
    l_Lean_Meta_getUInt32Value_x3f, l_Lean_Meta_getUInt64Value_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(
    mut v_e_233_: *mut LeanObject,
    mut v___y_234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut v_unused_257_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_236_ = l_Lean_Expr_hasMVar(v_e_233_);
                if v___x_236_ == 0 {
                    v___x_237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_237_, 0, v_e_233_);
                    return v___x_237_;
                } else {
                    v___x_238_ = lean_st_ref_get(v___y_234_);
                    v_mctx_239_ = lean_ctor_get(v___x_238_, 0);
                    lean_inc_ref(v_mctx_239_);
                    lean_dec(v___x_238_);
                    v___x_240_ = l_Lean_instantiateMVarsCore(v_mctx_239_, v_e_233_);
                    v_fst_241_ = lean_ctor_get(v___x_240_, 0);
                    lean_inc(v_fst_241_);
                    v_snd_242_ = lean_ctor_get(v___x_240_, 1);
                    lean_inc(v_snd_242_);
                    lean_dec_ref(v___x_240_);
                    v___x_243_ = lean_st_ref_take(v___y_234_);
                    v_cache_244_ = lean_ctor_get(v___x_243_, 1);
                    v_zetaDeltaFVarIds_245_ = lean_ctor_get(v___x_243_, 2);
                    v_postponed_246_ = lean_ctor_get(v___x_243_, 3);
                    v_diag_247_ = lean_ctor_get(v___x_243_, 4);
                    v_isSharedCheck_256_ = (!lean_is_exclusive(v___x_243_)) as u8;
                    if v_isSharedCheck_256_ == 0 {
                        v_unused_257_ = lean_ctor_get(v___x_243_, 0);
                        lean_dec(v_unused_257_);
                        v___x_249_ = v___x_243_;
                        v_isShared_250_ = v_isSharedCheck_256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_247_);
                        lean_inc(v_postponed_246_);
                        lean_inc(v_zetaDeltaFVarIds_245_);
                        lean_inc(v_cache_244_);
                        lean_dec(v___x_243_);
                        v___x_249_ = lean_box(0);
                        v_isShared_250_ = v_isSharedCheck_256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_250_ == 0 {
                    lean_ctor_set(v___x_249_, 0, v_snd_242_);
                    v___x_252_ = v___x_249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_255_, 0, v_snd_242_);
                    lean_ctor_set(v_reuseFailAlloc_255_, 1, v_cache_244_);
                    lean_ctor_set(v_reuseFailAlloc_255_, 2, v_zetaDeltaFVarIds_245_);
                    lean_ctor_set(v_reuseFailAlloc_255_, 3, v_postponed_246_);
                    lean_ctor_set(v_reuseFailAlloc_255_, 4, v_diag_247_);
                    v___x_252_ = v_reuseFailAlloc_255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_253_ = lean_st_ref_set(v___y_234_, v___x_252_);
                v___x_254_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_254_, 0, v_fst_241_);
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(
    mut v_e_258_: *mut LeanObject,
    mut v___y_259_: *mut LeanObject,
    mut v___y_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(
        v_e_258_, v___y_259_,
    );
    lean_dec(v___y_259_);
    return v_res_261_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(
    mut v_e_262_: *mut LeanObject,
    mut v___y_263_: *mut LeanObject,
    mut v___y_264_: *mut LeanObject,
    mut v___y_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(
        v_e_262_, v___y_264_,
    );
    return v___x_268_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(
    mut v_e_269_: *mut LeanObject,
    mut v___y_270_: *mut LeanObject,
    mut v___y_271_: *mut LeanObject,
    mut v___y_272_: *mut LeanObject,
    mut v___y_273_: *mut LeanObject,
    mut v___y_274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_275_: *mut LeanObject = core::ptr::null_mut();
    v_res_275_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(
        v_e_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_,
    );
    lean_dec(v___y_273_);
    lean_dec_ref(v___y_272_);
    lean_dec(v___y_271_);
    lean_dec_ref(v___y_270_);
    return v_res_275_;
}
pub unsafe fn l_Lean_Meta_isMatchValue(
    mut v_e_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_293_: u8 = 0;
    let mut v___x_294_: u8 = 0;
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_299_: u8 = 0;
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_304_: u8 = 0;
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_310_: u8 = 0;
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_315_: u8 = 0;
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_320_: u8 = 0;
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_325_: u8 = 0;
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_330_: u8 = 0;
    let mut v___x_331_: u8 = 0;
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_340_: u8 = 0;
    let mut v_a_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_344_: u8 = 0;
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_348_: u8 = 0;
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_353_: u8 = 0;
    let mut v_a_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_357_: u8 = 0;
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_361_: u8 = 0;
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_366_: u8 = 0;
    let mut v_a_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_374_: u8 = 0;
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_379_: u8 = 0;
    let mut v_a_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_383_: u8 = 0;
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_387_: u8 = 0;
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_392_: u8 = 0;
    let mut v_a_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_400_: u8 = 0;
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut v_a_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_422_: u8 = 0;
    let mut v_a_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_426_: u8 = 0;
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_a_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_439_: u8 = 0;
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_449_: u8 = 0;
    let mut v_a_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_282_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(
                        v_e_276_, v_a_278_,
                    );
                v_a_283_ = lean_ctor_get(v___x_282_, 0);
                lean_inc(v_a_283_);
                lean_dec_ref(v___x_282_);
                v___x_284_ =
                    l_Lean_Meta_getNatValue_x3f(v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
                if lean_obj_tag(v___x_284_) == 0 {
                    v_a_285_ = lean_ctor_get(v___x_284_, 0);
                    v_isSharedCheck_449_ = (!lean_is_exclusive(v___x_284_)) as u8;
                    if v_isSharedCheck_449_ == 0 {
                        v___x_287_ = v___x_284_;
                        v_isShared_288_ = v_isSharedCheck_449_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_285_);
                        lean_dec(v___x_284_);
                        v___x_287_ = lean_box(0);
                        v_isShared_288_ = v_isSharedCheck_449_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_283_);
                    v_a_450_ = lean_ctor_get(v___x_284_, 0);
                    v_isSharedCheck_457_ = (!lean_is_exclusive(v___x_284_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_452_ = v___x_284_;
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_450_);
                        lean_dec(v___x_284_);
                        v___x_452_ = lean_box(0);
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_285_) == 0 {
                    lean_del_object(v___x_287_);
                    lean_inc(v_a_283_);
                    v___x_289_ = l_Lean_Meta_getIntValue_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_289_) == 0 {
                        v_a_290_ = lean_ctor_get(v___x_289_, 0);
                        v_isSharedCheck_435_ = (!lean_is_exclusive(v___x_289_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v___x_292_ = v___x_289_;
                            v_isShared_293_ = v_isSharedCheck_435_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_290_);
                            lean_dec(v___x_289_);
                            v___x_292_ = lean_box(0);
                            v_isShared_293_ = v_isSharedCheck_435_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_436_ = lean_ctor_get(v___x_289_, 0);
                        v_isSharedCheck_443_ = (!lean_is_exclusive(v___x_289_)) as u8;
                        if v_isSharedCheck_443_ == 0 {
                            v___x_438_ = v___x_289_;
                            v_isShared_439_ = v_isSharedCheck_443_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_436_);
                            lean_dec(v___x_289_);
                            v___x_438_ = lean_box(0);
                            v_isShared_439_ = v_isSharedCheck_443_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_285_, 1);
                    lean_dec(v_a_283_);
                    v___x_444_ = 1;
                    v___x_445_ = lean_box((v___x_444_) as usize);
                    if v_isShared_288_ == 0 {
                        lean_ctor_set(v___x_287_, 0, v___x_445_);
                        v___x_447_ = v___x_287_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
                        v___x_447_ = v_reuseFailAlloc_448_;
                        state = 36;
                        continue;
                    }
                }
            }
            2 => {
                v___x_294_ = 1;
                if lean_obj_tag(v_a_290_) == 0 {
                    lean_del_object(v___x_292_);
                    lean_inc(v_a_283_);
                    v___x_295_ = l_Lean_Meta_getFinValue_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_295_) == 0 {
                        v_a_296_ = lean_ctor_get(v___x_295_, 0);
                        v_isSharedCheck_422_ = (!lean_is_exclusive(v___x_295_)) as u8;
                        if v_isSharedCheck_422_ == 0 {
                            v___x_298_ = v___x_295_;
                            v_isShared_299_ = v_isSharedCheck_422_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_296_);
                            lean_dec(v___x_295_);
                            v___x_298_ = lean_box(0);
                            v_isShared_299_ = v_isSharedCheck_422_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_423_ = lean_ctor_get(v___x_295_, 0);
                        v_isSharedCheck_430_ = (!lean_is_exclusive(v___x_295_)) as u8;
                        if v_isSharedCheck_430_ == 0 {
                            v___x_425_ = v___x_295_;
                            v_isShared_426_ = v_isSharedCheck_430_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_423_);
                            lean_dec(v___x_295_);
                            v___x_425_ = lean_box(0);
                            v_isShared_426_ = v_isSharedCheck_430_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_290_, 1);
                    lean_dec(v_a_283_);
                    v___x_431_ = lean_box((v___x_294_) as usize);
                    if v_isShared_293_ == 0 {
                        lean_ctor_set(v___x_292_, 0, v___x_431_);
                        v___x_433_ = v___x_292_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
                        v___x_433_ = v_reuseFailAlloc_434_;
                        state = 33;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_296_) == 0 {
                    lean_del_object(v___x_298_);
                    lean_inc(v_a_283_);
                    v___x_300_ = l_Lean_Meta_getBitVecValue_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_300_) == 0 {
                        v_a_301_ = lean_ctor_get(v___x_300_, 0);
                        v_isSharedCheck_409_ = (!lean_is_exclusive(v___x_300_)) as u8;
                        if v_isSharedCheck_409_ == 0 {
                            v___x_303_ = v___x_300_;
                            v_isShared_304_ = v_isSharedCheck_409_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_301_);
                            lean_dec(v___x_300_);
                            v___x_303_ = lean_box(0);
                            v_isShared_304_ = v_isSharedCheck_409_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_410_ = lean_ctor_get(v___x_300_, 0);
                        v_isSharedCheck_417_ = (!lean_is_exclusive(v___x_300_)) as u8;
                        if v_isSharedCheck_417_ == 0 {
                            v___x_412_ = v___x_300_;
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 28;
                            continue;
                        } else {
                            lean_inc(v_a_410_);
                            lean_dec(v___x_300_);
                            v___x_412_ = lean_box(0);
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_296_, 1);
                    lean_dec(v_a_283_);
                    v___x_418_ = lean_box((v___x_294_) as usize);
                    if v_isShared_299_ == 0 {
                        lean_ctor_set(v___x_298_, 0, v___x_418_);
                        v___x_420_ = v___x_298_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
                        v___x_420_ = v_reuseFailAlloc_421_;
                        state = 30;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_301_) == 0 {
                    lean_inc(v_a_283_);
                    v___x_305_ = l_Lean_Meta_getStringValue_x3f(v_a_283_);
                    if lean_obj_tag(v___x_305_) == 0 {
                        lean_del_object(v___x_303_);
                        lean_inc(v_a_283_);
                        v___x_306_ = l_Lean_Meta_getCharValue_x3f(
                            v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                        );
                        if lean_obj_tag(v___x_306_) == 0 {
                            v_a_307_ = lean_ctor_get(v___x_306_, 0);
                            v_isSharedCheck_392_ = (!lean_is_exclusive(v___x_306_)) as u8;
                            if v_isSharedCheck_392_ == 0 {
                                v___x_309_ = v___x_306_;
                                v_isShared_310_ = v_isSharedCheck_392_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_307_);
                                lean_dec(v___x_306_);
                                v___x_309_ = lean_box(0);
                                v_isShared_310_ = v_isSharedCheck_392_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_283_);
                            v_a_393_ = lean_ctor_get(v___x_306_, 0);
                            v_isSharedCheck_400_ = (!lean_is_exclusive(v___x_306_)) as u8;
                            if v_isSharedCheck_400_ == 0 {
                                v___x_395_ = v___x_306_;
                                v_isShared_396_ = v_isSharedCheck_400_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_393_);
                                lean_dec(v___x_306_);
                                v___x_395_ = lean_box(0);
                                v_isShared_396_ = v_isSharedCheck_400_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_305_, 1);
                        lean_dec(v_a_283_);
                        v___x_401_ = lean_box((v___x_294_) as usize);
                        if v_isShared_304_ == 0 {
                            lean_ctor_set(v___x_303_, 0, v___x_401_);
                            v___x_403_ = v___x_303_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
                            v___x_403_ = v_reuseFailAlloc_404_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_301_, 1);
                    lean_dec(v_a_283_);
                    v___x_405_ = lean_box((v___x_294_) as usize);
                    if v_isShared_304_ == 0 {
                        lean_ctor_set(v___x_303_, 0, v___x_405_);
                        v___x_407_ = v___x_303_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                        v___x_407_ = v_reuseFailAlloc_408_;
                        state = 27;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_307_) == 0 {
                    lean_del_object(v___x_309_);
                    lean_inc(v_a_283_);
                    v___x_311_ = l_Lean_Meta_getUInt8Value_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_311_) == 0 {
                        v_a_312_ = lean_ctor_get(v___x_311_, 0);
                        v_isSharedCheck_379_ = (!lean_is_exclusive(v___x_311_)) as u8;
                        if v_isSharedCheck_379_ == 0 {
                            v___x_314_ = v___x_311_;
                            v_isShared_315_ = v_isSharedCheck_379_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_312_);
                            lean_dec(v___x_311_);
                            v___x_314_ = lean_box(0);
                            v_isShared_315_ = v_isSharedCheck_379_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_380_ = lean_ctor_get(v___x_311_, 0);
                        v_isSharedCheck_387_ = (!lean_is_exclusive(v___x_311_)) as u8;
                        if v_isSharedCheck_387_ == 0 {
                            v___x_382_ = v___x_311_;
                            v_isShared_383_ = v_isSharedCheck_387_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_380_);
                            lean_dec(v___x_311_);
                            v___x_382_ = lean_box(0);
                            v_isShared_383_ = v_isSharedCheck_387_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_307_, 1);
                    lean_dec(v_a_283_);
                    v___x_388_ = lean_box((v___x_294_) as usize);
                    if v_isShared_310_ == 0 {
                        lean_ctor_set(v___x_309_, 0, v___x_388_);
                        v___x_390_ = v___x_309_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
                        v___x_390_ = v_reuseFailAlloc_391_;
                        state = 23;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_312_) == 0 {
                    lean_del_object(v___x_314_);
                    lean_inc(v_a_283_);
                    v___x_316_ = l_Lean_Meta_getUInt16Value_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_316_) == 0 {
                        v_a_317_ = lean_ctor_get(v___x_316_, 0);
                        v_isSharedCheck_366_ = (!lean_is_exclusive(v___x_316_)) as u8;
                        if v_isSharedCheck_366_ == 0 {
                            v___x_319_ = v___x_316_;
                            v_isShared_320_ = v_isSharedCheck_366_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_317_);
                            lean_dec(v___x_316_);
                            v___x_319_ = lean_box(0);
                            v_isShared_320_ = v_isSharedCheck_366_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_367_ = lean_ctor_get(v___x_316_, 0);
                        v_isSharedCheck_374_ = (!lean_is_exclusive(v___x_316_)) as u8;
                        if v_isSharedCheck_374_ == 0 {
                            v___x_369_ = v___x_316_;
                            v_isShared_370_ = v_isSharedCheck_374_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_367_);
                            lean_dec(v___x_316_);
                            v___x_369_ = lean_box(0);
                            v_isShared_370_ = v_isSharedCheck_374_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_312_, 1);
                    lean_dec(v_a_283_);
                    v___x_375_ = lean_box((v___x_294_) as usize);
                    if v_isShared_315_ == 0 {
                        lean_ctor_set(v___x_314_, 0, v___x_375_);
                        v___x_377_ = v___x_314_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
                        v___x_377_ = v_reuseFailAlloc_378_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v_a_317_) == 0 {
                    lean_del_object(v___x_319_);
                    lean_inc(v_a_283_);
                    v___x_321_ = l_Lean_Meta_getUInt32Value_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_321_) == 0 {
                        v_a_322_ = lean_ctor_get(v___x_321_, 0);
                        v_isSharedCheck_353_ = (!lean_is_exclusive(v___x_321_)) as u8;
                        if v_isSharedCheck_353_ == 0 {
                            v___x_324_ = v___x_321_;
                            v_isShared_325_ = v_isSharedCheck_353_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_322_);
                            lean_dec(v___x_321_);
                            v___x_324_ = lean_box(0);
                            v_isShared_325_ = v_isSharedCheck_353_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_283_);
                        v_a_354_ = lean_ctor_get(v___x_321_, 0);
                        v_isSharedCheck_361_ = (!lean_is_exclusive(v___x_321_)) as u8;
                        if v_isSharedCheck_361_ == 0 {
                            v___x_356_ = v___x_321_;
                            v_isShared_357_ = v_isSharedCheck_361_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_354_);
                            lean_dec(v___x_321_);
                            v___x_356_ = lean_box(0);
                            v_isShared_357_ = v_isSharedCheck_361_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_317_, 1);
                    lean_dec(v_a_283_);
                    v___x_362_ = lean_box((v___x_294_) as usize);
                    if v_isShared_320_ == 0 {
                        lean_ctor_set(v___x_319_, 0, v___x_362_);
                        v___x_364_ = v___x_319_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
                        v___x_364_ = v_reuseFailAlloc_365_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                if lean_obj_tag(v_a_322_) == 0 {
                    lean_del_object(v___x_324_);
                    v___x_326_ = l_Lean_Meta_getUInt64Value_x3f(
                        v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                    );
                    if lean_obj_tag(v___x_326_) == 0 {
                        v_a_327_ = lean_ctor_get(v___x_326_, 0);
                        v_isSharedCheck_340_ = (!lean_is_exclusive(v___x_326_)) as u8;
                        if v_isSharedCheck_340_ == 0 {
                            v___x_329_ = v___x_326_;
                            v_isShared_330_ = v_isSharedCheck_340_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_327_);
                            lean_dec(v___x_326_);
                            v___x_329_ = lean_box(0);
                            v_isShared_330_ = v_isSharedCheck_340_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_341_ = lean_ctor_get(v___x_326_, 0);
                        v_isSharedCheck_348_ = (!lean_is_exclusive(v___x_326_)) as u8;
                        if v_isSharedCheck_348_ == 0 {
                            v___x_343_ = v___x_326_;
                            v_isShared_344_ = v_isSharedCheck_348_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_341_);
                            lean_dec(v___x_326_);
                            v___x_343_ = lean_box(0);
                            v_isShared_344_ = v_isSharedCheck_348_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_322_, 1);
                    lean_dec(v_a_283_);
                    v___x_349_ = lean_box((v___x_294_) as usize);
                    if v_isShared_325_ == 0 {
                        lean_ctor_set(v___x_324_, 0, v___x_349_);
                        v___x_351_ = v___x_324_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
                        v___x_351_ = v_reuseFailAlloc_352_;
                        state = 14;
                        continue;
                    }
                }
            }
            9 => {
                if lean_obj_tag(v_a_327_) == 0 {
                    v___x_331_ = 0;
                    v___x_332_ = lean_box((v___x_331_) as usize);
                    if v_isShared_330_ == 0 {
                        lean_ctor_set(v___x_329_, 0, v___x_332_);
                        v___x_334_ = v___x_329_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
                        v___x_334_ = v_reuseFailAlloc_335_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_327_, 1);
                    v___x_336_ = lean_box((v___x_294_) as usize);
                    if v_isShared_330_ == 0 {
                        lean_ctor_set(v___x_329_, 0, v___x_336_);
                        v___x_338_ = v___x_329_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
                        v___x_338_ = v_reuseFailAlloc_339_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_334_;
            }
            11 => {
                return v___x_338_;
            }
            12 => {
                if v_isShared_344_ == 0 {
                    v___x_346_ = v___x_343_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
                    v___x_346_ = v_reuseFailAlloc_347_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_346_;
            }
            14 => {
                return v___x_351_;
            }
            15 => {
                if v_isShared_357_ == 0 {
                    v___x_359_ = v___x_356_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
                    v___x_359_ = v_reuseFailAlloc_360_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_359_;
            }
            17 => {
                return v___x_364_;
            }
            18 => {
                if v_isShared_370_ == 0 {
                    v___x_372_ = v___x_369_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
                    v___x_372_ = v_reuseFailAlloc_373_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_372_;
            }
            20 => {
                return v___x_377_;
            }
            21 => {
                if v_isShared_383_ == 0 {
                    v___x_385_ = v___x_382_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
                    v___x_385_ = v_reuseFailAlloc_386_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_385_;
            }
            23 => {
                return v___x_390_;
            }
            24 => {
                if v_isShared_396_ == 0 {
                    v___x_398_ = v___x_395_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
                    v___x_398_ = v_reuseFailAlloc_399_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_398_;
            }
            26 => {
                return v___x_403_;
            }
            27 => {
                return v___x_407_;
            }
            28 => {
                if v_isShared_413_ == 0 {
                    v___x_415_ = v___x_412_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
                    v___x_415_ = v_reuseFailAlloc_416_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_415_;
            }
            30 => {
                return v___x_420_;
            }
            31 => {
                if v_isShared_426_ == 0 {
                    v___x_428_ = v___x_425_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
                    v___x_428_ = v_reuseFailAlloc_429_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_428_;
            }
            33 => {
                return v___x_433_;
            }
            34 => {
                if v_isShared_439_ == 0 {
                    v___x_441_ = v___x_438_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
                    v___x_441_ = v_reuseFailAlloc_442_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_441_;
            }
            36 => {
                return v___x_447_;
            }
            37 => {
                if v_isShared_453_ == 0 {
                    v___x_455_ = v___x_452_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
                    v___x_455_ = v_reuseFailAlloc_456_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isMatchValue___boxed(
    mut v_e_458_: *mut LeanObject,
    mut v_a_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
    mut v_a_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_464_: *mut LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Lean_Meta_isMatchValue(v_e_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
    lean_dec(v_a_462_);
    lean_dec_ref(v_a_461_);
    lean_dec(v_a_460_);
    lean_dec_ref(v_a_459_);
    return v_res_464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_Value(builtin);
}
