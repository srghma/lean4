// Lean compiler output
// Module: Lake.Util.Lift
// Imports: Init.System.IO
use crate::r#gen::Init::Prelude::l_liftM;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(
    mut v_inst_216_: *mut LeanObject,
    mut v_00_u03b1_217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v_throw_218_ = lean_ctor_get(v_inst_216_, 0);
    lean_inc(v_throw_218_);
    lean_dec_ref(v_inst_216_);
    v___x_219_ = lean_box(0);
    v___x_220_ = lean_apply_2(v_throw_218_, lean_box(0), v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(
    mut v_inst_221_: *mut LeanObject,
    mut v_00_u03b1_222_: *mut LeanObject,
    mut v___y_223_: *mut LeanObject,
    mut v___y_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_225_ = lean_ctor_get(v_inst_221_, 1);
    lean_inc(v_tryCatch_225_);
    lean_dec_ref(v_inst_221_);
    v___x_226_ = lean_apply_3(v_tryCatch_225_, lean_box(0), v___y_223_, v___y_224_);
    return v___x_226_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(
    mut v_inst_227_: *mut LeanObject,
    mut v_inst_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_229_ = lean_ctor_get(v_inst_227_, 0);
    lean_inc_ref(v_inst_228_);
    v___f_230_ = lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_230_, 0, v_inst_228_);
    v___f_231_ = lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_231_, 0, v_inst_228_);
    lean_inc_ref(v_toApplicative_229_);
    v___x_232_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_232_, 0, v_toApplicative_229_);
    lean_ctor_set(v___x_232_, 1, v___f_230_);
    lean_ctor_set(v___x_232_, 2, v___f_231_);
    return v___x_232_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(
    mut v_inst_233_: *mut LeanObject,
    mut v_inst_234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_235_: *mut LeanObject = core::ptr::null_mut();
    v_res_235_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_233_, v_inst_234_);
    lean_dec_ref(v_inst_233_);
    return v_res_235_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(
    mut v_m_236_: *mut LeanObject,
    mut v_inst_237_: *mut LeanObject,
    mut v_inst_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    v___x_239_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_237_, v_inst_238_);
    return v___x_239_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(
    mut v_m_240_: *mut LeanObject,
    mut v_inst_241_: *mut LeanObject,
    mut v_inst_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_243_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(v_m_240_, v_inst_241_, v_inst_242_);
    lean_dec_ref(v_inst_241_);
    return v_res_243_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(
    mut v_inst_244_: *mut LeanObject,
    mut v_00_u03b1_245_: *mut LeanObject,
    mut v___y_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = lean_apply_2(v_inst_244_, lean_box(0), v___y_246_);
    return v___x_247_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg(
    mut v_inst_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_249_: *mut LeanObject = core::ptr::null_mut();
    v___f_249_ = lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_249_, 0, v_inst_248_);
    return v___f_249_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake(
    mut v_00_u03b1_250_: *mut LeanObject,
    mut v_00_u03b2_251_: *mut LeanObject,
    mut v_inst_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_253_: *mut LeanObject = core::ptr::null_mut();
    v___f_253_ = lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_253_, 0, v_inst_252_);
    return v___f_253_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(
    mut v_inst_254_: *mut LeanObject,
    mut v_00_u03b1_255_: *mut LeanObject,
    mut v_act_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    v___x_257_ = lean_apply_2(v_inst_254_, lean_box(0), v_act_256_);
    return v___x_257_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg(
    mut v_inst_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_259_: *mut LeanObject = core::ptr::null_mut();
    v___f_259_ = lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_259_, 0, v_inst_258_);
    return v___f_259_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake(
    mut v_m_260_: *mut LeanObject,
    mut v_inst_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_262_: *mut LeanObject = core::ptr::null_mut();
    v___f_262_ = lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_262_, 0, v_inst_261_);
    return v___f_262_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(
    mut v_failure_263_: *mut LeanObject,
    mut v_toPure_264_: *mut LeanObject,
    mut v_00_u03b1_265_: *mut LeanObject,
    mut v_x_266_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_264_);
        v___x_267_ = lean_apply_1(v_failure_263_, lean_box(0));
        return v___x_267_;
    } else {
        let mut v_val_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_failure_263_);
        v_val_268_ = lean_ctor_get(v_x_266_, 0);
        lean_inc(v_val_268_);
        lean_dec_ref_known(v_x_266_, 1);
        v___x_269_ = lean_apply_2(v_toPure_264_, lean_box(0), v_val_268_);
        return v___x_269_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(
    mut v_inst_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failure_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_274_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_271_ = lean_ctor_get(v_inst_270_, 0);
    lean_inc_ref(v_toApplicative_271_);
    v_failure_272_ = lean_ctor_get(v_inst_270_, 1);
    lean_inc(v_failure_272_);
    lean_dec_ref(v_inst_270_);
    v_toPure_273_ = lean_ctor_get(v_toApplicative_271_, 1);
    lean_inc(v_toPure_273_);
    lean_dec_ref(v_toApplicative_271_);
    v___f_274_ = lean_alloc_closure(
        l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_274_, 0, v_failure_272_);
    lean_closure_set(v___f_274_, 1, v_toPure_273_);
    return v___f_274_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake(
    mut v_m_275_: *mut LeanObject,
    mut v_inst_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_276_);
    return v___x_277_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_00_u03b1_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_281_) == 0 {
        let mut v_a_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_throw_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_279_);
        v_a_282_ = lean_ctor_get(v_x_281_, 0);
        lean_inc(v_a_282_);
        lean_dec_ref_known(v_x_281_, 1);
        v_throw_283_ = lean_ctor_get(v_inst_278_, 0);
        lean_inc(v_throw_283_);
        lean_dec_ref(v_inst_278_);
        v___x_284_ = lean_apply_2(v_throw_283_, lean_box(0), v_a_282_);
        return v___x_284_;
    } else {
        let mut v_a_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_278_);
        v_a_285_ = lean_ctor_get(v_x_281_, 0);
        lean_inc(v_a_285_);
        lean_dec_ref_known(v_x_281_, 1);
        v___x_286_ = lean_apply_2(v_inst_279_, lean_box(0), v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(
    mut v_inst_287_: *mut LeanObject,
    mut v_inst_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_289_: *mut LeanObject = core::ptr::null_mut();
    v___f_289_ = lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_289_, 0, v_inst_288_);
    lean_closure_set(v___f_289_, 1, v_inst_287_);
    return v___f_289_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(
    mut v_m_290_: *mut LeanObject,
    mut v_00_u03b5_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_294_: *mut LeanObject = core::ptr::null_mut();
    v___f_294_ = lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_294_, 0, v_inst_293_);
    lean_closure_set(v___f_294_, 1, v_inst_292_);
    return v___f_294_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0(
    mut v_act_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_____do__lift_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_apply_1(v_act_295_, v_____do__lift_297_);
    v___x_299_ = lean_apply_2(v_inst_296_, lean_box(0), v___x_298_);
    return v___x_299_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1(
    mut v_inst_300_: *mut LeanObject,
    mut v_toBind_301_: *mut LeanObject,
    mut v_inst_302_: *mut LeanObject,
    mut v_00_u03b1_303_: *mut LeanObject,
    mut v_act_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    v___f_305_ = lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_305_, 0, v_act_304_);
    lean_closure_set(v___f_305_, 1, v_inst_300_);
    v___x_306_ = lean_apply_4(
        v_toBind_301_,
        lean_box(0),
        lean_box(0),
        v_inst_302_,
        v___f_305_,
    );
    return v___x_306_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
    mut v_inst_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_311_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_310_ = lean_ctor_get(v_inst_307_, 1);
    lean_inc(v_toBind_310_);
    lean_dec_ref(v_inst_307_);
    v___f_311_ = lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_311_, 0, v_inst_309_);
    lean_closure_set(v___f_311_, 1, v_toBind_310_);
    lean_closure_set(v___f_311_, 2, v_inst_308_);
    return v___f_311_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake(
    mut v_m_312_: *mut LeanObject,
    mut v_00_u03c1_313_: *mut LeanObject,
    mut v_n_314_: *mut LeanObject,
    mut v_inst_315_: *mut LeanObject,
    mut v_inst_316_: *mut LeanObject,
    mut v_inst_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_318_ = l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
        v_inst_315_,
        v_inst_316_,
        v_inst_317_,
    );
    return v___x_318_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(
    mut v_toPure_319_: *mut LeanObject,
    mut v_fst_320_: *mut LeanObject,
    mut v_____r_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_apply_2(v_toPure_319_, lean_box(0), v_fst_320_);
    return v___x_322_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(
    mut v_inst_323_: *mut LeanObject,
    mut v_toPure_324_: *mut LeanObject,
    mut v_toBind_325_: *mut LeanObject,
    mut v_____x_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v_fst_327_ = lean_ctor_get(v_____x_326_, 0);
    lean_inc(v_fst_327_);
    v_snd_328_ = lean_ctor_get(v_____x_326_, 1);
    lean_inc(v_snd_328_);
    lean_dec_ref(v_____x_326_);
    v_set_329_ = lean_ctor_get(v_inst_323_, 1);
    lean_inc(v_set_329_);
    lean_dec_ref(v_inst_323_);
    v___f_330_ = lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_330_, 0, v_toPure_324_);
    lean_closure_set(v___f_330_, 1, v_fst_327_);
    v___x_331_ = lean_apply_1(v_set_329_, v_snd_328_);
    v___x_332_ = lean_apply_4(
        v_toBind_325_,
        lean_box(0),
        lean_box(0),
        v___x_331_,
        v___f_330_,
    );
    return v___x_332_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(
    mut v_act_333_: *mut LeanObject,
    mut v_inst_334_: *mut LeanObject,
    mut v_toBind_335_: *mut LeanObject,
    mut v___f_336_: *mut LeanObject,
    mut v_____do__lift_337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_338_ = lean_apply_1(v_act_333_, v_____do__lift_337_);
    v___x_339_ = lean_apply_2(v_inst_334_, lean_box(0), v___x_338_);
    v___x_340_ = lean_apply_4(
        v_toBind_335_,
        lean_box(0),
        lean_box(0),
        v___x_339_,
        v___f_336_,
    );
    return v___x_340_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(
    mut v_inst_341_: *mut LeanObject,
    mut v_inst_342_: *mut LeanObject,
    mut v_toBind_343_: *mut LeanObject,
    mut v___f_344_: *mut LeanObject,
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_act_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v_get_347_ = lean_ctor_get(v_inst_341_, 0);
    lean_inc(v_get_347_);
    lean_dec_ref(v_inst_341_);
    lean_inc(v_toBind_343_);
    v___f_348_ = lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_348_, 0, v_act_346_);
    lean_closure_set(v___f_348_, 1, v_inst_342_);
    lean_closure_set(v___f_348_, 2, v_toBind_343_);
    lean_closure_set(v___f_348_, 3, v___f_344_);
    v___x_349_ = lean_apply_4(
        v_toBind_343_,
        lean_box(0),
        lean_box(0),
        v_get_347_,
        v___f_348_,
    );
    return v___x_349_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
    mut v_inst_350_: *mut LeanObject,
    mut v_inst_351_: *mut LeanObject,
    mut v_inst_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_357_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_353_ = lean_ctor_get(v_inst_350_, 0);
    lean_inc_ref(v_toApplicative_353_);
    v_toBind_354_ = lean_ctor_get(v_inst_350_, 1);
    lean_inc_n(v_toBind_354_, 2);
    lean_dec_ref(v_inst_350_);
    v_toPure_355_ = lean_ctor_get(v_toApplicative_353_, 1);
    lean_inc(v_toPure_355_);
    lean_dec_ref(v_toApplicative_353_);
    lean_inc_ref(v_inst_351_);
    v___f_356_ = lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_356_, 0, v_inst_351_);
    lean_closure_set(v___f_356_, 1, v_toPure_355_);
    lean_closure_set(v___f_356_, 2, v_toBind_354_);
    v___f_357_ = lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3
            as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_357_, 0, v_inst_351_);
    lean_closure_set(v___f_357_, 1, v_inst_352_);
    lean_closure_set(v___f_357_, 2, v_toBind_354_);
    lean_closure_set(v___f_357_, 3, v___f_356_);
    return v___f_357_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(
    mut v_m_358_: *mut LeanObject,
    mut v_00_u03c3_359_: *mut LeanObject,
    mut v_n_360_: *mut LeanObject,
    mut v_inst_361_: *mut LeanObject,
    mut v_inst_362_: *mut LeanObject,
    mut v_inst_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
        v_inst_361_,
        v_inst_362_,
        v_inst_363_,
    );
    return v___x_364_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(
    mut v_inst_365_: *mut LeanObject,
    mut v___x_366_: *mut LeanObject,
    mut v_toBind_367_: *mut LeanObject,
    mut v_00_u03b1_368_: *mut LeanObject,
    mut v_act_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    v___x_370_ = lean_apply_2(v_inst_365_, lean_box(0), v_act_369_);
    v___x_371_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_371_, 0, lean_box(0));
    lean_closure_set(v___x_371_, 1, lean_box(0));
    lean_closure_set(v___x_371_, 2, v___x_366_);
    lean_closure_set(v___x_371_, 3, lean_box(0));
    v___x_372_ = lean_apply_4(
        v_toBind_367_,
        lean_box(0),
        lean_box(0),
        v___x_370_,
        v___x_371_,
    );
    return v___x_372_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
    mut v_inst_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_376_ = lean_ctor_get(v_inst_373_, 1);
    lean_inc(v_toBind_376_);
    lean_dec_ref(v_inst_373_);
    v___x_377_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_374_);
    v___f_378_ = lean_alloc_closure(
        l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_378_, 0, v_inst_375_);
    lean_closure_set(v___f_378_, 1, v___x_377_);
    lean_closure_set(v___f_378_, 2, v_toBind_376_);
    return v___f_378_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(
    mut v_m_379_: *mut LeanObject,
    mut v_n_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_inst_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
        v_inst_381_,
        v_inst_382_,
        v_inst_383_,
    );
    return v___x_384_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_385_: *mut LeanObject,
    mut v___f_386_: *mut LeanObject,
    mut v_toBind_387_: *mut LeanObject,
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_act_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = lean_apply_2(v_inst_385_, lean_box(0), v_act_389_);
    v___x_391_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_391_, 0, lean_box(0));
    lean_closure_set(v___x_391_, 1, lean_box(0));
    lean_closure_set(v___x_391_, 2, v___f_386_);
    lean_closure_set(v___x_391_, 3, lean_box(0));
    v___x_392_ = lean_apply_4(
        v_toBind_387_,
        lean_box(0),
        lean_box(0),
        v___x_390_,
        v___x_391_,
    );
    return v___x_392_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
    mut v_inst_393_: *mut LeanObject,
    mut v_inst_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_400_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_396_ = lean_ctor_get(v_inst_393_, 0);
    lean_inc_ref(v_toApplicative_396_);
    v_toBind_397_ = lean_ctor_get(v_inst_393_, 1);
    lean_inc(v_toBind_397_);
    lean_dec_ref(v_inst_393_);
    v_toPure_398_ = lean_ctor_get(v_toApplicative_396_, 1);
    lean_inc(v_toPure_398_);
    lean_dec_ref(v_toApplicative_396_);
    v___f_399_ = lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_399_, 0, v_inst_394_);
    lean_closure_set(v___f_399_, 1, v_toPure_398_);
    v___f_400_ = lean_alloc_closure(
        l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_400_, 0, v_inst_395_);
    lean_closure_set(v___f_400_, 1, v___f_399_);
    lean_closure_set(v___f_400_, 2, v_toBind_397_);
    return v___f_400_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(
    mut v_m_401_: *mut LeanObject,
    mut v_00_u03b5_402_: *mut LeanObject,
    mut v_n_403_: *mut LeanObject,
    mut v_inst_404_: *mut LeanObject,
    mut v_inst_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
        v_inst_404_,
        v_inst_405_,
        v_inst_406_,
    );
    return v___x_407_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(
    mut v_inst_408_: *mut LeanObject,
    mut v___f_409_: *mut LeanObject,
    mut v_toBind_410_: *mut LeanObject,
    mut v_00_u03b1_411_: *mut LeanObject,
    mut v_act_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_413_, 0, lean_box(0));
    lean_closure_set(v___x_413_, 1, lean_box(0));
    lean_closure_set(v___x_413_, 2, v_act_412_);
    v___x_414_ = lean_apply_2(v_inst_408_, lean_box(0), v___x_413_);
    v___x_415_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_415_, 0, lean_box(0));
    lean_closure_set(v___x_415_, 1, lean_box(0));
    lean_closure_set(v___x_415_, 2, v___f_409_);
    lean_closure_set(v___x_415_, 3, lean_box(0));
    v___x_416_ = lean_apply_4(
        v_toBind_410_,
        lean_box(0),
        lean_box(0),
        v___x_414_,
        v___x_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
    mut v_inst_417_: *mut LeanObject,
    mut v_inst_418_: *mut LeanObject,
    mut v_inst_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_420_ = lean_ctor_get(v_inst_417_, 0);
    lean_inc_ref(v_toApplicative_420_);
    v_toBind_421_ = lean_ctor_get(v_inst_417_, 1);
    lean_inc(v_toBind_421_);
    lean_dec_ref(v_inst_417_);
    v_toPure_422_ = lean_ctor_get(v_toApplicative_420_, 1);
    lean_inc(v_toPure_422_);
    lean_dec_ref(v_toApplicative_420_);
    v___f_423_ = lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_423_, 0, v_inst_418_);
    lean_closure_set(v___f_423_, 1, v_toPure_422_);
    v___f_424_ = lean_alloc_closure(
        l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_424_, 0, v_inst_419_);
    lean_closure_set(v___f_424_, 1, v___f_423_);
    lean_closure_set(v___f_424_, 2, v_toBind_421_);
    return v___f_424_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(
    mut v_m_425_: *mut LeanObject,
    mut v_00_u03b5_426_: *mut LeanObject,
    mut v_inst_427_: *mut LeanObject,
    mut v_inst_428_: *mut LeanObject,
    mut v_inst_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
        v_inst_427_,
        v_inst_428_,
        v_inst_429_,
    );
    return v___x_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Lift(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Lift(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Lift(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Lift(builtin);
}
