// Lean compiler output
// Module: Lake.Util.Lift
// Imports: Init.System.IO
use crate::r#gen::Init::Prelude::l_liftM;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(
    mut v_inst_216_: *mut leanh::LeanObject,
    mut v_00_u03b1_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_218_ = leanh::lean_ctor_get(v_inst_216_, 0);
    leanh::lean_inc(v_throw_218_);
    leanh::lean_dec_ref(v_inst_216_);
    v___x_219_ = leanh::lean_box(0);
    v___x_220_ = leanh::lean_apply_2(v_throw_218_, leanh::lean_box(0), v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(
    mut v_inst_221_: *mut leanh::LeanObject,
    mut v_00_u03b1_222_: *mut leanh::LeanObject,
    mut v___y_223_: *mut leanh::LeanObject,
    mut v___y_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_225_ = leanh::lean_ctor_get(v_inst_221_, 1);
    leanh::lean_inc(v_tryCatch_225_);
    leanh::lean_dec_ref(v_inst_221_);
    v___x_226_ = leanh::lean_apply_3(
        v_tryCatch_225_,
        leanh::lean_box(0),
        v___y_223_,
        v___y_224_,
    );
    return v___x_226_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_inst_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_229_ = leanh::lean_ctor_get(v_inst_227_, 0);
    leanh::lean_inc_ref(v_inst_228_);
    v___f_230_ = leanh::lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_230_, 0, v_inst_228_);
    v___f_231_ = leanh::lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_231_, 0, v_inst_228_);
    leanh::lean_inc_ref(v_toApplicative_229_);
    v___x_232_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_232_, 0, v_toApplicative_229_);
    leanh::lean_ctor_set(v___x_232_, 1, v___f_230_);
    leanh::lean_ctor_set(v___x_232_, 2, v___f_231_);
    return v___x_232_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(
    mut v_inst_233_: *mut leanh::LeanObject,
    mut v_inst_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_233_, v_inst_234_);
    leanh::lean_dec_ref(v_inst_233_);
    return v_res_235_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(
    mut v_m_236_: *mut leanh::LeanObject,
    mut v_inst_237_: *mut leanh::LeanObject,
    mut v_inst_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_237_, v_inst_238_);
    return v___x_239_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(
    mut v_m_240_: *mut leanh::LeanObject,
    mut v_inst_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(v_m_240_, v_inst_241_, v_inst_242_);
    leanh::lean_dec_ref(v_inst_241_);
    return v_res_243_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_00_u03b1_245_: *mut leanh::LeanObject,
    mut v___y_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = leanh::lean_apply_2(v_inst_244_, leanh::lean_box(0), v___y_246_);
    return v___x_247_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg(
    mut v_inst_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_249_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_249_, 0, v_inst_248_);
    return v___f_249_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake(
    mut v_00_u03b1_250_: *mut leanh::LeanObject,
    mut v_00_u03b2_251_: *mut leanh::LeanObject,
    mut v_inst_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_253_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_253_, 0, v_inst_252_);
    return v___f_253_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(
    mut v_inst_254_: *mut leanh::LeanObject,
    mut v_00_u03b1_255_: *mut leanh::LeanObject,
    mut v_act_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = leanh::lean_apply_2(v_inst_254_, leanh::lean_box(0), v_act_256_);
    return v___x_257_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg(
    mut v_inst_258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_259_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_259_, 0, v_inst_258_);
    return v___f_259_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake(
    mut v_m_260_: *mut leanh::LeanObject,
    mut v_inst_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_262_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_262_, 0, v_inst_261_);
    return v___f_262_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(
    mut v_failure_263_: *mut leanh::LeanObject,
    mut v_toPure_264_: *mut leanh::LeanObject,
    mut v_00_u03b1_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_264_);
        v___x_267_ = leanh::lean_apply_1(v_failure_263_, leanh::lean_box(0));
        return v___x_267_;
    } else {
        let mut v_val_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_failure_263_);
        v_val_268_ = leanh::lean_ctor_get(v_x_266_, 0);
        leanh::lean_inc(v_val_268_);
        leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_269_ =
            leanh::lean_apply_2(v_toPure_264_, leanh::lean_box(0), v_val_268_);
        return v___x_269_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(
    mut v_inst_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_271_ = leanh::lean_ctor_get(v_inst_270_, 0);
    leanh::lean_inc_ref(v_toApplicative_271_);
    v_failure_272_ = leanh::lean_ctor_get(v_inst_270_, 1);
    leanh::lean_inc(v_failure_272_);
    leanh::lean_dec_ref(v_inst_270_);
    v_toPure_273_ = leanh::lean_ctor_get(v_toApplicative_271_, 1);
    leanh::lean_inc(v_toPure_273_);
    leanh::lean_dec_ref(v_toApplicative_271_);
    v___f_274_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_274_, 0, v_failure_272_);
    leanh::lean_closure_set(v___f_274_, 1, v_toPure_273_);
    return v___f_274_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake(
    mut v_m_275_: *mut leanh::LeanObject,
    mut v_inst_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_276_);
    return v___x_277_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_inst_279_: *mut leanh::LeanObject,
    mut v_00_u03b1_280_: *mut leanh::LeanObject,
    mut v_x_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_281_) == 0 {
        let mut v_a_282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_throw_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_279_);
        v_a_282_ = leanh::lean_ctor_get(v_x_281_, 0);
        leanh::lean_inc(v_a_282_);
        leanh::lean_dec_ref_known(v_x_281_, 1);
        v_throw_283_ = leanh::lean_ctor_get(v_inst_278_, 0);
        leanh::lean_inc(v_throw_283_);
        leanh::lean_dec_ref(v_inst_278_);
        v___x_284_ = leanh::lean_apply_2(v_throw_283_, leanh::lean_box(0), v_a_282_);
        return v___x_284_;
    } else {
        let mut v_a_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_278_);
        v_a_285_ = leanh::lean_ctor_get(v_x_281_, 0);
        leanh::lean_inc(v_a_285_);
        leanh::lean_dec_ref_known(v_x_281_, 1);
        v___x_286_ = leanh::lean_apply_2(v_inst_279_, leanh::lean_box(0), v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_inst_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_289_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_289_, 0, v_inst_288_);
    leanh::lean_closure_set(v___f_289_, 1, v_inst_287_);
    return v___f_289_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(
    mut v_m_290_: *mut leanh::LeanObject,
    mut v_00_u03b5_291_: *mut leanh::LeanObject,
    mut v_inst_292_: *mut leanh::LeanObject,
    mut v_inst_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_294_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_294_, 0, v_inst_293_);
    leanh::lean_closure_set(v___f_294_, 1, v_inst_292_);
    return v___f_294_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0(
    mut v_act_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_____do__lift_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = leanh::lean_apply_1(v_act_295_, v_____do__lift_297_);
    v___x_299_ = leanh::lean_apply_2(v_inst_296_, leanh::lean_box(0), v___x_298_);
    return v___x_299_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1(
    mut v_inst_300_: *mut leanh::LeanObject,
    mut v_toBind_301_: *mut leanh::LeanObject,
    mut v_inst_302_: *mut leanh::LeanObject,
    mut v_00_u03b1_303_: *mut leanh::LeanObject,
    mut v_act_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_305_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_305_, 0, v_act_304_);
    leanh::lean_closure_set(v___f_305_, 1, v_inst_300_);
    v___x_306_ = leanh::lean_apply_4(
        v_toBind_301_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_302_,
        v___f_305_,
    );
    return v___x_306_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
    mut v_inst_307_: *mut leanh::LeanObject,
    mut v_inst_308_: *mut leanh::LeanObject,
    mut v_inst_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_310_ = leanh::lean_ctor_get(v_inst_307_, 1);
    leanh::lean_inc(v_toBind_310_);
    leanh::lean_dec_ref(v_inst_307_);
    v___f_311_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_311_, 0, v_inst_309_);
    leanh::lean_closure_set(v___f_311_, 1, v_toBind_310_);
    leanh::lean_closure_set(v___f_311_, 2, v_inst_308_);
    return v___f_311_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake(
    mut v_m_312_: *mut leanh::LeanObject,
    mut v_00_u03c1_313_: *mut leanh::LeanObject,
    mut v_n_314_: *mut leanh::LeanObject,
    mut v_inst_315_: *mut leanh::LeanObject,
    mut v_inst_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
        v_inst_315_,
        v_inst_316_,
        v_inst_317_,
    );
    return v___x_318_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(
    mut v_toPure_319_: *mut leanh::LeanObject,
    mut v_fst_320_: *mut leanh::LeanObject,
    mut v_____r_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = leanh::lean_apply_2(v_toPure_319_, leanh::lean_box(0), v_fst_320_);
    return v___x_322_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_toPure_324_: *mut leanh::LeanObject,
    mut v_toBind_325_: *mut leanh::LeanObject,
    mut v_____x_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_327_ = leanh::lean_ctor_get(v_____x_326_, 0);
    leanh::lean_inc(v_fst_327_);
    v_snd_328_ = leanh::lean_ctor_get(v_____x_326_, 1);
    leanh::lean_inc(v_snd_328_);
    leanh::lean_dec_ref(v_____x_326_);
    v_set_329_ = leanh::lean_ctor_get(v_inst_323_, 1);
    leanh::lean_inc(v_set_329_);
    leanh::lean_dec_ref(v_inst_323_);
    v___f_330_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_330_, 0, v_toPure_324_);
    leanh::lean_closure_set(v___f_330_, 1, v_fst_327_);
    v___x_331_ = leanh::lean_apply_1(v_set_329_, v_snd_328_);
    v___x_332_ = leanh::lean_apply_4(
        v_toBind_325_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_331_,
        v___f_330_,
    );
    return v___x_332_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(
    mut v_act_333_: *mut leanh::LeanObject,
    mut v_inst_334_: *mut leanh::LeanObject,
    mut v_toBind_335_: *mut leanh::LeanObject,
    mut v___f_336_: *mut leanh::LeanObject,
    mut v_____do__lift_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = leanh::lean_apply_1(v_act_333_, v_____do__lift_337_);
    v___x_339_ = leanh::lean_apply_2(v_inst_334_, leanh::lean_box(0), v___x_338_);
    v___x_340_ = leanh::lean_apply_4(
        v_toBind_335_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_339_,
        v___f_336_,
    );
    return v___x_340_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_inst_342_: *mut leanh::LeanObject,
    mut v_toBind_343_: *mut leanh::LeanObject,
    mut v___f_344_: *mut leanh::LeanObject,
    mut v_00_u03b1_345_: *mut leanh::LeanObject,
    mut v_act_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_get_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_get_347_ = leanh::lean_ctor_get(v_inst_341_, 0);
    leanh::lean_inc(v_get_347_);
    leanh::lean_dec_ref(v_inst_341_);
    leanh::lean_inc(v_toBind_343_);
    v___f_348_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_348_, 0, v_act_346_);
    leanh::lean_closure_set(v___f_348_, 1, v_inst_342_);
    leanh::lean_closure_set(v___f_348_, 2, v_toBind_343_);
    leanh::lean_closure_set(v___f_348_, 3, v___f_344_);
    v___x_349_ = leanh::lean_apply_4(
        v_toBind_343_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_get_347_,
        v___f_348_,
    );
    return v___x_349_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
    mut v_inst_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_inst_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_353_ = leanh::lean_ctor_get(v_inst_350_, 0);
    leanh::lean_inc_ref(v_toApplicative_353_);
    v_toBind_354_ = leanh::lean_ctor_get(v_inst_350_, 1);
    leanh::lean_inc_n(v_toBind_354_, 2);
    leanh::lean_dec_ref(v_inst_350_);
    v_toPure_355_ = leanh::lean_ctor_get(v_toApplicative_353_, 1);
    leanh::lean_inc(v_toPure_355_);
    leanh::lean_dec_ref(v_toApplicative_353_);
    leanh::lean_inc_ref(v_inst_351_);
    v___f_356_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_356_, 0, v_inst_351_);
    leanh::lean_closure_set(v___f_356_, 1, v_toPure_355_);
    leanh::lean_closure_set(v___f_356_, 2, v_toBind_354_);
    v___f_357_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3
            as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_357_, 0, v_inst_351_);
    leanh::lean_closure_set(v___f_357_, 1, v_inst_352_);
    leanh::lean_closure_set(v___f_357_, 2, v_toBind_354_);
    leanh::lean_closure_set(v___f_357_, 3, v___f_356_);
    return v___f_357_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(
    mut v_m_358_: *mut leanh::LeanObject,
    mut v_00_u03c3_359_: *mut leanh::LeanObject,
    mut v_n_360_: *mut leanh::LeanObject,
    mut v_inst_361_: *mut leanh::LeanObject,
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_inst_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
        v_inst_361_,
        v_inst_362_,
        v_inst_363_,
    );
    return v___x_364_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v___x_366_: *mut leanh::LeanObject,
    mut v_toBind_367_: *mut leanh::LeanObject,
    mut v_00_u03b1_368_: *mut leanh::LeanObject,
    mut v_act_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = leanh::lean_apply_2(v_inst_365_, leanh::lean_box(0), v_act_369_);
    v___x_371_ = leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_371_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_371_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_371_, 2, v___x_366_);
    leanh::lean_closure_set(v___x_371_, 3, leanh::lean_box(0));
    v___x_372_ = leanh::lean_apply_4(
        v_toBind_367_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_370_,
        v___x_371_,
    );
    return v___x_372_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_376_ = leanh::lean_ctor_get(v_inst_373_, 1);
    leanh::lean_inc(v_toBind_376_);
    leanh::lean_dec_ref(v_inst_373_);
    v___x_377_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_374_);
    v___f_378_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_378_, 0, v_inst_375_);
    leanh::lean_closure_set(v___f_378_, 1, v___x_377_);
    leanh::lean_closure_set(v___f_378_, 2, v_toBind_376_);
    return v___f_378_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(
    mut v_m_379_: *mut leanh::LeanObject,
    mut v_n_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_inst_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
        v_inst_381_,
        v_inst_382_,
        v_inst_383_,
    );
    return v___x_384_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v___f_386_: *mut leanh::LeanObject,
    mut v_toBind_387_: *mut leanh::LeanObject,
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_act_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = leanh::lean_apply_2(v_inst_385_, leanh::lean_box(0), v_act_389_);
    v___x_391_ = leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_391_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_391_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_391_, 2, v___f_386_);
    leanh::lean_closure_set(v___x_391_, 3, leanh::lean_box(0));
    v___x_392_ = leanh::lean_apply_4(
        v_toBind_387_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_390_,
        v___x_391_,
    );
    return v___x_392_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
    mut v_inst_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_396_ = leanh::lean_ctor_get(v_inst_393_, 0);
    leanh::lean_inc_ref(v_toApplicative_396_);
    v_toBind_397_ = leanh::lean_ctor_get(v_inst_393_, 1);
    leanh::lean_inc(v_toBind_397_);
    leanh::lean_dec_ref(v_inst_393_);
    v_toPure_398_ = leanh::lean_ctor_get(v_toApplicative_396_, 1);
    leanh::lean_inc(v_toPure_398_);
    leanh::lean_dec_ref(v_toApplicative_396_);
    v___f_399_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_399_, 0, v_inst_394_);
    leanh::lean_closure_set(v___f_399_, 1, v_toPure_398_);
    v___f_400_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_400_, 0, v_inst_395_);
    leanh::lean_closure_set(v___f_400_, 1, v___f_399_);
    leanh::lean_closure_set(v___f_400_, 2, v_toBind_397_);
    return v___f_400_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(
    mut v_m_401_: *mut leanh::LeanObject,
    mut v_00_u03b5_402_: *mut leanh::LeanObject,
    mut v_n_403_: *mut leanh::LeanObject,
    mut v_inst_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
        v_inst_404_,
        v_inst_405_,
        v_inst_406_,
    );
    return v___x_407_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(
    mut v_inst_408_: *mut leanh::LeanObject,
    mut v___f_409_: *mut leanh::LeanObject,
    mut v_toBind_410_: *mut leanh::LeanObject,
    mut v_00_u03b1_411_: *mut leanh::LeanObject,
    mut v_act_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ =
        leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_413_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_413_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_413_, 2, v_act_412_);
    v___x_414_ = leanh::lean_apply_2(v_inst_408_, leanh::lean_box(0), v___x_413_);
    v___x_415_ = leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_415_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_415_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_415_, 2, v___f_409_);
    leanh::lean_closure_set(v___x_415_, 3, leanh::lean_box(0));
    v___x_416_ = leanh::lean_apply_4(
        v_toBind_410_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_414_,
        v___x_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
    mut v_inst_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_420_ = leanh::lean_ctor_get(v_inst_417_, 0);
    leanh::lean_inc_ref(v_toApplicative_420_);
    v_toBind_421_ = leanh::lean_ctor_get(v_inst_417_, 1);
    leanh::lean_inc(v_toBind_421_);
    leanh::lean_dec_ref(v_inst_417_);
    v_toPure_422_ = leanh::lean_ctor_get(v_toApplicative_420_, 1);
    leanh::lean_inc(v_toPure_422_);
    leanh::lean_dec_ref(v_toApplicative_420_);
    v___f_423_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_423_, 0, v_inst_418_);
    leanh::lean_closure_set(v___f_423_, 1, v_toPure_422_);
    v___f_424_ = leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_424_, 0, v_inst_419_);
    leanh::lean_closure_set(v___f_424_, 1, v___f_423_);
    leanh::lean_closure_set(v___f_424_, 2, v_toBind_421_);
    return v___f_424_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(
    mut v_m_425_: *mut leanh::LeanObject,
    mut v_00_u03b5_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_inst_428_: *mut leanh::LeanObject,
    mut v_inst_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
        v_inst_427_,
        v_inst_428_,
        v_inst_429_,
    );
    return v___x_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Lift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Lift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Lift(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Lift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Lift(builtin);
}