// Lean compiler output
// Module: Lake.Util.Lift
// Imports: Init.System.IO
use crate::r#gen::Init::Prelude::l_liftM;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_EIO_toBaseIO___boxed, runtime_initialize_Init_System_IO,
};
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(
    mut v_inst_216_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_218_ = crate::leanh::lean_ctor_get(v_inst_216_, 0);
    crate::leanh::lean_inc(v_throw_218_);
    crate::leanh::lean_dec_ref(v_inst_216_);
    v___x_219_ = crate::leanh::lean_box(0);
    v___x_220_ = crate::leanh::lean_apply_2(v_throw_218_, crate::leanh::lean_box(0), v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(
    mut v_inst_221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_222_: *mut crate::leanh::LeanObject,
    mut v___y_223_: *mut crate::leanh::LeanObject,
    mut v___y_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_225_ = crate::leanh::lean_ctor_get(v_inst_221_, 1);
    crate::leanh::lean_inc(v_tryCatch_225_);
    crate::leanh::lean_dec_ref(v_inst_221_);
    v___x_226_ = crate::leanh::lean_apply_3(
        v_tryCatch_225_,
        crate::leanh::lean_box(0),
        v___y_223_,
        v___y_224_,
    );
    return v___x_226_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_229_ = crate::leanh::lean_ctor_get(v_inst_227_, 0);
    crate::leanh::lean_inc_ref(v_inst_228_);
    v___f_230_ = crate::leanh::lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_230_, 0, v_inst_228_);
    v___f_231_ = crate::leanh::lean_alloc_closure(
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_231_, 0, v_inst_228_);
    crate::leanh::lean_inc_ref(v_toApplicative_229_);
    v___x_232_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_232_, 0, v_toApplicative_229_);
    crate::leanh::lean_ctor_set(v___x_232_, 1, v___f_230_);
    crate::leanh::lean_ctor_set(v___x_232_, 2, v___f_231_);
    return v___x_232_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(
    mut v_inst_233_: *mut crate::leanh::LeanObject,
    mut v_inst_234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_233_, v_inst_234_);
    crate::leanh::lean_dec_ref(v_inst_233_);
    return v_res_235_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(
    mut v_m_236_: *mut crate::leanh::LeanObject,
    mut v_inst_237_: *mut crate::leanh::LeanObject,
    mut v_inst_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_237_, v_inst_238_);
    return v___x_239_;
}
pub unsafe fn l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(
    mut v_m_240_: *mut crate::leanh::LeanObject,
    mut v_inst_241_: *mut crate::leanh::LeanObject,
    mut v_inst_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ =
        l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(v_m_240_, v_inst_241_, v_inst_242_);
    crate::leanh::lean_dec_ref(v_inst_241_);
    return v_res_243_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_245_: *mut crate::leanh::LeanObject,
    mut v___y_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_apply_2(v_inst_244_, crate::leanh::lean_box(0), v___y_246_);
    return v___x_247_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake___redArg(
    mut v_inst_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_249_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_249_, 0, v_inst_248_);
    return v___f_249_;
}
pub unsafe fn l_Lake_instMonadLiftTOfMonadLift__lake(
    mut v_00_u03b1_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_253_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_253_, 0, v_inst_252_);
    return v___f_253_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(
    mut v_inst_254_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_255_: *mut crate::leanh::LeanObject,
    mut v_act_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = crate::leanh::lean_apply_2(v_inst_254_, crate::leanh::lean_box(0), v_act_256_);
    return v___x_257_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake___redArg(
    mut v_inst_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_259_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_259_, 0, v_inst_258_);
    return v___f_259_;
}
pub unsafe fn l_Lake_instMonadLiftTIdOfPure__lake(
    mut v_m_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_262_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_262_, 0, v_inst_261_);
    return v___f_262_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(
    mut v_failure_263_: *mut crate::leanh::LeanObject,
    mut v_toPure_264_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_265_: *mut crate::leanh::LeanObject,
    mut v_x_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_264_);
        v___x_267_ = crate::leanh::lean_apply_1(v_failure_263_, crate::leanh::lean_box(0));
        return v___x_267_;
    } else {
        let mut v_val_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_failure_263_);
        v_val_268_ = crate::leanh::lean_ctor_get(v_x_266_, 0);
        crate::leanh::lean_inc(v_val_268_);
        crate::leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_269_ =
            crate::leanh::lean_apply_2(v_toPure_264_, crate::leanh::lean_box(0), v_val_268_);
        return v___x_269_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(
    mut v_inst_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_271_ = crate::leanh::lean_ctor_get(v_inst_270_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_271_);
    v_failure_272_ = crate::leanh::lean_ctor_get(v_inst_270_, 1);
    crate::leanh::lean_inc(v_failure_272_);
    crate::leanh::lean_dec_ref(v_inst_270_);
    v_toPure_273_ = crate::leanh::lean_ctor_get(v_toApplicative_271_, 1);
    crate::leanh::lean_inc(v_toPure_273_);
    crate::leanh::lean_dec_ref(v_toApplicative_271_);
    v___f_274_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_274_, 0, v_failure_272_);
    crate::leanh::lean_closure_set(v___f_274_, 1, v_toPure_273_);
    return v___f_274_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionOfAlternative__lake(
    mut v_m_275_: *mut crate::leanh::LeanObject,
    mut v_inst_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_276_);
    return v___x_277_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_278_: *mut crate::leanh::LeanObject,
    mut v_inst_279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_280_: *mut crate::leanh::LeanObject,
    mut v_x_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_281_) == 0 {
        let mut v_a_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_throw_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_279_);
        v_a_282_ = crate::leanh::lean_ctor_get(v_x_281_, 0);
        crate::leanh::lean_inc(v_a_282_);
        crate::leanh::lean_dec_ref_known(v_x_281_, 1);
        v_throw_283_ = crate::leanh::lean_ctor_get(v_inst_278_, 0);
        crate::leanh::lean_inc(v_throw_283_);
        crate::leanh::lean_dec_ref(v_inst_278_);
        v___x_284_ = crate::leanh::lean_apply_2(v_throw_283_, crate::leanh::lean_box(0), v_a_282_);
        return v___x_284_;
    } else {
        let mut v_a_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_278_);
        v_a_285_ = crate::leanh::lean_ctor_get(v_x_281_, 0);
        crate::leanh::lean_inc(v_a_285_);
        crate::leanh::lean_dec_ref_known(v_x_281_, 1);
        v___x_286_ = crate::leanh::lean_apply_2(v_inst_279_, crate::leanh::lean_box(0), v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_289_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_289_, 0, v_inst_288_);
    crate::leanh::lean_closure_set(v___f_289_, 1, v_inst_287_);
    return v___f_289_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(
    mut v_m_290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_291_: *mut crate::leanh::LeanObject,
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_inst_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_294_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_294_, 0, v_inst_293_);
    crate::leanh::lean_closure_set(v___f_294_, 1, v_inst_292_);
    return v___f_294_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0(
    mut v_act_295_: *mut crate::leanh::LeanObject,
    mut v_inst_296_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = crate::leanh::lean_apply_1(v_act_295_, v_____do__lift_297_);
    v___x_299_ = crate::leanh::lean_apply_2(v_inst_296_, crate::leanh::lean_box(0), v___x_298_);
    return v___x_299_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1(
    mut v_inst_300_: *mut crate::leanh::LeanObject,
    mut v_toBind_301_: *mut crate::leanh::LeanObject,
    mut v_inst_302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_303_: *mut crate::leanh::LeanObject,
    mut v_act_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_305_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_305_, 0, v_act_304_);
    crate::leanh::lean_closure_set(v___f_305_, 1, v_inst_300_);
    v___x_306_ = crate::leanh::lean_apply_4(
        v_toBind_301_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_302_,
        v___f_305_,
    );
    return v___x_306_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
    mut v_inst_307_: *mut crate::leanh::LeanObject,
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_310_ = crate::leanh::lean_ctor_get(v_inst_307_, 1);
    crate::leanh::lean_inc(v_toBind_310_);
    crate::leanh::lean_dec_ref(v_inst_307_);
    v___f_311_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_311_, 0, v_inst_309_);
    crate::leanh::lean_closure_set(v___f_311_, 1, v_toBind_310_);
    crate::leanh::lean_closure_set(v___f_311_, 2, v_inst_308_);
    return v___f_311_;
}
pub unsafe fn l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake(
    mut v_m_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_313_: *mut crate::leanh::LeanObject,
    mut v_n_314_: *mut crate::leanh::LeanObject,
    mut v_inst_315_: *mut crate::leanh::LeanObject,
    mut v_inst_316_: *mut crate::leanh::LeanObject,
    mut v_inst_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(
        v_inst_315_,
        v_inst_316_,
        v_inst_317_,
    );
    return v___x_318_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(
    mut v_toPure_319_: *mut crate::leanh::LeanObject,
    mut v_fst_320_: *mut crate::leanh::LeanObject,
    mut v_____r_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = crate::leanh::lean_apply_2(v_toPure_319_, crate::leanh::lean_box(0), v_fst_320_);
    return v___x_322_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(
    mut v_inst_323_: *mut crate::leanh::LeanObject,
    mut v_toPure_324_: *mut crate::leanh::LeanObject,
    mut v_toBind_325_: *mut crate::leanh::LeanObject,
    mut v_____x_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_327_ = crate::leanh::lean_ctor_get(v_____x_326_, 0);
    crate::leanh::lean_inc(v_fst_327_);
    v_snd_328_ = crate::leanh::lean_ctor_get(v_____x_326_, 1);
    crate::leanh::lean_inc(v_snd_328_);
    crate::leanh::lean_dec_ref(v_____x_326_);
    v_set_329_ = crate::leanh::lean_ctor_get(v_inst_323_, 1);
    crate::leanh::lean_inc(v_set_329_);
    crate::leanh::lean_dec_ref(v_inst_323_);
    v___f_330_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_330_, 0, v_toPure_324_);
    crate::leanh::lean_closure_set(v___f_330_, 1, v_fst_327_);
    v___x_331_ = crate::leanh::lean_apply_1(v_set_329_, v_snd_328_);
    v___x_332_ = crate::leanh::lean_apply_4(
        v_toBind_325_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_331_,
        v___f_330_,
    );
    return v___x_332_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(
    mut v_act_333_: *mut crate::leanh::LeanObject,
    mut v_inst_334_: *mut crate::leanh::LeanObject,
    mut v_toBind_335_: *mut crate::leanh::LeanObject,
    mut v___f_336_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = crate::leanh::lean_apply_1(v_act_333_, v_____do__lift_337_);
    v___x_339_ = crate::leanh::lean_apply_2(v_inst_334_, crate::leanh::lean_box(0), v___x_338_);
    v___x_340_ = crate::leanh::lean_apply_4(
        v_toBind_335_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_339_,
        v___f_336_,
    );
    return v___x_340_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_inst_342_: *mut crate::leanh::LeanObject,
    mut v_toBind_343_: *mut crate::leanh::LeanObject,
    mut v___f_344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_345_: *mut crate::leanh::LeanObject,
    mut v_act_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_347_ = crate::leanh::lean_ctor_get(v_inst_341_, 0);
    crate::leanh::lean_inc(v_get_347_);
    crate::leanh::lean_dec_ref(v_inst_341_);
    crate::leanh::lean_inc(v_toBind_343_);
    v___f_348_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_348_, 0, v_act_346_);
    crate::leanh::lean_closure_set(v___f_348_, 1, v_inst_342_);
    crate::leanh::lean_closure_set(v___f_348_, 2, v_toBind_343_);
    crate::leanh::lean_closure_set(v___f_348_, 3, v___f_344_);
    v___x_349_ = crate::leanh::lean_apply_4(
        v_toBind_343_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_get_347_,
        v___f_348_,
    );
    return v___x_349_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
    mut v_inst_350_: *mut crate::leanh::LeanObject,
    mut v_inst_351_: *mut crate::leanh::LeanObject,
    mut v_inst_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_353_ = crate::leanh::lean_ctor_get(v_inst_350_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_353_);
    v_toBind_354_ = crate::leanh::lean_ctor_get(v_inst_350_, 1);
    crate::leanh::lean_inc_n(v_toBind_354_, 2);
    crate::leanh::lean_dec_ref(v_inst_350_);
    v_toPure_355_ = crate::leanh::lean_ctor_get(v_toApplicative_353_, 1);
    crate::leanh::lean_inc(v_toPure_355_);
    crate::leanh::lean_dec_ref(v_toApplicative_353_);
    crate::leanh::lean_inc_ref(v_inst_351_);
    v___f_356_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_356_, 0, v_inst_351_);
    crate::leanh::lean_closure_set(v___f_356_, 1, v_toPure_355_);
    crate::leanh::lean_closure_set(v___f_356_, 2, v_toBind_354_);
    v___f_357_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_357_, 0, v_inst_351_);
    crate::leanh::lean_closure_set(v___f_357_, 1, v_inst_352_);
    crate::leanh::lean_closure_set(v___f_357_, 2, v_toBind_354_);
    crate::leanh::lean_closure_set(v___f_357_, 3, v___f_356_);
    return v___f_357_;
}
pub unsafe fn l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(
    mut v_m_358_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_359_: *mut crate::leanh::LeanObject,
    mut v_n_360_: *mut crate::leanh::LeanObject,
    mut v_inst_361_: *mut crate::leanh::LeanObject,
    mut v_inst_362_: *mut crate::leanh::LeanObject,
    mut v_inst_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(
        v_inst_361_,
        v_inst_362_,
        v_inst_363_,
    );
    return v___x_364_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(
    mut v_inst_365_: *mut crate::leanh::LeanObject,
    mut v___x_366_: *mut crate::leanh::LeanObject,
    mut v_toBind_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_368_: *mut crate::leanh::LeanObject,
    mut v_act_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = crate::leanh::lean_apply_2(v_inst_365_, crate::leanh::lean_box(0), v_act_369_);
    v___x_371_ = crate::leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_371_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_371_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_371_, 2, v___x_366_);
    crate::leanh::lean_closure_set(v___x_371_, 3, crate::leanh::lean_box(0));
    v___x_372_ = crate::leanh::lean_apply_4(
        v_toBind_367_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_370_,
        v___x_371_,
    );
    return v___x_372_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_inst_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_376_ = crate::leanh::lean_ctor_get(v_inst_373_, 1);
    crate::leanh::lean_inc(v_toBind_376_);
    crate::leanh::lean_dec_ref(v_inst_373_);
    v___x_377_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_374_);
    v___f_378_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_378_, 0, v_inst_375_);
    crate::leanh::lean_closure_set(v___f_378_, 1, v___x_377_);
    crate::leanh::lean_closure_set(v___f_378_, 2, v_toBind_376_);
    return v___f_378_;
}
pub unsafe fn l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(
    mut v_m_379_: *mut crate::leanh::LeanObject,
    mut v_n_380_: *mut crate::leanh::LeanObject,
    mut v_inst_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(
        v_inst_381_,
        v_inst_382_,
        v_inst_383_,
    );
    return v___x_384_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v___f_386_: *mut crate::leanh::LeanObject,
    mut v_toBind_387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_act_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = crate::leanh::lean_apply_2(v_inst_385_, crate::leanh::lean_box(0), v_act_389_);
    v___x_391_ = crate::leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_391_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_391_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_391_, 2, v___f_386_);
    crate::leanh::lean_closure_set(v___x_391_, 3, crate::leanh::lean_box(0));
    v___x_392_ = crate::leanh::lean_apply_4(
        v_toBind_387_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_390_,
        v___x_391_,
    );
    return v___x_392_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
    mut v_inst_393_: *mut crate::leanh::LeanObject,
    mut v_inst_394_: *mut crate::leanh::LeanObject,
    mut v_inst_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_396_ = crate::leanh::lean_ctor_get(v_inst_393_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_396_);
    v_toBind_397_ = crate::leanh::lean_ctor_get(v_inst_393_, 1);
    crate::leanh::lean_inc(v_toBind_397_);
    crate::leanh::lean_dec_ref(v_inst_393_);
    v_toPure_398_ = crate::leanh::lean_ctor_get(v_toApplicative_396_, 1);
    crate::leanh::lean_inc(v_toPure_398_);
    crate::leanh::lean_dec_ref(v_toApplicative_396_);
    v___f_399_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_399_, 0, v_inst_394_);
    crate::leanh::lean_closure_set(v___f_399_, 1, v_toPure_398_);
    v___f_400_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_400_, 0, v_inst_395_);
    crate::leanh::lean_closure_set(v___f_400_, 1, v___f_399_);
    crate::leanh::lean_closure_set(v___f_400_, 2, v_toBind_397_);
    return v___f_400_;
}
pub unsafe fn l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(
    mut v_m_401_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_402_: *mut crate::leanh::LeanObject,
    mut v_n_403_: *mut crate::leanh::LeanObject,
    mut v_inst_404_: *mut crate::leanh::LeanObject,
    mut v_inst_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(
        v_inst_404_,
        v_inst_405_,
        v_inst_406_,
    );
    return v___x_407_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(
    mut v_inst_408_: *mut crate::leanh::LeanObject,
    mut v___f_409_: *mut crate::leanh::LeanObject,
    mut v_toBind_410_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_411_: *mut crate::leanh::LeanObject,
    mut v_act_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ =
        crate::leanh::lean_alloc_closure(l_EIO_toBaseIO___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_413_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_413_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_413_, 2, v_act_412_);
    v___x_414_ = crate::leanh::lean_apply_2(v_inst_408_, crate::leanh::lean_box(0), v___x_413_);
    v___x_415_ = crate::leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_415_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_415_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_415_, 2, v___f_409_);
    crate::leanh::lean_closure_set(v___x_415_, 3, crate::leanh::lean_box(0));
    v___x_416_ = crate::leanh::lean_apply_4(
        v_toBind_410_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_414_,
        v___x_415_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
    mut v_inst_417_: *mut crate::leanh::LeanObject,
    mut v_inst_418_: *mut crate::leanh::LeanObject,
    mut v_inst_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_420_ = crate::leanh::lean_ctor_get(v_inst_417_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_420_);
    v_toBind_421_ = crate::leanh::lean_ctor_get(v_inst_417_, 1);
    crate::leanh::lean_inc(v_toBind_421_);
    crate::leanh::lean_dec_ref(v_inst_417_);
    v_toPure_422_ = crate::leanh::lean_ctor_get(v_toApplicative_420_, 1);
    crate::leanh::lean_inc(v_toPure_422_);
    crate::leanh::lean_dec_ref(v_toApplicative_420_);
    v___f_423_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_423_, 0, v_inst_418_);
    crate::leanh::lean_closure_set(v___f_423_, 1, v_toPure_422_);
    v___f_424_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_424_, 0, v_inst_419_);
    crate::leanh::lean_closure_set(v___f_424_, 1, v___f_423_);
    crate::leanh::lean_closure_set(v___f_424_, 2, v_toBind_421_);
    return v___f_424_;
}
pub unsafe fn l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(
    mut v_m_425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_426_: *mut crate::leanh::LeanObject,
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_inst_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(
        v_inst_427_,
        v_inst_428_,
        v_inst_429_,
    );
    return v___x_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Lift(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Lift(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Lift(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Lift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Lift(builtin);
}
