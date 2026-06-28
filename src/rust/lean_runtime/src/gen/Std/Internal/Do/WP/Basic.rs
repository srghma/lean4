// Lean compiler output
// Module: Std.Internal.Do.WP.Basic
// Imports: Std.Internal.Do.PredTrans
use crate::r#gen::Std::Internal::Do::PredTrans::{
    initialize_Std_Internal_Do_PredTrans, l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1,
    l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1,
    l_Std_Internal_Do_pushArg___redArg___lam__1, runtime_initialize_Std_Internal_Do_PredTrans,
};
pub static mut l_Std_Internal_Do_Id_instWPMonad: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_Do_Option_instWPMonad: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Internal_Do_wp___redArg(
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_x_219_: *mut crate::leanh::LeanObject,
    mut v_post_220_: *mut crate::leanh::LeanObject,
    mut v_epost_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = crate::leanh::lean_apply_4(
        v_inst_218_,
        crate::leanh::lean_box(0),
        v_x_219_,
        v_post_220_,
        v_epost_221_,
    );
    return v___x_222_;
}
pub unsafe fn l_Std_Internal_Do_wp(
    mut v_m_223_: *mut crate::leanh::LeanObject,
    mut v_Pred_224_: *mut crate::leanh::LeanObject,
    mut v_EPred_225_: *mut crate::leanh::LeanObject,
    mut v_inst_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
    mut v_inst_229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_x_231_: *mut crate::leanh::LeanObject,
    mut v_post_232_: *mut crate::leanh::LeanObject,
    mut v_epost_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = crate::leanh::lean_apply_4(
        v_inst_229_,
        crate::leanh::lean_box(0),
        v_x_231_,
        v_post_232_,
        v_epost_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Std_Internal_Do_wp___boxed(
    mut v_m_235_: *mut crate::leanh::LeanObject,
    mut v_Pred_236_: *mut crate::leanh::LeanObject,
    mut v_EPred_237_: *mut crate::leanh::LeanObject,
    mut v_inst_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_inst_241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_242_: *mut crate::leanh::LeanObject,
    mut v_x_243_: *mut crate::leanh::LeanObject,
    mut v_post_244_: *mut crate::leanh::LeanObject,
    mut v_epost_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_238_);
    return v_res_246_;
}
pub unsafe fn _init_l_Std_Internal_Do_Id_instWPMonad() -> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_box(0);
    return v___x_247_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_248_: *mut crate::leanh::LeanObject,
    mut v_h__1_249_: *mut crate::leanh::LeanObject,
    mut v_h__2_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_248_) == 0 {
        let mut v_a_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_249_);
        v_a_251_ = crate::leanh::lean_ctor_get(v_x_248_, 0);
        crate::leanh::lean_inc(v_a_251_);
        crate::leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_252_ = crate::leanh::lean_apply_1(v_h__2_250_, v_a_251_);
        return v___x_252_;
    } else {
        let mut v_a_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_250_);
        v_a_253_ = crate::leanh::lean_ctor_get(v_x_248_, 0);
        crate::leanh::lean_inc(v_a_253_);
        crate::leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = crate::leanh::lean_apply_1(v_h__1_249_, v_a_253_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_255_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_motive_257_: *mut crate::leanh::LeanObject,
    mut v_x_258_: *mut crate::leanh::LeanObject,
    mut v_h__1_259_: *mut crate::leanh::LeanObject,
    mut v_h__2_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_258_) == 0 {
        let mut v_a_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_259_);
        v_a_261_ = crate::leanh::lean_ctor_get(v_x_258_, 0);
        crate::leanh::lean_inc(v_a_261_);
        crate::leanh::lean_dec_ref_known(v_x_258_, 1);
        v___x_262_ = crate::leanh::lean_apply_1(v_h__2_260_, v_a_261_);
        return v___x_262_;
    } else {
        let mut v_a_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_260_);
        v_a_263_ = crate::leanh::lean_ctor_get(v_x_258_, 0);
        crate::leanh::lean_inc(v_a_263_);
        crate::leanh::lean_dec_ref_known(v_x_258_, 1);
        v___x_264_ = crate::leanh::lean_apply_1(v_h__1_259_, v_a_263_);
        return v___x_264_;
    }
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0(
    mut v_inst_265_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_266_: *mut crate::leanh::LeanObject,
    mut v_x_267_: *mut crate::leanh::LeanObject,
    mut v___y_268_: *mut crate::leanh::LeanObject,
    mut v___y_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = crate::leanh::lean_apply_2(v_inst_265_, crate::leanh::lean_box(0), v_x_267_);
    v___x_271_ = l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(
        v___x_270_, v___y_268_, v___y_269_,
    );
    return v___x_271_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___redArg(
    mut v_inst_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_273_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_273_, 0, v_inst_272_);
    return v___f_273_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad(
    mut v_m_274_: *mut crate::leanh::LeanObject,
    mut v_EPred_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_276_: *mut crate::leanh::LeanObject,
    mut v_Pred_277_: *mut crate::leanh::LeanObject,
    mut v_inst_278_: *mut crate::leanh::LeanObject,
    mut v_inst_279_: *mut crate::leanh::LeanObject,
    mut v_inst_280_: *mut crate::leanh::LeanObject,
    mut v_inst_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_282_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_282_, 0, v_inst_281_);
    return v___f_282_;
}
pub unsafe fn l_Std_Internal_Do_ExceptT_instWPMonad___boxed(
    mut v_m_283_: *mut crate::leanh::LeanObject,
    mut v_EPred_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_285_: *mut crate::leanh::LeanObject,
    mut v_Pred_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_inst_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_287_);
    return v_res_291_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0(
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
    mut v_x_294_: *mut crate::leanh::LeanObject,
    mut v___y_295_: *mut crate::leanh::LeanObject,
    mut v___y_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = crate::leanh::lean_apply_2(v_inst_292_, crate::leanh::lean_box(0), v_x_294_);
    v___x_298_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(
        v___x_297_, v___y_295_, v___y_296_,
    );
    return v___x_298_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___redArg(
    mut v_inst_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_300_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_300_, 0, v_inst_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad(
    mut v_m_301_: *mut crate::leanh::LeanObject,
    mut v_EPred_302_: *mut crate::leanh::LeanObject,
    mut v_Pred_303_: *mut crate::leanh::LeanObject,
    mut v_inst_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
    mut v_inst_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_308_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_308_, 0, v_inst_307_);
    return v___f_308_;
}
pub unsafe fn l_Std_Internal_Do_OptionT_instWPMonad___boxed(
    mut v_m_309_: *mut crate::leanh::LeanObject,
    mut v_EPred_310_: *mut crate::leanh::LeanObject,
    mut v_Pred_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_inst_313_: *mut crate::leanh::LeanObject,
    mut v_inst_314_: *mut crate::leanh::LeanObject,
    mut v_inst_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Std_Internal_Do_OptionT_instWPMonad(
        v_m_309_,
        v_EPred_310_,
        v_Pred_311_,
        v_inst_312_,
        v_inst_313_,
        v_inst_314_,
        v_inst_315_,
    );
    crate::leanh::lean_dec_ref(v_inst_312_);
    return v_res_316_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0(
    mut v_x_317_: *mut crate::leanh::LeanObject,
    mut v_inst_318_: *mut crate::leanh::LeanObject,
    mut v_x_319_: *mut crate::leanh::LeanObject,
    mut v___y_320_: *mut crate::leanh::LeanObject,
    mut v___y_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = crate::leanh::lean_apply_1(v_x_317_, v_x_319_);
    v___x_323_ = crate::leanh::lean_apply_4(
        v_inst_318_,
        crate::leanh::lean_box(0),
        v___x_322_,
        v___y_320_,
        v___y_321_,
    );
    return v___x_323_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1(
    mut v_inst_324_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_325_: *mut crate::leanh::LeanObject,
    mut v_x_326_: *mut crate::leanh::LeanObject,
    mut v___y_327_: *mut crate::leanh::LeanObject,
    mut v___y_328_: *mut crate::leanh::LeanObject,
    mut v___y_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_330_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_330_, 0, v_x_326_);
    crate::leanh::lean_closure_set(v___f_330_, 1, v_inst_324_);
    v___x_331_ =
        l_Std_Internal_Do_pushArg___redArg___lam__1(v___f_330_, v___y_327_, v___y_328_, v___y_329_);
    return v___x_331_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___redArg(
    mut v_inst_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_333_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_333_, 0, v_inst_332_);
    return v___f_333_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad(
    mut v_m_334_: *mut crate::leanh::LeanObject,
    mut v_EPred_335_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_336_: *mut crate::leanh::LeanObject,
    mut v_Pred_337_: *mut crate::leanh::LeanObject,
    mut v_inst_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_inst_340_: *mut crate::leanh::LeanObject,
    mut v_inst_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_342_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_342_, 0, v_inst_341_);
    return v___f_342_;
}
pub unsafe fn l_Std_Internal_Do_StateT_instWPMonad___boxed(
    mut v_m_343_: *mut crate::leanh::LeanObject,
    mut v_EPred_344_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_345_: *mut crate::leanh::LeanObject,
    mut v_Pred_346_: *mut crate::leanh::LeanObject,
    mut v_inst_347_: *mut crate::leanh::LeanObject,
    mut v_inst_348_: *mut crate::leanh::LeanObject,
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_inst_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_347_);
    return v_res_351_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0(
    mut v___y_352_: *mut crate::leanh::LeanObject,
    mut v___y_353_: *mut crate::leanh::LeanObject,
    mut v_a_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = crate::leanh::lean_apply_2(v___y_352_, v_a_354_, v___y_353_);
    return v___x_355_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1(
    mut v_inst_356_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_357_: *mut crate::leanh::LeanObject,
    mut v_x_358_: *mut crate::leanh::LeanObject,
    mut v___y_359_: *mut crate::leanh::LeanObject,
    mut v___y_360_: *mut crate::leanh::LeanObject,
    mut v___y_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_361_);
    v___f_362_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_362_, 0, v___y_359_);
    crate::leanh::lean_closure_set(v___f_362_, 1, v___y_361_);
    v___x_363_ = crate::leanh::lean_apply_1(v_x_358_, v___y_361_);
    v___x_364_ = crate::leanh::lean_apply_4(
        v_inst_356_,
        crate::leanh::lean_box(0),
        v___x_363_,
        v___f_362_,
        v___y_360_,
    );
    return v___x_364_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___redArg(
    mut v_inst_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_366_, 0, v_inst_365_);
    return v___f_366_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad(
    mut v_m_367_: *mut crate::leanh::LeanObject,
    mut v_EPred_368_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_369_: *mut crate::leanh::LeanObject,
    mut v_Pred_370_: *mut crate::leanh::LeanObject,
    mut v_inst_371_: *mut crate::leanh::LeanObject,
    mut v_inst_372_: *mut crate::leanh::LeanObject,
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_inst_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_375_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_375_, 0, v_inst_374_);
    return v___f_375_;
}
pub unsafe fn l_Std_Internal_Do_ReaderT_instWPMonad___boxed(
    mut v_m_376_: *mut crate::leanh::LeanObject,
    mut v_EPred_377_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_378_: *mut crate::leanh::LeanObject,
    mut v_Pred_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
    mut v_inst_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_380_);
    return v_res_384_;
}
pub unsafe fn _init_l_Std_Internal_Do_Option_instWPMonad() -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = crate::leanh::lean_box(0);
    return v___x_385_;
}
pub unsafe fn l_Std_Internal_Do_Except_instWPMonad(
    mut v_00_u03b5_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = crate::leanh::lean_box(0);
    return v___x_387_;
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(
    mut v_x_388_: *mut crate::leanh::LeanObject,
    mut v_h__1_389_: *mut crate::leanh::LeanObject,
    mut v_h__2_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_388_) == 0 {
        let mut v_a_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_390_);
        v_a_391_ = crate::leanh::lean_ctor_get(v_x_388_, 0);
        crate::leanh::lean_inc(v_a_391_);
        v_a_392_ = crate::leanh::lean_ctor_get(v_x_388_, 1);
        crate::leanh::lean_inc(v_a_392_);
        crate::leanh::lean_dec_ref_known(v_x_388_, 2);
        v___x_393_ = crate::leanh::lean_apply_2(v_h__1_389_, v_a_391_, v_a_392_);
        return v___x_393_;
    } else {
        let mut v_a_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_389_);
        v_a_394_ = crate::leanh::lean_ctor_get(v_x_388_, 0);
        crate::leanh::lean_inc(v_a_394_);
        v_a_395_ = crate::leanh::lean_ctor_get(v_x_388_, 1);
        crate::leanh::lean_inc(v_a_395_);
        crate::leanh::lean_dec_ref_known(v_x_388_, 2);
        v___x_396_ = crate::leanh::lean_apply_2(v_h__2_390_, v_a_394_, v_a_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(
    mut v_00_u03b5_397_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_399_: *mut crate::leanh::LeanObject,
    mut v_motive_400_: *mut crate::leanh::LeanObject,
    mut v_x_401_: *mut crate::leanh::LeanObject,
    mut v_h__1_402_: *mut crate::leanh::LeanObject,
    mut v_h__2_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_401_) == 0 {
        let mut v_a_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_403_);
        v_a_404_ = crate::leanh::lean_ctor_get(v_x_401_, 0);
        crate::leanh::lean_inc(v_a_404_);
        v_a_405_ = crate::leanh::lean_ctor_get(v_x_401_, 1);
        crate::leanh::lean_inc(v_a_405_);
        crate::leanh::lean_dec_ref_known(v_x_401_, 2);
        v___x_406_ = crate::leanh::lean_apply_2(v_h__1_402_, v_a_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_402_);
        v_a_407_ = crate::leanh::lean_ctor_get(v_x_401_, 0);
        crate::leanh::lean_inc(v_a_407_);
        v_a_408_ = crate::leanh::lean_ctor_get(v_x_401_, 1);
        crate::leanh::lean_inc(v_a_408_);
        crate::leanh::lean_dec_ref_known(v_x_401_, 2);
        v___x_409_ = crate::leanh::lean_apply_2(v_h__2_403_, v_a_407_, v_a_408_);
        return v___x_409_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter___redArg(
    mut v_x_410_: *mut crate::leanh::LeanObject,
    mut v_h__1_411_: *mut crate::leanh::LeanObject,
    mut v_h__2_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_410_) == 0 {
        let mut v_a_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_412_);
        v_a_413_ = crate::leanh::lean_ctor_get(v_x_410_, 0);
        crate::leanh::lean_inc(v_a_413_);
        v_a_414_ = crate::leanh::lean_ctor_get(v_x_410_, 1);
        crate::leanh::lean_inc(v_a_414_);
        crate::leanh::lean_dec_ref_known(v_x_410_, 2);
        v___x_415_ = crate::leanh::lean_apply_2(v_h__1_411_, v_a_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_411_);
        v_a_416_ = crate::leanh::lean_ctor_get(v_x_410_, 0);
        crate::leanh::lean_inc(v_a_416_);
        v_a_417_ = crate::leanh::lean_ctor_get(v_x_410_, 1);
        crate::leanh::lean_inc(v_a_417_);
        crate::leanh::lean_dec_ref_known(v_x_410_, 2);
        v___x_418_ = crate::leanh::lean_apply_2(v_h__2_412_, v_a_416_, v_a_417_);
        return v___x_418_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter(
    mut v_00_u03b5_419_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_420_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_421_: *mut crate::leanh::LeanObject,
    mut v_motive_422_: *mut crate::leanh::LeanObject,
    mut v_x_423_: *mut crate::leanh::LeanObject,
    mut v_h__1_424_: *mut crate::leanh::LeanObject,
    mut v_h__2_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_423_) == 0 {
        let mut v_a_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_425_);
        v_a_426_ = crate::leanh::lean_ctor_get(v_x_423_, 0);
        crate::leanh::lean_inc(v_a_426_);
        v_a_427_ = crate::leanh::lean_ctor_get(v_x_423_, 1);
        crate::leanh::lean_inc(v_a_427_);
        crate::leanh::lean_dec_ref_known(v_x_423_, 2);
        v___x_428_ = crate::leanh::lean_apply_2(v_h__1_424_, v_a_426_, v_a_427_);
        return v___x_428_;
    } else {
        let mut v_a_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_424_);
        v_a_429_ = crate::leanh::lean_ctor_get(v_x_423_, 0);
        crate::leanh::lean_inc(v_a_429_);
        v_a_430_ = crate::leanh::lean_ctor_get(v_x_423_, 1);
        crate::leanh::lean_inc(v_a_430_);
        crate::leanh::lean_dec_ref_known(v_x_423_, 2);
        v___x_431_ = crate::leanh::lean_apply_2(v_h__2_425_, v_a_429_, v_a_430_);
        return v___x_431_;
    }
}
pub unsafe fn l_Std_Internal_Do_EStateM_instWPMonad(
    mut v_00_u03b5_432_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = crate::leanh::lean_box(0);
    return v___x_434_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_WP_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Internal_Do_Id_instWPMonad = _init_l_Std_Internal_Do_Id_instWPMonad();
    l_Std_Internal_Do_Option_instWPMonad = _init_l_Std_Internal_Do_Option_instWPMonad();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_WP_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_WP_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_WP_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_WP_Basic(builtin);
}
