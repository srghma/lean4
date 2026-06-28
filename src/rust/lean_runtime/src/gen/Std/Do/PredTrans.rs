// Lean compiler output
// Module: Std.Do.PredTrans
// Imports: Init.Control.Lawful Std.Do.PostCond
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
};
use crate::r#gen::Init::Prelude::{l_Function_comp, l_Function_const___boxed};
use crate::r#gen::Std::Do::PostCond::{
    initialize_Std_Do_PostCond, runtime_initialize_Std_Do_PostCond,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag,
};
pub static l_Std_Do_PredTrans_instMonad___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_PredTrans_instMonad___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__8 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_Do_PredTrans_apply___redArg(
    mut v_t_276_: *mut LeanObject,
    mut v_Q_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    v___x_278_ = lean_apply_1(v_t_276_, v_Q_277_);
    return v___x_278_;
}
pub unsafe fn l_Std_Do_PredTrans_apply(
    mut v_ps_279_: *mut LeanObject,
    mut v_00_u03b1_280_: *mut LeanObject,
    mut v_t_281_: *mut LeanObject,
    mut v_Q_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_283_ = lean_apply_1(v_t_281_, v_Q_282_);
    return v___x_283_;
}
pub unsafe fn l_Std_Do_PredTrans_apply___boxed(
    mut v_ps_284_: *mut LeanObject,
    mut v_00_u03b1_285_: *mut LeanObject,
    mut v_t_286_: *mut LeanObject,
    mut v_Q_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_288_: *mut LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Std_Do_PredTrans_apply(v_ps_284_, v_00_u03b1_285_, v_t_286_, v_Q_287_);
    lean_dec(v_ps_284_);
    return v_res_288_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE(
    mut v_ps_289_: *mut LeanObject,
    mut v_00_u03b1_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_box(0);
    return v___x_291_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE___boxed(
    mut v_ps_292_: *mut LeanObject,
    mut v_00_u03b1_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Do_PredTrans_instLE(v_ps_292_, v_00_u03b1_293_);
    lean_dec(v_ps_292_);
    return v_res_294_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg___lam__0(
    mut v_a_295_: *mut LeanObject,
    mut v_Q_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v_fst_297_ = lean_ctor_get(v_Q_296_, 0);
    lean_inc(v_fst_297_);
    lean_dec_ref(v_Q_296_);
    v___x_298_ = lean_apply_1(v_fst_297_, v_a_295_);
    return v___x_298_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg(mut v_a_299_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_300_: *mut LeanObject = core::ptr::null_mut();
    v___f_300_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_300_, 0, v_a_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Do_PredTrans_pure(
    mut v_ps_301_: *mut LeanObject,
    mut v_00_u03b1_302_: *mut LeanObject,
    mut v_a_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_304_: *mut LeanObject = core::ptr::null_mut();
    v___f_304_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_304_, 0, v_a_303_);
    return v___f_304_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___boxed(
    mut v_ps_305_: *mut LeanObject,
    mut v_00_u03b1_306_: *mut LeanObject,
    mut v_a_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Std_Do_PredTrans_pure(v_ps_305_, v_00_u03b1_306_, v_a_307_);
    lean_dec(v_ps_305_);
    return v_res_308_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__0(
    mut v_f_309_: *mut LeanObject,
    mut v_Q_310_: *mut LeanObject,
    mut v_a_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = lean_apply_2(v_f_309_, v_a_311_, v_Q_310_);
    return v___x_312_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__1(
    mut v_f_313_: *mut LeanObject,
    mut v_x_314_: *mut LeanObject,
    mut v_Q_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    v_snd_316_ = lean_ctor_get(v_Q_315_, 1);
    lean_inc(v_snd_316_);
    v___f_317_ = lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_317_, 0, v_f_313_);
    lean_closure_set(v___f_317_, 1, v_Q_315_);
    v___x_318_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v___f_317_);
    lean_ctor_set(v___x_318_, 1, v_snd_316_);
    v___x_319_ = lean_apply_1(v_x_314_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg(
    mut v_x_320_: *mut LeanObject,
    mut v_f_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_322_: *mut LeanObject = core::ptr::null_mut();
    v___f_322_ = lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_322_, 0, v_f_321_);
    lean_closure_set(v___f_322_, 1, v_x_320_);
    return v___f_322_;
}
pub unsafe fn l_Std_Do_PredTrans_bind(
    mut v_ps_323_: *mut LeanObject,
    mut v_00_u03b1_324_: *mut LeanObject,
    mut v_00_u03b2_325_: *mut LeanObject,
    mut v_x_326_: *mut LeanObject,
    mut v_f_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_328_: *mut LeanObject = core::ptr::null_mut();
    v___f_328_ = lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_328_, 0, v_f_327_);
    lean_closure_set(v___f_328_, 1, v_x_326_);
    return v___f_328_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___boxed(
    mut v_ps_329_: *mut LeanObject,
    mut v_00_u03b1_330_: *mut LeanObject,
    mut v_00_u03b2_331_: *mut LeanObject,
    mut v_x_332_: *mut LeanObject,
    mut v_f_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Do_PredTrans_bind(
        v_ps_329_,
        v_00_u03b1_330_,
        v_00_u03b2_331_,
        v_x_332_,
        v_f_333_,
    );
    lean_dec(v_ps_329_);
    return v_res_334_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0(
    mut v_P_335_: *mut LeanObject,
    mut v_Q_336_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_P_335_);
    return v_P_335_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0___boxed(
    mut v_P_337_: *mut LeanObject,
    mut v_Q_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Do_PredTrans_const___redArg___lam__0(v_P_337_, v_Q_338_);
    lean_dec_ref(v_Q_338_);
    lean_dec(v_P_337_);
    return v_res_339_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg(mut v_P_340_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_341_: *mut LeanObject = core::ptr::null_mut();
    v___f_341_ = lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_341_, 0, v_P_340_);
    return v___f_341_;
}
pub unsafe fn l_Std_Do_PredTrans_const(
    mut v_ps_342_: *mut LeanObject,
    mut v_00_u03b1_343_: *mut LeanObject,
    mut v_P_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_345_: *mut LeanObject = core::ptr::null_mut();
    v___f_345_ = lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_345_, 0, v_P_344_);
    return v___f_345_;
}
pub unsafe fn l_Std_Do_PredTrans_const___boxed(
    mut v_ps_346_: *mut LeanObject,
    mut v_00_u03b1_347_: *mut LeanObject,
    mut v_P_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_Do_PredTrans_const(v_ps_346_, v_00_u03b1_347_, v_P_348_);
    lean_dec(v_ps_346_);
    return v_res_349_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg___lam__0(
    mut v_e_350_: *mut LeanObject,
    mut v_Q_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v_snd_352_ = lean_ctor_get(v_Q_351_, 1);
    lean_inc(v_snd_352_);
    lean_dec_ref(v_Q_351_);
    v_fst_353_ = lean_ctor_get(v_snd_352_, 0);
    lean_inc(v_fst_353_);
    lean_dec(v_snd_352_);
    v___x_354_ = lean_apply_1(v_fst_353_, v_e_350_);
    return v___x_354_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg(mut v_e_355_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_356_: *mut LeanObject = core::ptr::null_mut();
    v___f_356_ = lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_356_, 0, v_e_355_);
    return v___f_356_;
}
pub unsafe fn l_Std_Do_PredTrans_throw(
    mut v_ps_357_: *mut LeanObject,
    mut v_00_u03b1_358_: *mut LeanObject,
    mut v_00_u03b5_359_: *mut LeanObject,
    mut v_e_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_361_: *mut LeanObject = core::ptr::null_mut();
    v___f_361_ = lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_361_, 0, v_e_360_);
    return v___f_361_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___boxed(
    mut v_ps_362_: *mut LeanObject,
    mut v_00_u03b1_363_: *mut LeanObject,
    mut v_00_u03b5_364_: *mut LeanObject,
    mut v_e_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_366_: *mut LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Do_PredTrans_throw(v_ps_362_, v_00_u03b1_363_, v_00_u03b5_364_, v_e_365_);
    lean_dec(v_ps_362_);
    return v_res_366_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__0(
    mut v_ps_367_: *mut LeanObject,
    mut v_00_u03b1_368_: *mut LeanObject,
    mut v_00_u03b2_369_: *mut LeanObject,
    mut v_f_370_: *mut LeanObject,
    mut v_x_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_373_, 0, v_ps_367_);
    lean_closure_set(v___x_373_, 1, lean_box(0));
    v___x_374_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_374_, 0, lean_box(0));
    lean_closure_set(v___x_374_, 1, lean_box(0));
    lean_closure_set(v___x_374_, 2, lean_box(0));
    lean_closure_set(v___x_374_, 3, v___x_373_);
    lean_closure_set(v___x_374_, 4, v_f_370_);
    v___x_375_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_374_, v_x_371_, v___y_372_);
    return v___x_375_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__1(
    mut v_ps_376_: *mut LeanObject,
    mut v_00_u03b1_377_: *mut LeanObject,
    mut v_00_u03b2_378_: *mut LeanObject,
    mut v___y_379_: *mut LeanObject,
    mut v___y_380_: *mut LeanObject,
    mut v___y_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_382_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_382_, 0, lean_box(0));
    lean_closure_set(v___x_382_, 1, lean_box(0));
    lean_closure_set(v___x_382_, 2, v___y_379_);
    v___x_383_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_383_, 0, v_ps_376_);
    lean_closure_set(v___x_383_, 1, lean_box(0));
    v___x_384_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_384_, 0, lean_box(0));
    lean_closure_set(v___x_384_, 1, lean_box(0));
    lean_closure_set(v___x_384_, 2, lean_box(0));
    lean_closure_set(v___x_384_, 3, v___x_383_);
    lean_closure_set(v___x_384_, 4, v___x_382_);
    v___x_385_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_384_, v___y_380_, v___y_381_);
    return v___x_385_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__2(
    mut v_x_386_: *mut LeanObject,
    mut v_ps_387_: *mut LeanObject,
    mut v_y_388_: *mut LeanObject,
    mut v___y_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = lean_box(0);
    v___x_391_ = lean_apply_1(v_x_386_, v___x_390_);
    v___x_392_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_392_, 0, v_ps_387_);
    lean_closure_set(v___x_392_, 1, lean_box(0));
    v___x_393_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_393_, 0, lean_box(0));
    lean_closure_set(v___x_393_, 1, lean_box(0));
    lean_closure_set(v___x_393_, 2, lean_box(0));
    lean_closure_set(v___x_393_, 3, v___x_392_);
    lean_closure_set(v___x_393_, 4, v_y_388_);
    v___x_394_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_393_, v___x_391_, v___y_389_);
    return v___x_394_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__3(
    mut v_ps_395_: *mut LeanObject,
    mut v_00_u03b1_396_: *mut LeanObject,
    mut v_00_u03b2_397_: *mut LeanObject,
    mut v_f_398_: *mut LeanObject,
    mut v_x_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___f_401_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_401_, 0, v_x_399_);
    lean_closure_set(v___f_401_, 1, v_ps_395_);
    v___x_402_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_401_, v_f_398_, v___y_400_);
    return v___x_402_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4(
    mut v_a_403_: *mut LeanObject,
    mut v_x_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v_a_403_, v___y_405_);
    return v___x_406_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4___boxed(
    mut v_a_407_: *mut LeanObject,
    mut v_x_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_410_: *mut LeanObject = core::ptr::null_mut();
    v_res_410_ = l_Std_Do_PredTrans_instMonad___lam__4(v_a_407_, v_x_408_, v___y_409_);
    lean_dec(v_x_408_);
    return v_res_410_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__5(
    mut v_y_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v___y_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    v___f_414_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_414_, 0, v_a_412_);
    v___x_415_ = lean_box(0);
    v___x_416_ = lean_apply_1(v_y_411_, v___x_415_);
    v___x_417_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_414_, v___x_416_, v___y_413_);
    return v___x_417_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__6(
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v_00_u03b2_419_: *mut LeanObject,
    mut v_x_420_: *mut LeanObject,
    mut v_y_421_: *mut LeanObject,
    mut v___y_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___f_423_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__5 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_423_, 0, v_y_421_);
    v___x_424_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_423_, v_x_420_, v___y_422_);
    return v___x_424_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7(
    mut v_y_425_: *mut LeanObject,
    mut v_x_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_box(0);
    v___x_429_ = lean_apply_2(v_y_425_, v___x_428_, v___y_427_);
    return v___x_429_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7___boxed(
    mut v_y_430_: *mut LeanObject,
    mut v_x_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_433_: *mut LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Do_PredTrans_instMonad___lam__7(v_y_430_, v_x_431_, v___y_432_);
    lean_dec(v_x_431_);
    return v_res_433_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__8(
    mut v_00_u03b1_434_: *mut LeanObject,
    mut v_00_u03b2_435_: *mut LeanObject,
    mut v_x_436_: *mut LeanObject,
    mut v_y_437_: *mut LeanObject,
    mut v___y_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___f_439_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_439_, 0, v_y_437_);
    v___x_440_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_439_, v_x_436_, v___y_438_);
    return v___x_440_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad(mut v_ps_443_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_ps_443_, 4);
    v___f_444_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_444_, 0, v_ps_443_);
    v___f_445_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_445_, 0, v_ps_443_);
    v___f_446_ = lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_446_, 0, v_ps_443_);
    v___f_447_ = l_Std_Do_PredTrans_instMonad___closed__0;
    v___f_448_ = l_Std_Do_PredTrans_instMonad___closed__1;
    v___x_449_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_449_, 0, v___f_444_);
    lean_ctor_set(v___x_449_, 1, v___f_445_);
    v___x_450_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_450_, 0, v_ps_443_);
    v___x_451_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_451_, 0, v___x_449_);
    lean_ctor_set(v___x_451_, 1, v___x_450_);
    lean_ctor_set(v___x_451_, 2, v___f_446_);
    lean_ctor_set(v___x_451_, 3, v___f_447_);
    lean_ctor_set(v___x_451_, 4, v___f_448_);
    v___x_452_ = lean_alloc_closure(
        l_Std_Do_PredTrans_bind___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___x_452_, 0, v_ps_443_);
    v___x_453_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_453_, 0, v___x_451_);
    lean_ctor_set(v___x_453_, 1, v___x_452_);
    return v___x_453_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__0(
    mut v_fst_454_: *mut LeanObject,
    mut v_x_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    v_fst_456_ = lean_ctor_get(v_x_455_, 0);
    lean_inc(v_fst_456_);
    v_snd_457_ = lean_ctor_get(v_x_455_, 1);
    lean_inc(v_snd_457_);
    lean_dec_ref(v_x_455_);
    v___x_458_ = lean_apply_2(v_fst_454_, v_fst_456_, v_snd_457_);
    return v___x_458_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__1(
    mut v_x_459_: *mut LeanObject,
    mut v_Q_460_: *mut LeanObject,
    mut v_s_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___f_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_462_ = lean_ctor_get(v_Q_460_, 0);
                v_snd_463_ = lean_ctor_get(v_Q_460_, 1);
                v_isSharedCheck_472_ = (!lean_is_exclusive(v_Q_460_)) as u8;
                if v_isSharedCheck_472_ == 0 {
                    v___x_465_ = v_Q_460_;
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_463_);
                    lean_inc(v_fst_462_);
                    lean_dec(v_Q_460_);
                    v___x_465_ = lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_467_ = lean_alloc_closure(
                    l_Std_Do_PredTrans_pushArg___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_467_, 0, v_fst_462_);
                if v_isShared_466_ == 0 {
                    lean_ctor_set(v___x_465_, 0, v___f_467_);
                    v___x_469_ = v___x_465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_471_, 0, v___f_467_);
                    lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_463_);
                    v___x_469_ = v_reuseFailAlloc_471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_470_ = lean_apply_2(v_x_459_, v_s_461_, v___x_469_);
                return v___x_470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg(
    mut v_x_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_474_: *mut LeanObject = core::ptr::null_mut();
    v___f_474_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_474_, 0, v_x_473_);
    return v___f_474_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg(
    mut v_ps_475_: *mut LeanObject,
    mut v_00_u03b1_476_: *mut LeanObject,
    mut v_00_u03c3_477_: *mut LeanObject,
    mut v_x_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_479_: *mut LeanObject = core::ptr::null_mut();
    v___f_479_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_479_, 0, v_x_478_);
    return v___f_479_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___boxed(
    mut v_ps_480_: *mut LeanObject,
    mut v_00_u03b1_481_: *mut LeanObject,
    mut v_00_u03c3_482_: *mut LeanObject,
    mut v_x_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Std_Do_PredTrans_pushArg(v_ps_480_, v_00_u03b1_481_, v_00_u03c3_482_, v_x_483_);
    lean_dec(v_ps_480_);
    return v_res_484_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__0(
    mut v_fst_485_: *mut LeanObject,
    mut v_fst_486_: *mut LeanObject,
    mut v_x_487_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_487_) == 0 {
        let mut v_a_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_486_);
        v_a_488_ = lean_ctor_get(v_x_487_, 0);
        lean_inc(v_a_488_);
        lean_dec_ref_known(v_x_487_, 1);
        v___x_489_ = lean_apply_1(v_fst_485_, v_a_488_);
        return v___x_489_;
    } else {
        let mut v_a_490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_485_);
        v_a_490_ = lean_ctor_get(v_x_487_, 0);
        lean_inc(v_a_490_);
        lean_dec_ref_known(v_x_487_, 1);
        v___x_491_ = lean_apply_1(v_fst_486_, v_a_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__1(
    mut v_x_492_: *mut LeanObject,
    mut v_Q_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___f_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_494_ = lean_ctor_get(v_Q_493_, 1);
                lean_inc(v_snd_494_);
                v_fst_495_ = lean_ctor_get(v_Q_493_, 0);
                lean_inc(v_fst_495_);
                lean_dec_ref(v_Q_493_);
                v_fst_496_ = lean_ctor_get(v_snd_494_, 0);
                v_snd_497_ = lean_ctor_get(v_snd_494_, 1);
                v_isSharedCheck_506_ = (!lean_is_exclusive(v_snd_494_)) as u8;
                if v_isSharedCheck_506_ == 0 {
                    v___x_499_ = v_snd_494_;
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_497_);
                    lean_inc(v_fst_496_);
                    lean_dec(v_snd_494_);
                    v___x_499_ = lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_501_ = lean_alloc_closure(
                    l_Std_Do_PredTrans_pushExcept___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_501_, 0, v_fst_496_);
                lean_closure_set(v___f_501_, 1, v_fst_495_);
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 0, v___f_501_);
                    v___x_503_ = v___x_499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_505_, 0, v___f_501_);
                    lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_497_);
                    v___x_503_ = v_reuseFailAlloc_505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_504_ = lean_apply_1(v_x_492_, v___x_503_);
                return v___x_504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg(
    mut v_x_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_508_: *mut LeanObject = core::ptr::null_mut();
    v___f_508_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_508_, 0, v_x_507_);
    return v___f_508_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept(
    mut v_ps_509_: *mut LeanObject,
    mut v_00_u03b1_510_: *mut LeanObject,
    mut v_00_u03b5_511_: *mut LeanObject,
    mut v_x_512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_513_: *mut LeanObject = core::ptr::null_mut();
    v___f_513_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_513_, 0, v_x_512_);
    return v___f_513_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___boxed(
    mut v_ps_514_: *mut LeanObject,
    mut v_00_u03b1_515_: *mut LeanObject,
    mut v_00_u03b5_516_: *mut LeanObject,
    mut v_x_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_518_: *mut LeanObject = core::ptr::null_mut();
    v_res_518_ =
        l_Std_Do_PredTrans_pushExcept(v_ps_514_, v_00_u03b1_515_, v_00_u03b5_516_, v_x_517_);
    lean_dec(v_ps_514_);
    return v_res_518_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__0(
    mut v_fst_519_: *mut LeanObject,
    mut v_fst_520_: *mut LeanObject,
    mut v_x_521_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_521_) == 0 {
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_520_);
        v___x_522_ = lean_box(0);
        v___x_523_ = lean_apply_1(v_fst_519_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_val_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_519_);
        v_val_524_ = lean_ctor_get(v_x_521_, 0);
        lean_inc(v_val_524_);
        lean_dec_ref_known(v_x_521_, 1);
        v___x_525_ = lean_apply_1(v_fst_520_, v_val_524_);
        return v___x_525_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__1(
    mut v_x_526_: *mut LeanObject,
    mut v_Q_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_534_: u8 = 0;
    let mut v___f_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_528_ = lean_ctor_get(v_Q_527_, 1);
                lean_inc(v_snd_528_);
                v_fst_529_ = lean_ctor_get(v_Q_527_, 0);
                lean_inc(v_fst_529_);
                lean_dec_ref(v_Q_527_);
                v_fst_530_ = lean_ctor_get(v_snd_528_, 0);
                v_snd_531_ = lean_ctor_get(v_snd_528_, 1);
                v_isSharedCheck_540_ = (!lean_is_exclusive(v_snd_528_)) as u8;
                if v_isSharedCheck_540_ == 0 {
                    v___x_533_ = v_snd_528_;
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_531_);
                    lean_inc(v_fst_530_);
                    lean_dec(v_snd_528_);
                    v___x_533_ = lean_box(0);
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_535_ = lean_alloc_closure(
                    l_Std_Do_PredTrans_pushOption___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_535_, 0, v_fst_530_);
                lean_closure_set(v___f_535_, 1, v_fst_529_);
                if v_isShared_534_ == 0 {
                    lean_ctor_set(v___x_533_, 0, v___f_535_);
                    v___x_537_ = v___x_533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_539_, 0, v___f_535_);
                    lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_531_);
                    v___x_537_ = v_reuseFailAlloc_539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_538_ = lean_apply_1(v_x_526_, v___x_537_);
                return v___x_538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg(
    mut v_x_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_542_: *mut LeanObject = core::ptr::null_mut();
    v___f_542_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_542_, 0, v_x_541_);
    return v___f_542_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption(
    mut v_ps_543_: *mut LeanObject,
    mut v_00_u03b1_544_: *mut LeanObject,
    mut v_x_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_546_: *mut LeanObject = core::ptr::null_mut();
    v___f_546_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_546_, 0, v_x_545_);
    return v___f_546_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___boxed(
    mut v_ps_547_: *mut LeanObject,
    mut v_00_u03b1_548_: *mut LeanObject,
    mut v_x_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_550_: *mut LeanObject = core::ptr::null_mut();
    v_res_550_ = l_Std_Do_PredTrans_pushOption(v_ps_547_, v_00_u03b1_548_, v_x_549_);
    lean_dec(v_ps_547_);
    return v_res_550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_PredTrans(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PostCond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_PredTrans(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_PredTrans(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Do_PostCond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_PredTrans(builtin);
}
