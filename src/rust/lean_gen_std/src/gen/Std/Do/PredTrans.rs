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
pub static l_Std_Do_PredTrans_instMonad___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_PredTrans_instMonad___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__8 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Do_PredTrans_apply___redArg(
    mut v_t_276_: *mut crate::leanh::LeanObject,
    mut v_Q_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = crate::leanh::lean_apply_1(v_t_276_, v_Q_277_);
    return v___x_278_;
}
pub unsafe fn l_Std_Do_PredTrans_apply(
    mut v_ps_279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_280_: *mut crate::leanh::LeanObject,
    mut v_t_281_: *mut crate::leanh::LeanObject,
    mut v_Q_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = crate::leanh::lean_apply_1(v_t_281_, v_Q_282_);
    return v___x_283_;
}
pub unsafe fn l_Std_Do_PredTrans_apply___boxed(
    mut v_ps_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_285_: *mut crate::leanh::LeanObject,
    mut v_t_286_: *mut crate::leanh::LeanObject,
    mut v_Q_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Std_Do_PredTrans_apply(v_ps_284_, v_00_u03b1_285_, v_t_286_, v_Q_287_);
    crate::leanh::lean_dec(v_ps_284_);
    return v_res_288_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE(
    mut v_ps_289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_box(0);
    return v___x_291_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE___boxed(
    mut v_ps_292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Do_PredTrans_instLE(v_ps_292_, v_00_u03b1_293_);
    crate::leanh::lean_dec(v_ps_292_);
    return v_res_294_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg___lam__0(
    mut v_a_295_: *mut crate::leanh::LeanObject,
    mut v_Q_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_297_ = crate::leanh::lean_ctor_get(v_Q_296_, 0);
    crate::leanh::lean_inc(v_fst_297_);
    crate::leanh::lean_dec_ref(v_Q_296_);
    v___x_298_ = crate::leanh::lean_apply_1(v_fst_297_, v_a_295_);
    return v___x_298_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg(
    mut v_a_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_300_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_300_, 0, v_a_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Do_PredTrans_pure(
    mut v_ps_301_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_302_: *mut crate::leanh::LeanObject,
    mut v_a_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_304_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_304_, 0, v_a_303_);
    return v___f_304_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___boxed(
    mut v_ps_305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_306_: *mut crate::leanh::LeanObject,
    mut v_a_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Std_Do_PredTrans_pure(v_ps_305_, v_00_u03b1_306_, v_a_307_);
    crate::leanh::lean_dec(v_ps_305_);
    return v_res_308_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__0(
    mut v_f_309_: *mut crate::leanh::LeanObject,
    mut v_Q_310_: *mut crate::leanh::LeanObject,
    mut v_a_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = crate::leanh::lean_apply_2(v_f_309_, v_a_311_, v_Q_310_);
    return v___x_312_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__1(
    mut v_f_313_: *mut crate::leanh::LeanObject,
    mut v_x_314_: *mut crate::leanh::LeanObject,
    mut v_Q_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_316_ = crate::leanh::lean_ctor_get(v_Q_315_, 1);
    crate::leanh::lean_inc(v_snd_316_);
    v___f_317_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_317_, 0, v_f_313_);
    crate::leanh::lean_closure_set(v___f_317_, 1, v_Q_315_);
    v___x_318_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v___f_317_);
    crate::leanh::lean_ctor_set(v___x_318_, 1, v_snd_316_);
    v___x_319_ = crate::leanh::lean_apply_1(v_x_314_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg(
    mut v_x_320_: *mut crate::leanh::LeanObject,
    mut v_f_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_322_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_322_, 0, v_f_321_);
    crate::leanh::lean_closure_set(v___f_322_, 1, v_x_320_);
    return v___f_322_;
}
pub unsafe fn l_Std_Do_PredTrans_bind(
    mut v_ps_323_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_324_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_325_: *mut crate::leanh::LeanObject,
    mut v_x_326_: *mut crate::leanh::LeanObject,
    mut v_f_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_328_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_328_, 0, v_f_327_);
    crate::leanh::lean_closure_set(v___f_328_, 1, v_x_326_);
    return v___f_328_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___boxed(
    mut v_ps_329_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_330_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
    mut v_f_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Do_PredTrans_bind(
        v_ps_329_,
        v_00_u03b1_330_,
        v_00_u03b2_331_,
        v_x_332_,
        v_f_333_,
    );
    crate::leanh::lean_dec(v_ps_329_);
    return v_res_334_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0(
    mut v_P_335_: *mut crate::leanh::LeanObject,
    mut v_Q_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_P_335_);
    return v_P_335_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0___boxed(
    mut v_P_337_: *mut crate::leanh::LeanObject,
    mut v_Q_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Do_PredTrans_const___redArg___lam__0(v_P_337_, v_Q_338_);
    crate::leanh::lean_dec_ref(v_Q_338_);
    crate::leanh::lean_dec(v_P_337_);
    return v_res_339_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg(
    mut v_P_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_341_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_341_, 0, v_P_340_);
    return v___f_341_;
}
pub unsafe fn l_Std_Do_PredTrans_const(
    mut v_ps_342_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_343_: *mut crate::leanh::LeanObject,
    mut v_P_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_345_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_345_, 0, v_P_344_);
    return v___f_345_;
}
pub unsafe fn l_Std_Do_PredTrans_const___boxed(
    mut v_ps_346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_347_: *mut crate::leanh::LeanObject,
    mut v_P_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_Do_PredTrans_const(v_ps_346_, v_00_u03b1_347_, v_P_348_);
    crate::leanh::lean_dec(v_ps_346_);
    return v_res_349_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg___lam__0(
    mut v_e_350_: *mut crate::leanh::LeanObject,
    mut v_Q_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_352_ = crate::leanh::lean_ctor_get(v_Q_351_, 1);
    crate::leanh::lean_inc(v_snd_352_);
    crate::leanh::lean_dec_ref(v_Q_351_);
    v_fst_353_ = crate::leanh::lean_ctor_get(v_snd_352_, 0);
    crate::leanh::lean_inc(v_fst_353_);
    crate::leanh::lean_dec(v_snd_352_);
    v___x_354_ = crate::leanh::lean_apply_1(v_fst_353_, v_e_350_);
    return v___x_354_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg(
    mut v_e_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_356_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_356_, 0, v_e_355_);
    return v___f_356_;
}
pub unsafe fn l_Std_Do_PredTrans_throw(
    mut v_ps_357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_358_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_359_: *mut crate::leanh::LeanObject,
    mut v_e_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_361_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_361_, 0, v_e_360_);
    return v___f_361_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___boxed(
    mut v_ps_362_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_364_: *mut crate::leanh::LeanObject,
    mut v_e_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Do_PredTrans_throw(v_ps_362_, v_00_u03b1_363_, v_00_u03b5_364_, v_e_365_);
    crate::leanh::lean_dec(v_ps_362_);
    return v_res_366_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__0(
    mut v_ps_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_369_: *mut crate::leanh::LeanObject,
    mut v_f_370_: *mut crate::leanh::LeanObject,
    mut v_x_371_: *mut crate::leanh::LeanObject,
    mut v___y_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_373_, 0, v_ps_367_);
    crate::leanh::lean_closure_set(v___x_373_, 1, crate::leanh::lean_box(0));
    v___x_374_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_374_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_374_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_374_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_374_, 3, v___x_373_);
    crate::leanh::lean_closure_set(v___x_374_, 4, v_f_370_);
    v___x_375_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_374_, v_x_371_, v___y_372_);
    return v___x_375_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__1(
    mut v_ps_376_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_378_: *mut crate::leanh::LeanObject,
    mut v___y_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_382_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_382_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_382_, 2, v___y_379_);
    v___x_383_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_383_, 0, v_ps_376_);
    crate::leanh::lean_closure_set(v___x_383_, 1, crate::leanh::lean_box(0));
    v___x_384_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_384_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_384_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_384_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_384_, 3, v___x_383_);
    crate::leanh::lean_closure_set(v___x_384_, 4, v___x_382_);
    v___x_385_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_384_, v___y_380_, v___y_381_);
    return v___x_385_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__2(
    mut v_x_386_: *mut crate::leanh::LeanObject,
    mut v_ps_387_: *mut crate::leanh::LeanObject,
    mut v_y_388_: *mut crate::leanh::LeanObject,
    mut v___y_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = crate::leanh::lean_box(0);
    v___x_391_ = crate::leanh::lean_apply_1(v_x_386_, v___x_390_);
    v___x_392_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_392_, 0, v_ps_387_);
    crate::leanh::lean_closure_set(v___x_392_, 1, crate::leanh::lean_box(0));
    v___x_393_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_393_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_393_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_393_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_393_, 3, v___x_392_);
    crate::leanh::lean_closure_set(v___x_393_, 4, v_y_388_);
    v___x_394_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_393_, v___x_391_, v___y_389_);
    return v___x_394_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__3(
    mut v_ps_395_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_397_: *mut crate::leanh::LeanObject,
    mut v_f_398_: *mut crate::leanh::LeanObject,
    mut v_x_399_: *mut crate::leanh::LeanObject,
    mut v___y_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_401_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_401_, 0, v_x_399_);
    crate::leanh::lean_closure_set(v___f_401_, 1, v_ps_395_);
    v___x_402_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_401_, v_f_398_, v___y_400_);
    return v___x_402_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4(
    mut v_a_403_: *mut crate::leanh::LeanObject,
    mut v_x_404_: *mut crate::leanh::LeanObject,
    mut v___y_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v_a_403_, v___y_405_);
    return v___x_406_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4___boxed(
    mut v_a_407_: *mut crate::leanh::LeanObject,
    mut v_x_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_410_ = l_Std_Do_PredTrans_instMonad___lam__4(v_a_407_, v_x_408_, v___y_409_);
    crate::leanh::lean_dec(v_x_408_);
    return v_res_410_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__5(
    mut v_y_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_414_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_414_, 0, v_a_412_);
    v___x_415_ = crate::leanh::lean_box(0);
    v___x_416_ = crate::leanh::lean_apply_1(v_y_411_, v___x_415_);
    v___x_417_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_414_, v___x_416_, v___y_413_);
    return v___x_417_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__6(
    mut v_00_u03b1_418_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_419_: *mut crate::leanh::LeanObject,
    mut v_x_420_: *mut crate::leanh::LeanObject,
    mut v_y_421_: *mut crate::leanh::LeanObject,
    mut v___y_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_423_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__5 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_423_, 0, v_y_421_);
    v___x_424_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_423_, v_x_420_, v___y_422_);
    return v___x_424_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7(
    mut v_y_425_: *mut crate::leanh::LeanObject,
    mut v_x_426_: *mut crate::leanh::LeanObject,
    mut v___y_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = crate::leanh::lean_box(0);
    v___x_429_ = crate::leanh::lean_apply_2(v_y_425_, v___x_428_, v___y_427_);
    return v___x_429_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7___boxed(
    mut v_y_430_: *mut crate::leanh::LeanObject,
    mut v_x_431_: *mut crate::leanh::LeanObject,
    mut v___y_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Do_PredTrans_instMonad___lam__7(v_y_430_, v_x_431_, v___y_432_);
    crate::leanh::lean_dec(v_x_431_);
    return v_res_433_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__8(
    mut v_00_u03b1_434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
    mut v_y_437_: *mut crate::leanh::LeanObject,
    mut v___y_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_439_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_439_, 0, v_y_437_);
    v___x_440_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_439_, v_x_436_, v___y_438_);
    return v___x_440_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad(
    mut v_ps_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_ps_443_, 4);
    v___f_444_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_444_, 0, v_ps_443_);
    v___f_445_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_445_, 0, v_ps_443_);
    v___f_446_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_446_, 0, v_ps_443_);
    v___f_447_ = l_Std_Do_PredTrans_instMonad___closed__0;
    v___f_448_ = l_Std_Do_PredTrans_instMonad___closed__1;
    v___x_449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_449_, 0, v___f_444_);
    crate::leanh::lean_ctor_set(v___x_449_, 1, v___f_445_);
    v___x_450_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_450_, 0, v_ps_443_);
    v___x_451_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_449_);
    crate::leanh::lean_ctor_set(v___x_451_, 1, v___x_450_);
    crate::leanh::lean_ctor_set(v___x_451_, 2, v___f_446_);
    crate::leanh::lean_ctor_set(v___x_451_, 3, v___f_447_);
    crate::leanh::lean_ctor_set(v___x_451_, 4, v___f_448_);
    v___x_452_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___x_452_, 0, v_ps_443_);
    v___x_453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_451_);
    crate::leanh::lean_ctor_set(v___x_453_, 1, v___x_452_);
    return v___x_453_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__0(
    mut v_fst_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_456_ = crate::leanh::lean_ctor_get(v_x_455_, 0);
    crate::leanh::lean_inc(v_fst_456_);
    v_snd_457_ = crate::leanh::lean_ctor_get(v_x_455_, 1);
    crate::leanh::lean_inc(v_snd_457_);
    crate::leanh::lean_dec_ref(v_x_455_);
    v___x_458_ = crate::leanh::lean_apply_2(v_fst_454_, v_fst_456_, v_snd_457_);
    return v___x_458_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__1(
    mut v_x_459_: *mut crate::leanh::LeanObject,
    mut v_Q_460_: *mut crate::leanh::LeanObject,
    mut v_s_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___f_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_462_ = crate::leanh::lean_ctor_get(v_Q_460_, 0);
                v_snd_463_ = crate::leanh::lean_ctor_get(v_Q_460_, 1);
                v_isSharedCheck_472_ = (!crate::leanh::lean_is_exclusive(v_Q_460_)) as u8;
                if v_isSharedCheck_472_ == 0 {
                    v___x_465_ = v_Q_460_;
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_463_);
                    crate::leanh::lean_inc(v_fst_462_);
                    crate::leanh::lean_dec(v_Q_460_);
                    v___x_465_ = crate::leanh::lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_467_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushArg___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_467_, 0, v_fst_462_);
                if v_isShared_466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_465_, 0, v___f_467_);
                    v___x_469_ = v___x_465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_471_, 0, v___f_467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_463_);
                    v___x_469_ = v_reuseFailAlloc_471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_470_ = crate::leanh::lean_apply_2(v_x_459_, v_s_461_, v___x_469_);
                return v___x_470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg(
    mut v_x_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_474_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_474_, 0, v_x_473_);
    return v___f_474_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg(
    mut v_ps_475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_476_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_477_: *mut crate::leanh::LeanObject,
    mut v_x_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_479_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_479_, 0, v_x_478_);
    return v___f_479_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___boxed(
    mut v_ps_480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_481_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_482_: *mut crate::leanh::LeanObject,
    mut v_x_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Std_Do_PredTrans_pushArg(v_ps_480_, v_00_u03b1_481_, v_00_u03c3_482_, v_x_483_);
    crate::leanh::lean_dec(v_ps_480_);
    return v_res_484_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__0(
    mut v_fst_485_: *mut crate::leanh::LeanObject,
    mut v_fst_486_: *mut crate::leanh::LeanObject,
    mut v_x_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_487_) == 0 {
        let mut v_a_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_486_);
        v_a_488_ = crate::leanh::lean_ctor_get(v_x_487_, 0);
        crate::leanh::lean_inc(v_a_488_);
        crate::leanh::lean_dec_ref_known(v_x_487_, 1);
        v___x_489_ = crate::leanh::lean_apply_1(v_fst_485_, v_a_488_);
        return v___x_489_;
    } else {
        let mut v_a_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_485_);
        v_a_490_ = crate::leanh::lean_ctor_get(v_x_487_, 0);
        crate::leanh::lean_inc(v_a_490_);
        crate::leanh::lean_dec_ref_known(v_x_487_, 1);
        v___x_491_ = crate::leanh::lean_apply_1(v_fst_486_, v_a_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__1(
    mut v_x_492_: *mut crate::leanh::LeanObject,
    mut v_Q_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___f_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_494_ = crate::leanh::lean_ctor_get(v_Q_493_, 1);
                crate::leanh::lean_inc(v_snd_494_);
                v_fst_495_ = crate::leanh::lean_ctor_get(v_Q_493_, 0);
                crate::leanh::lean_inc(v_fst_495_);
                crate::leanh::lean_dec_ref(v_Q_493_);
                v_fst_496_ = crate::leanh::lean_ctor_get(v_snd_494_, 0);
                v_snd_497_ = crate::leanh::lean_ctor_get(v_snd_494_, 1);
                v_isSharedCheck_506_ = (!crate::leanh::lean_is_exclusive(v_snd_494_)) as u8;
                if v_isSharedCheck_506_ == 0 {
                    v___x_499_ = v_snd_494_;
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_497_);
                    crate::leanh::lean_inc(v_fst_496_);
                    crate::leanh::lean_dec(v_snd_494_);
                    v___x_499_ = crate::leanh::lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_501_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushExcept___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_501_, 0, v_fst_496_);
                crate::leanh::lean_closure_set(v___f_501_, 1, v_fst_495_);
                if v_isShared_500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_499_, 0, v___f_501_);
                    v___x_503_ = v___x_499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_505_, 0, v___f_501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_497_);
                    v___x_503_ = v_reuseFailAlloc_505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_504_ = crate::leanh::lean_apply_1(v_x_492_, v___x_503_);
                return v___x_504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg(
    mut v_x_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_508_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_508_, 0, v_x_507_);
    return v___f_508_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept(
    mut v_ps_509_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_510_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_511_: *mut crate::leanh::LeanObject,
    mut v_x_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_513_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_513_, 0, v_x_512_);
    return v___f_513_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___boxed(
    mut v_ps_514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_516_: *mut crate::leanh::LeanObject,
    mut v_x_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_518_ =
        l_Std_Do_PredTrans_pushExcept(v_ps_514_, v_00_u03b1_515_, v_00_u03b5_516_, v_x_517_);
    crate::leanh::lean_dec(v_ps_514_);
    return v_res_518_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__0(
    mut v_fst_519_: *mut crate::leanh::LeanObject,
    mut v_fst_520_: *mut crate::leanh::LeanObject,
    mut v_x_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_521_) == 0 {
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_520_);
        v___x_522_ = crate::leanh::lean_box(0);
        v___x_523_ = crate::leanh::lean_apply_1(v_fst_519_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_val_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_519_);
        v_val_524_ = crate::leanh::lean_ctor_get(v_x_521_, 0);
        crate::leanh::lean_inc(v_val_524_);
        crate::leanh::lean_dec_ref_known(v_x_521_, 1);
        v___x_525_ = crate::leanh::lean_apply_1(v_fst_520_, v_val_524_);
        return v___x_525_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__1(
    mut v_x_526_: *mut crate::leanh::LeanObject,
    mut v_Q_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_534_: u8 = 0;
    let mut v___f_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_528_ = crate::leanh::lean_ctor_get(v_Q_527_, 1);
                crate::leanh::lean_inc(v_snd_528_);
                v_fst_529_ = crate::leanh::lean_ctor_get(v_Q_527_, 0);
                crate::leanh::lean_inc(v_fst_529_);
                crate::leanh::lean_dec_ref(v_Q_527_);
                v_fst_530_ = crate::leanh::lean_ctor_get(v_snd_528_, 0);
                v_snd_531_ = crate::leanh::lean_ctor_get(v_snd_528_, 1);
                v_isSharedCheck_540_ = (!crate::leanh::lean_is_exclusive(v_snd_528_)) as u8;
                if v_isSharedCheck_540_ == 0 {
                    v___x_533_ = v_snd_528_;
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_531_);
                    crate::leanh::lean_inc(v_fst_530_);
                    crate::leanh::lean_dec(v_snd_528_);
                    v___x_533_ = crate::leanh::lean_box(0);
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_535_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushOption___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_535_, 0, v_fst_530_);
                crate::leanh::lean_closure_set(v___f_535_, 1, v_fst_529_);
                if v_isShared_534_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_533_, 0, v___f_535_);
                    v___x_537_ = v___x_533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 0, v___f_535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_531_);
                    v___x_537_ = v_reuseFailAlloc_539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_538_ = crate::leanh::lean_apply_1(v_x_526_, v___x_537_);
                return v___x_538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg(
    mut v_x_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_542_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_542_, 0, v_x_541_);
    return v___f_542_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption(
    mut v_ps_543_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_544_: *mut crate::leanh::LeanObject,
    mut v_x_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_546_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_546_, 0, v_x_545_);
    return v___f_546_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___boxed(
    mut v_ps_547_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_548_: *mut crate::leanh::LeanObject,
    mut v_x_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_550_ = l_Std_Do_PredTrans_pushOption(v_ps_547_, v_00_u03b1_548_, v_x_549_);
    crate::leanh::lean_dec(v_ps_547_);
    return v_res_550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_PredTrans(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PostCond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_PredTrans(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_PredTrans(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Do_PostCond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Do_PredTrans(builtin);
}
