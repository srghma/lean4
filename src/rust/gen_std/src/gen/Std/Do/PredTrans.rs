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
pub static l_Std_Do_PredTrans_instMonad___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_PredTrans_instMonad___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_PredTrans_instMonad___lam__8 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_PredTrans_instMonad___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_PredTrans_instMonad___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Do_PredTrans_apply___redArg(
    mut v_t_276_: *mut leanh::LeanObject,
    mut v_Q_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = leanh::lean_apply_1(v_t_276_, v_Q_277_);
    return v___x_278_;
}
pub unsafe fn l_Std_Do_PredTrans_apply(
    mut v_ps_279_: *mut leanh::LeanObject,
    mut v_00_u03b1_280_: *mut leanh::LeanObject,
    mut v_t_281_: *mut leanh::LeanObject,
    mut v_Q_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = leanh::lean_apply_1(v_t_281_, v_Q_282_);
    return v___x_283_;
}
pub unsafe fn l_Std_Do_PredTrans_apply___boxed(
    mut v_ps_284_: *mut leanh::LeanObject,
    mut v_00_u03b1_285_: *mut leanh::LeanObject,
    mut v_t_286_: *mut leanh::LeanObject,
    mut v_Q_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Std_Do_PredTrans_apply(v_ps_284_, v_00_u03b1_285_, v_t_286_, v_Q_287_);
    leanh::lean_dec(v_ps_284_);
    return v_res_288_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE(
    mut v_ps_289_: *mut leanh::LeanObject,
    mut v_00_u03b1_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = leanh::lean_box(0);
    return v___x_291_;
}
pub unsafe fn l_Std_Do_PredTrans_instLE___boxed(
    mut v_ps_292_: *mut leanh::LeanObject,
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Do_PredTrans_instLE(v_ps_292_, v_00_u03b1_293_);
    leanh::lean_dec(v_ps_292_);
    return v_res_294_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg___lam__0(
    mut v_a_295_: *mut leanh::LeanObject,
    mut v_Q_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_297_ = leanh::lean_ctor_get(v_Q_296_, 0);
    leanh::lean_inc(v_fst_297_);
    leanh::lean_dec_ref(v_Q_296_);
    v___x_298_ = leanh::lean_apply_1(v_fst_297_, v_a_295_);
    return v___x_298_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___redArg(
    mut v_a_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_300_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_300_, 0, v_a_299_);
    return v___f_300_;
}
pub unsafe fn l_Std_Do_PredTrans_pure(
    mut v_ps_301_: *mut leanh::LeanObject,
    mut v_00_u03b1_302_: *mut leanh::LeanObject,
    mut v_a_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_304_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_304_, 0, v_a_303_);
    return v___f_304_;
}
pub unsafe fn l_Std_Do_PredTrans_pure___boxed(
    mut v_ps_305_: *mut leanh::LeanObject,
    mut v_00_u03b1_306_: *mut leanh::LeanObject,
    mut v_a_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Std_Do_PredTrans_pure(v_ps_305_, v_00_u03b1_306_, v_a_307_);
    leanh::lean_dec(v_ps_305_);
    return v_res_308_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__0(
    mut v_f_309_: *mut leanh::LeanObject,
    mut v_Q_310_: *mut leanh::LeanObject,
    mut v_a_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = leanh::lean_apply_2(v_f_309_, v_a_311_, v_Q_310_);
    return v___x_312_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg___lam__1(
    mut v_f_313_: *mut leanh::LeanObject,
    mut v_x_314_: *mut leanh::LeanObject,
    mut v_Q_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_316_ = leanh::lean_ctor_get(v_Q_315_, 1);
    leanh::lean_inc(v_snd_316_);
    v___f_317_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_317_, 0, v_f_313_);
    leanh::lean_closure_set(v___f_317_, 1, v_Q_315_);
    v___x_318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_318_, 0, v___f_317_);
    leanh::lean_ctor_set(v___x_318_, 1, v_snd_316_);
    v___x_319_ = leanh::lean_apply_1(v_x_314_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___redArg(
    mut v_x_320_: *mut leanh::LeanObject,
    mut v_f_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_322_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_322_, 0, v_f_321_);
    leanh::lean_closure_set(v___f_322_, 1, v_x_320_);
    return v___f_322_;
}
pub unsafe fn l_Std_Do_PredTrans_bind(
    mut v_ps_323_: *mut leanh::LeanObject,
    mut v_00_u03b1_324_: *mut leanh::LeanObject,
    mut v_00_u03b2_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
    mut v_f_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_328_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_328_, 0, v_f_327_);
    leanh::lean_closure_set(v___f_328_, 1, v_x_326_);
    return v___f_328_;
}
pub unsafe fn l_Std_Do_PredTrans_bind___boxed(
    mut v_ps_329_: *mut leanh::LeanObject,
    mut v_00_u03b1_330_: *mut leanh::LeanObject,
    mut v_00_u03b2_331_: *mut leanh::LeanObject,
    mut v_x_332_: *mut leanh::LeanObject,
    mut v_f_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Do_PredTrans_bind(
        v_ps_329_,
        v_00_u03b1_330_,
        v_00_u03b2_331_,
        v_x_332_,
        v_f_333_,
    );
    leanh::lean_dec(v_ps_329_);
    return v_res_334_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0(
    mut v_P_335_: *mut leanh::LeanObject,
    mut v_Q_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_P_335_);
    return v_P_335_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg___lam__0___boxed(
    mut v_P_337_: *mut leanh::LeanObject,
    mut v_Q_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Do_PredTrans_const___redArg___lam__0(v_P_337_, v_Q_338_);
    leanh::lean_dec_ref(v_Q_338_);
    leanh::lean_dec(v_P_337_);
    return v_res_339_;
}
pub unsafe fn l_Std_Do_PredTrans_const___redArg(
    mut v_P_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_341_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_341_, 0, v_P_340_);
    return v___f_341_;
}
pub unsafe fn l_Std_Do_PredTrans_const(
    mut v_ps_342_: *mut leanh::LeanObject,
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_P_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_345_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_const___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_345_, 0, v_P_344_);
    return v___f_345_;
}
pub unsafe fn l_Std_Do_PredTrans_const___boxed(
    mut v_ps_346_: *mut leanh::LeanObject,
    mut v_00_u03b1_347_: *mut leanh::LeanObject,
    mut v_P_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_Do_PredTrans_const(v_ps_346_, v_00_u03b1_347_, v_P_348_);
    leanh::lean_dec(v_ps_346_);
    return v_res_349_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg___lam__0(
    mut v_e_350_: *mut leanh::LeanObject,
    mut v_Q_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_352_ = leanh::lean_ctor_get(v_Q_351_, 1);
    leanh::lean_inc(v_snd_352_);
    leanh::lean_dec_ref(v_Q_351_);
    v_fst_353_ = leanh::lean_ctor_get(v_snd_352_, 0);
    leanh::lean_inc(v_fst_353_);
    leanh::lean_dec(v_snd_352_);
    v___x_354_ = leanh::lean_apply_1(v_fst_353_, v_e_350_);
    return v___x_354_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___redArg(
    mut v_e_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_356_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_356_, 0, v_e_355_);
    return v___f_356_;
}
pub unsafe fn l_Std_Do_PredTrans_throw(
    mut v_ps_357_: *mut leanh::LeanObject,
    mut v_00_u03b1_358_: *mut leanh::LeanObject,
    mut v_00_u03b5_359_: *mut leanh::LeanObject,
    mut v_e_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_361_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_throw___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_361_, 0, v_e_360_);
    return v___f_361_;
}
pub unsafe fn l_Std_Do_PredTrans_throw___boxed(
    mut v_ps_362_: *mut leanh::LeanObject,
    mut v_00_u03b1_363_: *mut leanh::LeanObject,
    mut v_00_u03b5_364_: *mut leanh::LeanObject,
    mut v_e_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Do_PredTrans_throw(v_ps_362_, v_00_u03b1_363_, v_00_u03b5_364_, v_e_365_);
    leanh::lean_dec(v_ps_362_);
    return v_res_366_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__0(
    mut v_ps_367_: *mut leanh::LeanObject,
    mut v_00_u03b1_368_: *mut leanh::LeanObject,
    mut v_00_u03b2_369_: *mut leanh::LeanObject,
    mut v_f_370_: *mut leanh::LeanObject,
    mut v_x_371_: *mut leanh::LeanObject,
    mut v___y_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_373_, 0, v_ps_367_);
    leanh::lean_closure_set(v___x_373_, 1, leanh::lean_box(0));
    v___x_374_ = leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___x_374_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 3, v___x_373_);
    leanh::lean_closure_set(v___x_374_, 4, v_f_370_);
    v___x_375_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_374_, v_x_371_, v___y_372_);
    return v___x_375_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__1(
    mut v_ps_376_: *mut leanh::LeanObject,
    mut v_00_u03b1_377_: *mut leanh::LeanObject,
    mut v_00_u03b2_378_: *mut leanh::LeanObject,
    mut v___y_379_: *mut leanh::LeanObject,
    mut v___y_380_: *mut leanh::LeanObject,
    mut v___y_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_382_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_382_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_382_, 2, v___y_379_);
    v___x_383_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_383_, 0, v_ps_376_);
    leanh::lean_closure_set(v___x_383_, 1, leanh::lean_box(0));
    v___x_384_ = leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___x_384_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_384_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_384_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_384_, 3, v___x_383_);
    leanh::lean_closure_set(v___x_384_, 4, v___x_382_);
    v___x_385_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_384_, v___y_380_, v___y_381_);
    return v___x_385_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__2(
    mut v_x_386_: *mut leanh::LeanObject,
    mut v_ps_387_: *mut leanh::LeanObject,
    mut v_y_388_: *mut leanh::LeanObject,
    mut v___y_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = leanh::lean_box(0);
    v___x_391_ = leanh::lean_apply_1(v_x_386_, v___x_390_);
    v___x_392_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_392_, 0, v_ps_387_);
    leanh::lean_closure_set(v___x_392_, 1, leanh::lean_box(0));
    v___x_393_ = leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___x_393_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_393_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_393_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_393_, 3, v___x_392_);
    leanh::lean_closure_set(v___x_393_, 4, v_y_388_);
    v___x_394_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_393_, v___x_391_, v___y_389_);
    return v___x_394_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__3(
    mut v_ps_395_: *mut leanh::LeanObject,
    mut v_00_u03b1_396_: *mut leanh::LeanObject,
    mut v_00_u03b2_397_: *mut leanh::LeanObject,
    mut v_f_398_: *mut leanh::LeanObject,
    mut v_x_399_: *mut leanh::LeanObject,
    mut v___y_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_401_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_401_, 0, v_x_399_);
    leanh::lean_closure_set(v___f_401_, 1, v_ps_395_);
    v___x_402_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_401_, v_f_398_, v___y_400_);
    return v___x_402_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4(
    mut v_a_403_: *mut leanh::LeanObject,
    mut v_x_404_: *mut leanh::LeanObject,
    mut v___y_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v_a_403_, v___y_405_);
    return v___x_406_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__4___boxed(
    mut v_a_407_: *mut leanh::LeanObject,
    mut v_x_408_: *mut leanh::LeanObject,
    mut v___y_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_410_ = l_Std_Do_PredTrans_instMonad___lam__4(v_a_407_, v_x_408_, v___y_409_);
    leanh::lean_dec(v_x_408_);
    return v_res_410_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__5(
    mut v_y_411_: *mut leanh::LeanObject,
    mut v_a_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_414_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_414_, 0, v_a_412_);
    v___x_415_ = leanh::lean_box(0);
    v___x_416_ = leanh::lean_apply_1(v_y_411_, v___x_415_);
    v___x_417_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_414_, v___x_416_, v___y_413_);
    return v___x_417_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__6(
    mut v_00_u03b1_418_: *mut leanh::LeanObject,
    mut v_00_u03b2_419_: *mut leanh::LeanObject,
    mut v_x_420_: *mut leanh::LeanObject,
    mut v_y_421_: *mut leanh::LeanObject,
    mut v___y_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_423_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__5 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_423_, 0, v_y_421_);
    v___x_424_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_423_, v_x_420_, v___y_422_);
    return v___x_424_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7(
    mut v_y_425_: *mut leanh::LeanObject,
    mut v_x_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_box(0);
    v___x_429_ = leanh::lean_apply_2(v_y_425_, v___x_428_, v___y_427_);
    return v___x_429_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__7___boxed(
    mut v_y_430_: *mut leanh::LeanObject,
    mut v_x_431_: *mut leanh::LeanObject,
    mut v___y_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Do_PredTrans_instMonad___lam__7(v_y_430_, v_x_431_, v___y_432_);
    leanh::lean_dec(v_x_431_);
    return v_res_433_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad___lam__8(
    mut v_00_u03b1_434_: *mut leanh::LeanObject,
    mut v_00_u03b2_435_: *mut leanh::LeanObject,
    mut v_x_436_: *mut leanh::LeanObject,
    mut v_y_437_: *mut leanh::LeanObject,
    mut v___y_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_439_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_439_, 0, v_y_437_);
    v___x_440_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___f_439_, v_x_436_, v___y_438_);
    return v___x_440_;
}
pub unsafe fn l_Std_Do_PredTrans_instMonad(
    mut v_ps_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_ps_443_, 4);
    v___f_444_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_444_, 0, v_ps_443_);
    v___f_445_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_445_, 0, v_ps_443_);
    v___f_446_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_instMonad___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_446_, 0, v_ps_443_);
    v___f_447_ = l_Std_Do_PredTrans_instMonad___closed__0;
    v___f_448_ = l_Std_Do_PredTrans_instMonad___closed__1;
    v___x_449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_449_, 0, v___f_444_);
    leanh::lean_ctor_set(v___x_449_, 1, v___f_445_);
    v___x_450_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_450_, 0, v_ps_443_);
    v___x_451_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_451_, 0, v___x_449_);
    leanh::lean_ctor_set(v___x_451_, 1, v___x_450_);
    leanh::lean_ctor_set(v___x_451_, 2, v___f_446_);
    leanh::lean_ctor_set(v___x_451_, 3, v___f_447_);
    leanh::lean_ctor_set(v___x_451_, 4, v___f_448_);
    v___x_452_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_bind___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___x_452_, 0, v_ps_443_);
    v___x_453_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_453_, 0, v___x_451_);
    leanh::lean_ctor_set(v___x_453_, 1, v___x_452_);
    return v___x_453_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__0(
    mut v_fst_454_: *mut leanh::LeanObject,
    mut v_x_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_456_ = leanh::lean_ctor_get(v_x_455_, 0);
    leanh::lean_inc(v_fst_456_);
    v_snd_457_ = leanh::lean_ctor_get(v_x_455_, 1);
    leanh::lean_inc(v_snd_457_);
    leanh::lean_dec_ref(v_x_455_);
    v___x_458_ = leanh::lean_apply_2(v_fst_454_, v_fst_456_, v_snd_457_);
    return v___x_458_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg___lam__1(
    mut v_x_459_: *mut leanh::LeanObject,
    mut v_Q_460_: *mut leanh::LeanObject,
    mut v_s_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___f_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_462_ = leanh::lean_ctor_get(v_Q_460_, 0);
                v_snd_463_ = leanh::lean_ctor_get(v_Q_460_, 1);
                v_isSharedCheck_472_ = (!leanh::lean_is_exclusive(v_Q_460_)) as u8;
                if v_isSharedCheck_472_ == 0 {
                    v___x_465_ = v_Q_460_;
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_463_);
                    leanh::lean_inc(v_fst_462_);
                    leanh::lean_dec(v_Q_460_);
                    v___x_465_ = leanh::lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_472_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_467_ = leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushArg___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_467_, 0, v_fst_462_);
                if v_isShared_466_ == 0 {
                    leanh::lean_ctor_set(v___x_465_, 0, v___f_467_);
                    v___x_469_ = v___x_465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_471_, 0, v___f_467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_463_);
                    v___x_469_ = v_reuseFailAlloc_471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_470_ = leanh::lean_apply_2(v_x_459_, v_s_461_, v___x_469_);
                return v___x_470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___redArg(
    mut v_x_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_474_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_474_, 0, v_x_473_);
    return v___f_474_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg(
    mut v_ps_475_: *mut leanh::LeanObject,
    mut v_00_u03b1_476_: *mut leanh::LeanObject,
    mut v_00_u03c3_477_: *mut leanh::LeanObject,
    mut v_x_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_479_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_479_, 0, v_x_478_);
    return v___f_479_;
}
pub unsafe fn l_Std_Do_PredTrans_pushArg___boxed(
    mut v_ps_480_: *mut leanh::LeanObject,
    mut v_00_u03b1_481_: *mut leanh::LeanObject,
    mut v_00_u03c3_482_: *mut leanh::LeanObject,
    mut v_x_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Std_Do_PredTrans_pushArg(v_ps_480_, v_00_u03b1_481_, v_00_u03c3_482_, v_x_483_);
    leanh::lean_dec(v_ps_480_);
    return v_res_484_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__0(
    mut v_fst_485_: *mut leanh::LeanObject,
    mut v_fst_486_: *mut leanh::LeanObject,
    mut v_x_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_487_) == 0 {
        let mut v_a_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_486_);
        v_a_488_ = leanh::lean_ctor_get(v_x_487_, 0);
        leanh::lean_inc(v_a_488_);
        leanh::lean_dec_ref_known(v_x_487_, 1);
        v___x_489_ = leanh::lean_apply_1(v_fst_485_, v_a_488_);
        return v___x_489_;
    } else {
        let mut v_a_490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_485_);
        v_a_490_ = leanh::lean_ctor_get(v_x_487_, 0);
        leanh::lean_inc(v_a_490_);
        leanh::lean_dec_ref_known(v_x_487_, 1);
        v___x_491_ = leanh::lean_apply_1(v_fst_486_, v_a_490_);
        return v___x_491_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg___lam__1(
    mut v_x_492_: *mut leanh::LeanObject,
    mut v_Q_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___f_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_494_ = leanh::lean_ctor_get(v_Q_493_, 1);
                leanh::lean_inc(v_snd_494_);
                v_fst_495_ = leanh::lean_ctor_get(v_Q_493_, 0);
                leanh::lean_inc(v_fst_495_);
                leanh::lean_dec_ref(v_Q_493_);
                v_fst_496_ = leanh::lean_ctor_get(v_snd_494_, 0);
                v_snd_497_ = leanh::lean_ctor_get(v_snd_494_, 1);
                v_isSharedCheck_506_ = (!leanh::lean_is_exclusive(v_snd_494_)) as u8;
                if v_isSharedCheck_506_ == 0 {
                    v___x_499_ = v_snd_494_;
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_497_);
                    leanh::lean_inc(v_fst_496_);
                    leanh::lean_dec(v_snd_494_);
                    v___x_499_ = leanh::lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_501_ = leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushExcept___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_501_, 0, v_fst_496_);
                leanh::lean_closure_set(v___f_501_, 1, v_fst_495_);
                if v_isShared_500_ == 0 {
                    leanh::lean_ctor_set(v___x_499_, 0, v___f_501_);
                    v___x_503_ = v___x_499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_505_, 0, v___f_501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_497_);
                    v___x_503_ = v_reuseFailAlloc_505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_504_ = leanh::lean_apply_1(v_x_492_, v___x_503_);
                return v___x_504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___redArg(
    mut v_x_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_508_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_508_, 0, v_x_507_);
    return v___f_508_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept(
    mut v_ps_509_: *mut leanh::LeanObject,
    mut v_00_u03b1_510_: *mut leanh::LeanObject,
    mut v_00_u03b5_511_: *mut leanh::LeanObject,
    mut v_x_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_513_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_513_, 0, v_x_512_);
    return v___f_513_;
}
pub unsafe fn l_Std_Do_PredTrans_pushExcept___boxed(
    mut v_ps_514_: *mut leanh::LeanObject,
    mut v_00_u03b1_515_: *mut leanh::LeanObject,
    mut v_00_u03b5_516_: *mut leanh::LeanObject,
    mut v_x_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_518_ =
        l_Std_Do_PredTrans_pushExcept(v_ps_514_, v_00_u03b1_515_, v_00_u03b5_516_, v_x_517_);
    leanh::lean_dec(v_ps_514_);
    return v_res_518_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__0(
    mut v_fst_519_: *mut leanh::LeanObject,
    mut v_fst_520_: *mut leanh::LeanObject,
    mut v_x_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_521_) == 0 {
        let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_520_);
        v___x_522_ = leanh::lean_box(0);
        v___x_523_ = leanh::lean_apply_1(v_fst_519_, v___x_522_);
        return v___x_523_;
    } else {
        let mut v_val_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_519_);
        v_val_524_ = leanh::lean_ctor_get(v_x_521_, 0);
        leanh::lean_inc(v_val_524_);
        leanh::lean_dec_ref_known(v_x_521_, 1);
        v___x_525_ = leanh::lean_apply_1(v_fst_520_, v_val_524_);
        return v___x_525_;
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg___lam__1(
    mut v_x_526_: *mut leanh::LeanObject,
    mut v_Q_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_534_: u8 = 0;
    let mut v___f_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_528_ = leanh::lean_ctor_get(v_Q_527_, 1);
                leanh::lean_inc(v_snd_528_);
                v_fst_529_ = leanh::lean_ctor_get(v_Q_527_, 0);
                leanh::lean_inc(v_fst_529_);
                leanh::lean_dec_ref(v_Q_527_);
                v_fst_530_ = leanh::lean_ctor_get(v_snd_528_, 0);
                v_snd_531_ = leanh::lean_ctor_get(v_snd_528_, 1);
                v_isSharedCheck_540_ = (!leanh::lean_is_exclusive(v_snd_528_)) as u8;
                if v_isSharedCheck_540_ == 0 {
                    v___x_533_ = v_snd_528_;
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_531_);
                    leanh::lean_inc(v_fst_530_);
                    leanh::lean_dec(v_snd_528_);
                    v___x_533_ = leanh::lean_box(0);
                    v_isShared_534_ = v_isSharedCheck_540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_535_ = leanh::lean_alloc_closure(
                    l_Std_Do_PredTrans_pushOption___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_535_, 0, v_fst_530_);
                leanh::lean_closure_set(v___f_535_, 1, v_fst_529_);
                if v_isShared_534_ == 0 {
                    leanh::lean_ctor_set(v___x_533_, 0, v___f_535_);
                    v___x_537_ = v___x_533_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_539_, 0, v___f_535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_531_);
                    v___x_537_ = v_reuseFailAlloc_539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_538_ = leanh::lean_apply_1(v_x_526_, v___x_537_);
                return v___x_538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___redArg(
    mut v_x_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_542_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_542_, 0, v_x_541_);
    return v___f_542_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption(
    mut v_ps_543_: *mut leanh::LeanObject,
    mut v_00_u03b1_544_: *mut leanh::LeanObject,
    mut v_x_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_546_ = leanh::lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_546_, 0, v_x_545_);
    return v___f_546_;
}
pub unsafe fn l_Std_Do_PredTrans_pushOption___boxed(
    mut v_ps_547_: *mut leanh::LeanObject,
    mut v_00_u03b1_548_: *mut leanh::LeanObject,
    mut v_x_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_550_ = l_Std_Do_PredTrans_pushOption(v_ps_547_, v_00_u03b1_548_, v_x_549_);
    leanh::lean_dec(v_ps_547_);
    return v_res_550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_PredTrans(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PostCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_PredTrans(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_PredTrans(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_PostCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_PredTrans(builtin);
}