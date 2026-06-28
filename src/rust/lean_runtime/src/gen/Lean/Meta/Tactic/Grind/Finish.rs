// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Finish
// Imports: Lean.Meta.Tactic.Grind.Action Lean.Meta.Tactic.Grind.EMatchAction Lean.Meta.Tactic.Grind.Split
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    initialize_Lean_Meta_Tactic_Grind_Action, l_Lean_Meta_Grind_Action_andThen,
    l_Lean_Meta_Grind_Action_checkTactic___boxed, l_Lean_Meta_Grind_Action_loop___redArg,
    l_Lean_Meta_Grind_Action_mbtc___boxed, l_Lean_Meta_Grind_Action_orElse,
    runtime_initialize_Lean_Meta_Tactic_Grind_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchAction::{
    initialize_Lean_Meta_Tactic_Grind_EMatchAction, l_Lean_Meta_Grind_Action_instantiate___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Intro::{
    l_Lean_Meta_Grind_Action_assertAll___boxed, l_Lean_Meta_Grind_Action_intros___boxed,
    l_Lean_Meta_Grind_Solvers_mkAction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Split::{
    initialize_Lean_Meta_Tactic_Grind_Split, l_Lean_Meta_Grind_Action_splitNext___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Split,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_Grind_Action_maxIterationsDefault: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_splitNext___boxed as *const core::ffi::c_void,
        m_arity: 15,
        m_num_fixed: 2,
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_instantiate___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_assertAll___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_intros___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_mbtc___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_checkTactic___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind_Action_maxIterationsDefault() -> *mut LeanObject {
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    v___x_259_ = lean_unsigned_to_nat(10000);
    return v___x_259_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__0(
    mut v___f_264_: *mut LeanObject,
    mut v___y_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
    mut v___y_267_: *mut LeanObject,
    mut v___y_268_: *mut LeanObject,
    mut v___y_269_: *mut LeanObject,
    mut v___y_270_: *mut LeanObject,
    mut v___y_271_: *mut LeanObject,
    mut v___y_272_: *mut LeanObject,
    mut v___y_273_: *mut LeanObject,
    mut v___y_274_: *mut LeanObject,
    mut v___y_275_: *mut LeanObject,
    mut v___y_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    v___x_278_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0;
    v___x_279_ = l_Lean_Meta_Grind_Action_orElse(
        v___x_278_, v___f_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_,
        v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_,
    );
    return v___x_279_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed(
    mut v___f_280_: *mut LeanObject,
    mut v___y_281_: *mut LeanObject,
    mut v___y_282_: *mut LeanObject,
    mut v___y_283_: *mut LeanObject,
    mut v___y_284_: *mut LeanObject,
    mut v___y_285_: *mut LeanObject,
    mut v___y_286_: *mut LeanObject,
    mut v___y_287_: *mut LeanObject,
    mut v___y_288_: *mut LeanObject,
    mut v___y_289_: *mut LeanObject,
    mut v___y_290_: *mut LeanObject,
    mut v___y_291_: *mut LeanObject,
    mut v___y_292_: *mut LeanObject,
    mut v___y_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0(
        v___f_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_,
        v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_,
    );
    lean_dec(v___y_292_);
    lean_dec_ref(v___y_291_);
    lean_dec(v___y_290_);
    lean_dec_ref(v___y_289_);
    lean_dec(v___y_288_);
    lean_dec_ref(v___y_287_);
    lean_dec(v___y_286_);
    lean_dec_ref(v___y_285_);
    lean_dec(v___y_284_);
    return v_res_294_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__1(
    mut v___f_296_: *mut LeanObject,
    mut v___y_297_: *mut LeanObject,
    mut v___y_298_: *mut LeanObject,
    mut v___y_299_: *mut LeanObject,
    mut v___y_300_: *mut LeanObject,
    mut v___y_301_: *mut LeanObject,
    mut v___y_302_: *mut LeanObject,
    mut v___y_303_: *mut LeanObject,
    mut v___y_304_: *mut LeanObject,
    mut v___y_305_: *mut LeanObject,
    mut v___y_306_: *mut LeanObject,
    mut v___y_307_: *mut LeanObject,
    mut v___y_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0;
    v___x_311_ = l_Lean_Meta_Grind_Action_orElse(
        v___x_310_, v___f_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_,
        v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_,
    );
    return v___x_311_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed(
    mut v___f_312_: *mut LeanObject,
    mut v___y_313_: *mut LeanObject,
    mut v___y_314_: *mut LeanObject,
    mut v___y_315_: *mut LeanObject,
    mut v___y_316_: *mut LeanObject,
    mut v___y_317_: *mut LeanObject,
    mut v___y_318_: *mut LeanObject,
    mut v___y_319_: *mut LeanObject,
    mut v___y_320_: *mut LeanObject,
    mut v___y_321_: *mut LeanObject,
    mut v___y_322_: *mut LeanObject,
    mut v___y_323_: *mut LeanObject,
    mut v___y_324_: *mut LeanObject,
    mut v___y_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1(
        v___f_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_,
        v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_,
    );
    lean_dec(v___y_324_);
    lean_dec_ref(v___y_323_);
    lean_dec(v___y_322_);
    lean_dec_ref(v___y_321_);
    lean_dec(v___y_320_);
    lean_dec_ref(v___y_319_);
    lean_dec(v___y_318_);
    lean_dec_ref(v___y_317_);
    lean_dec(v___y_316_);
    return v_res_326_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__2(
    mut v_a_327_: *mut LeanObject,
    mut v___f_328_: *mut LeanObject,
    mut v___y_329_: *mut LeanObject,
    mut v___y_330_: *mut LeanObject,
    mut v___y_331_: *mut LeanObject,
    mut v___y_332_: *mut LeanObject,
    mut v___y_333_: *mut LeanObject,
    mut v___y_334_: *mut LeanObject,
    mut v___y_335_: *mut LeanObject,
    mut v___y_336_: *mut LeanObject,
    mut v___y_337_: *mut LeanObject,
    mut v___y_338_: *mut LeanObject,
    mut v___y_339_: *mut LeanObject,
    mut v___y_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Meta_Grind_Action_orElse(
        v_a_327_, v___f_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_,
        v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_,
    );
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed(
    mut v_a_343_: *mut LeanObject,
    mut v___f_344_: *mut LeanObject,
    mut v___y_345_: *mut LeanObject,
    mut v___y_346_: *mut LeanObject,
    mut v___y_347_: *mut LeanObject,
    mut v___y_348_: *mut LeanObject,
    mut v___y_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v___y_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Lean_Meta_Grind_Action_mkFinish___lam__2(
        v_a_343_, v___f_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_,
        v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_,
    );
    lean_dec(v___y_356_);
    lean_dec_ref(v___y_355_);
    lean_dec(v___y_354_);
    lean_dec_ref(v___y_353_);
    lean_dec(v___y_352_);
    lean_dec_ref(v___y_351_);
    lean_dec(v___y_350_);
    lean_dec_ref(v___y_349_);
    lean_dec(v___y_348_);
    return v_res_358_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__3(
    mut v_maxIterations_359_: *mut LeanObject,
    mut v___f_360_: *mut LeanObject,
    mut v___y_361_: *mut LeanObject,
    mut v___y_362_: *mut LeanObject,
    mut v___y_363_: *mut LeanObject,
    mut v___y_364_: *mut LeanObject,
    mut v___y_365_: *mut LeanObject,
    mut v___y_366_: *mut LeanObject,
    mut v___y_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
    mut v___y_369_: *mut LeanObject,
    mut v___y_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_374_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v_maxIterations_359_,
        v___f_360_,
        v___y_361_,
        v___y_363_,
        v___y_364_,
        v___y_365_,
        v___y_366_,
        v___y_367_,
        v___y_368_,
        v___y_369_,
        v___y_370_,
        v___y_371_,
        v___y_372_,
    );
    return v___x_374_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed(
    mut v_maxIterations_375_: *mut LeanObject,
    mut v___f_376_: *mut LeanObject,
    mut v___y_377_: *mut LeanObject,
    mut v___y_378_: *mut LeanObject,
    mut v___y_379_: *mut LeanObject,
    mut v___y_380_: *mut LeanObject,
    mut v___y_381_: *mut LeanObject,
    mut v___y_382_: *mut LeanObject,
    mut v___y_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
    mut v___y_388_: *mut LeanObject,
    mut v___y_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_390_: *mut LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Lean_Meta_Grind_Action_mkFinish___lam__3(
        v_maxIterations_375_,
        v___f_376_,
        v___y_377_,
        v___y_378_,
        v___y_379_,
        v___y_380_,
        v___y_381_,
        v___y_382_,
        v___y_383_,
        v___y_384_,
        v___y_385_,
        v___y_386_,
        v___y_387_,
        v___y_388_,
    );
    lean_dec(v___y_388_);
    lean_dec_ref(v___y_387_);
    lean_dec(v___y_386_);
    lean_dec_ref(v___y_385_);
    lean_dec(v___y_384_);
    lean_dec_ref(v___y_383_);
    lean_dec(v___y_382_);
    lean_dec_ref(v___y_381_);
    lean_dec(v___y_380_);
    lean_dec_ref(v___y_378_);
    lean_dec(v_maxIterations_375_);
    return v_res_390_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__4(
    mut v___f_392_: *mut LeanObject,
    mut v___y_393_: *mut LeanObject,
    mut v___y_394_: *mut LeanObject,
    mut v___y_395_: *mut LeanObject,
    mut v___y_396_: *mut LeanObject,
    mut v___y_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
    mut v___y_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
    mut v___y_401_: *mut LeanObject,
    mut v___y_402_: *mut LeanObject,
    mut v___y_403_: *mut LeanObject,
    mut v___y_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0;
    v___x_407_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_406_, v___f_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_,
        v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_,
    );
    return v___x_407_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed(
    mut v___f_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
    mut v___y_413_: *mut LeanObject,
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
    mut v___y_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
    mut v___y_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_422_: *mut LeanObject = core::ptr::null_mut();
    v_res_422_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4(
        v___f_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_,
        v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_,
    );
    lean_dec(v___y_420_);
    lean_dec_ref(v___y_419_);
    lean_dec(v___y_418_);
    lean_dec_ref(v___y_417_);
    lean_dec(v___y_416_);
    lean_dec_ref(v___y_415_);
    lean_dec(v___y_414_);
    lean_dec_ref(v___y_413_);
    lean_dec(v___y_412_);
    return v_res_422_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__5(
    mut v___f_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
    mut v___y_433_: *mut LeanObject,
    mut v___y_434_: *mut LeanObject,
    mut v___y_435_: *mut LeanObject,
    mut v___y_436_: *mut LeanObject,
    mut v___y_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_439_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0;
    v___x_440_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_439_, v___f_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_,
        v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_,
    );
    return v___x_440_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed(
    mut v___f_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
    mut v___y_451_: *mut LeanObject,
    mut v___y_452_: *mut LeanObject,
    mut v___y_453_: *mut LeanObject,
    mut v___y_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_455_: *mut LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5(
        v___f_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_,
        v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_,
    );
    lean_dec(v___y_453_);
    lean_dec_ref(v___y_452_);
    lean_dec(v___y_451_);
    lean_dec_ref(v___y_450_);
    lean_dec(v___y_449_);
    lean_dec_ref(v___y_448_);
    lean_dec(v___y_447_);
    lean_dec_ref(v___y_446_);
    lean_dec(v___y_445_);
    return v_res_455_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__6(
    mut v___x_456_: *mut LeanObject,
    mut v___f_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
    mut v___y_461_: *mut LeanObject,
    mut v___y_462_: *mut LeanObject,
    mut v___y_463_: *mut LeanObject,
    mut v___y_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_456_, v___f_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_,
        v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_,
    );
    return v___x_471_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed(
    mut v___x_472_: *mut LeanObject,
    mut v___f_473_: *mut LeanObject,
    mut v___y_474_: *mut LeanObject,
    mut v___y_475_: *mut LeanObject,
    mut v___y_476_: *mut LeanObject,
    mut v___y_477_: *mut LeanObject,
    mut v___y_478_: *mut LeanObject,
    mut v___y_479_: *mut LeanObject,
    mut v___y_480_: *mut LeanObject,
    mut v___y_481_: *mut LeanObject,
    mut v___y_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
    mut v___y_485_: *mut LeanObject,
    mut v___y_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_487_: *mut LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Lean_Meta_Grind_Action_mkFinish___lam__6(
        v___x_472_, v___f_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_,
        v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_,
    );
    lean_dec(v___y_485_);
    lean_dec_ref(v___y_484_);
    lean_dec(v___y_483_);
    lean_dec_ref(v___y_482_);
    lean_dec(v___y_481_);
    lean_dec_ref(v___y_480_);
    lean_dec(v___y_479_);
    lean_dec_ref(v___y_478_);
    lean_dec(v___y_477_);
    return v_res_487_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish(
    mut v_maxIterations_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_502_: u8 = 0;
    let mut v___f_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_498_ = l_Lean_Meta_Grind_Solvers_mkAction();
                if lean_obj_tag(v___x_498_) == 0 {
                    v_a_499_ = lean_ctor_get(v___x_498_, 0);
                    v_isSharedCheck_513_ = (!lean_is_exclusive(v___x_498_)) as u8;
                    if v_isSharedCheck_513_ == 0 {
                        v___x_501_ = v___x_498_;
                        v_isShared_502_ = v_isSharedCheck_513_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_499_);
                        lean_dec(v___x_498_);
                        v___x_501_ = lean_box(0);
                        v_isShared_502_ = v_isSharedCheck_513_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_maxIterations_496_);
                    return v___x_498_;
                }
            }
            1 => {
                v___f_503_ = l_Lean_Meta_Grind_Action_mkFinish___closed__2;
                v___f_504_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                lean_closure_set(v___f_504_, 0, v_a_499_);
                lean_closure_set(v___f_504_, 1, v___f_503_);
                v___f_505_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                lean_closure_set(v___f_505_, 0, v_maxIterations_496_);
                lean_closure_set(v___f_505_, 1, v___f_504_);
                v___f_506_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed as *mut core::ffi::c_void,
                    14,
                    1,
                );
                lean_closure_set(v___f_506_, 0, v___f_505_);
                v___f_507_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed as *mut core::ffi::c_void,
                    14,
                    1,
                );
                lean_closure_set(v___f_507_, 0, v___f_506_);
                v___x_508_ = l_Lean_Meta_Grind_Action_mkFinish___closed__3;
                v___f_509_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                lean_closure_set(v___f_509_, 0, v___x_508_);
                lean_closure_set(v___f_509_, 1, v___f_507_);
                if v_isShared_502_ == 0 {
                    lean_ctor_set(v___x_501_, 0, v___f_509_);
                    v___x_511_ = v___x_501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_512_, 0, v___f_509_);
                    v___x_511_ = v_reuseFailAlloc_512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___boxed(
    mut v_maxIterations_514_: *mut LeanObject,
    mut v_a_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Meta_Grind_Action_mkFinish(v_maxIterations_514_);
    return v_res_516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Action_maxIterationsDefault =
        _init_l_Lean_Meta_Grind_Action_maxIterationsDefault();
    lean_mark_persistent(l_Lean_Meta_Grind_Action_maxIterationsDefault);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Finish(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Finish(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
}
