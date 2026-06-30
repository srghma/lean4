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
pub static mut l_Lean_Meta_Grind_Action_maxIterationsDefault: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Action_splitNext___boxed as *const core::ffi::c_void,
    m_arity: 15,
    m_num_fixed: 2,
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Action_instantiate___boxed as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Action_assertAll___boxed as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Action_intros___boxed as *const core::ffi::c_void,
    m_arity: 14,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_mbtc___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__2_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkFinish___closed__3_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_checkTactic___boxed as *const core::ffi::c_void,
        m_arity: 14,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_Action_mkFinish___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkFinish___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind_Action_maxIterationsDefault() -> *mut leanh::LeanObject
{
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_259_ = leanh::lean_unsigned_to_nat(10000);
    return v___x_259_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__0(
    mut v___f_264_: *mut leanh::LeanObject,
    mut v___y_265_: *mut leanh::LeanObject,
    mut v___y_266_: *mut leanh::LeanObject,
    mut v___y_267_: *mut leanh::LeanObject,
    mut v___y_268_: *mut leanh::LeanObject,
    mut v___y_269_: *mut leanh::LeanObject,
    mut v___y_270_: *mut leanh::LeanObject,
    mut v___y_271_: *mut leanh::LeanObject,
    mut v___y_272_: *mut leanh::LeanObject,
    mut v___y_273_: *mut leanh::LeanObject,
    mut v___y_274_: *mut leanh::LeanObject,
    mut v___y_275_: *mut leanh::LeanObject,
    mut v___y_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0;
    v___x_279_ = l_Lean_Meta_Grind_Action_orElse(
        v___x_278_, v___f_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_,
        v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_,
    );
    return v___x_279_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed(
    mut v___f_280_: *mut leanh::LeanObject,
    mut v___y_281_: *mut leanh::LeanObject,
    mut v___y_282_: *mut leanh::LeanObject,
    mut v___y_283_: *mut leanh::LeanObject,
    mut v___y_284_: *mut leanh::LeanObject,
    mut v___y_285_: *mut leanh::LeanObject,
    mut v___y_286_: *mut leanh::LeanObject,
    mut v___y_287_: *mut leanh::LeanObject,
    mut v___y_288_: *mut leanh::LeanObject,
    mut v___y_289_: *mut leanh::LeanObject,
    mut v___y_290_: *mut leanh::LeanObject,
    mut v___y_291_: *mut leanh::LeanObject,
    mut v___y_292_: *mut leanh::LeanObject,
    mut v___y_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0(
        v___f_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_,
        v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_,
    );
    leanh::lean_dec(v___y_292_);
    leanh::lean_dec_ref(v___y_291_);
    leanh::lean_dec(v___y_290_);
    leanh::lean_dec_ref(v___y_289_);
    leanh::lean_dec(v___y_288_);
    leanh::lean_dec_ref(v___y_287_);
    leanh::lean_dec(v___y_286_);
    leanh::lean_dec_ref(v___y_285_);
    leanh::lean_dec(v___y_284_);
    return v_res_294_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__1(
    mut v___f_296_: *mut leanh::LeanObject,
    mut v___y_297_: *mut leanh::LeanObject,
    mut v___y_298_: *mut leanh::LeanObject,
    mut v___y_299_: *mut leanh::LeanObject,
    mut v___y_300_: *mut leanh::LeanObject,
    mut v___y_301_: *mut leanh::LeanObject,
    mut v___y_302_: *mut leanh::LeanObject,
    mut v___y_303_: *mut leanh::LeanObject,
    mut v___y_304_: *mut leanh::LeanObject,
    mut v___y_305_: *mut leanh::LeanObject,
    mut v___y_306_: *mut leanh::LeanObject,
    mut v___y_307_: *mut leanh::LeanObject,
    mut v___y_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0;
    v___x_311_ = l_Lean_Meta_Grind_Action_orElse(
        v___x_310_, v___f_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_,
        v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_,
    );
    return v___x_311_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed(
    mut v___f_312_: *mut leanh::LeanObject,
    mut v___y_313_: *mut leanh::LeanObject,
    mut v___y_314_: *mut leanh::LeanObject,
    mut v___y_315_: *mut leanh::LeanObject,
    mut v___y_316_: *mut leanh::LeanObject,
    mut v___y_317_: *mut leanh::LeanObject,
    mut v___y_318_: *mut leanh::LeanObject,
    mut v___y_319_: *mut leanh::LeanObject,
    mut v___y_320_: *mut leanh::LeanObject,
    mut v___y_321_: *mut leanh::LeanObject,
    mut v___y_322_: *mut leanh::LeanObject,
    mut v___y_323_: *mut leanh::LeanObject,
    mut v___y_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1(
        v___f_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_,
        v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_,
    );
    leanh::lean_dec(v___y_324_);
    leanh::lean_dec_ref(v___y_323_);
    leanh::lean_dec(v___y_322_);
    leanh::lean_dec_ref(v___y_321_);
    leanh::lean_dec(v___y_320_);
    leanh::lean_dec_ref(v___y_319_);
    leanh::lean_dec(v___y_318_);
    leanh::lean_dec_ref(v___y_317_);
    leanh::lean_dec(v___y_316_);
    return v_res_326_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__2(
    mut v_a_327_: *mut leanh::LeanObject,
    mut v___f_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
    mut v___y_332_: *mut leanh::LeanObject,
    mut v___y_333_: *mut leanh::LeanObject,
    mut v___y_334_: *mut leanh::LeanObject,
    mut v___y_335_: *mut leanh::LeanObject,
    mut v___y_336_: *mut leanh::LeanObject,
    mut v___y_337_: *mut leanh::LeanObject,
    mut v___y_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
    mut v___y_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Meta_Grind_Action_orElse(
        v_a_327_, v___f_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_,
        v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_,
    );
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed(
    mut v_a_343_: *mut leanh::LeanObject,
    mut v___f_344_: *mut leanh::LeanObject,
    mut v___y_345_: *mut leanh::LeanObject,
    mut v___y_346_: *mut leanh::LeanObject,
    mut v___y_347_: *mut leanh::LeanObject,
    mut v___y_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
    mut v___y_352_: *mut leanh::LeanObject,
    mut v___y_353_: *mut leanh::LeanObject,
    mut v___y_354_: *mut leanh::LeanObject,
    mut v___y_355_: *mut leanh::LeanObject,
    mut v___y_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Lean_Meta_Grind_Action_mkFinish___lam__2(
        v_a_343_, v___f_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_,
        v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_,
    );
    leanh::lean_dec(v___y_356_);
    leanh::lean_dec_ref(v___y_355_);
    leanh::lean_dec(v___y_354_);
    leanh::lean_dec_ref(v___y_353_);
    leanh::lean_dec(v___y_352_);
    leanh::lean_dec_ref(v___y_351_);
    leanh::lean_dec(v___y_350_);
    leanh::lean_dec_ref(v___y_349_);
    leanh::lean_dec(v___y_348_);
    return v_res_358_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__3(
    mut v_maxIterations_359_: *mut leanh::LeanObject,
    mut v___f_360_: *mut leanh::LeanObject,
    mut v___y_361_: *mut leanh::LeanObject,
    mut v___y_362_: *mut leanh::LeanObject,
    mut v___y_363_: *mut leanh::LeanObject,
    mut v___y_364_: *mut leanh::LeanObject,
    mut v___y_365_: *mut leanh::LeanObject,
    mut v___y_366_: *mut leanh::LeanObject,
    mut v___y_367_: *mut leanh::LeanObject,
    mut v___y_368_: *mut leanh::LeanObject,
    mut v___y_369_: *mut leanh::LeanObject,
    mut v___y_370_: *mut leanh::LeanObject,
    mut v___y_371_: *mut leanh::LeanObject,
    mut v___y_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_maxIterations_375_: *mut leanh::LeanObject,
    mut v___f_376_: *mut leanh::LeanObject,
    mut v___y_377_: *mut leanh::LeanObject,
    mut v___y_378_: *mut leanh::LeanObject,
    mut v___y_379_: *mut leanh::LeanObject,
    mut v___y_380_: *mut leanh::LeanObject,
    mut v___y_381_: *mut leanh::LeanObject,
    mut v___y_382_: *mut leanh::LeanObject,
    mut v___y_383_: *mut leanh::LeanObject,
    mut v___y_384_: *mut leanh::LeanObject,
    mut v___y_385_: *mut leanh::LeanObject,
    mut v___y_386_: *mut leanh::LeanObject,
    mut v___y_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
    mut v___y_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_390_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_388_);
    leanh::lean_dec_ref(v___y_387_);
    leanh::lean_dec(v___y_386_);
    leanh::lean_dec_ref(v___y_385_);
    leanh::lean_dec(v___y_384_);
    leanh::lean_dec_ref(v___y_383_);
    leanh::lean_dec(v___y_382_);
    leanh::lean_dec_ref(v___y_381_);
    leanh::lean_dec(v___y_380_);
    leanh::lean_dec_ref(v___y_378_);
    leanh::lean_dec(v_maxIterations_375_);
    return v_res_390_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__4(
    mut v___f_392_: *mut leanh::LeanObject,
    mut v___y_393_: *mut leanh::LeanObject,
    mut v___y_394_: *mut leanh::LeanObject,
    mut v___y_395_: *mut leanh::LeanObject,
    mut v___y_396_: *mut leanh::LeanObject,
    mut v___y_397_: *mut leanh::LeanObject,
    mut v___y_398_: *mut leanh::LeanObject,
    mut v___y_399_: *mut leanh::LeanObject,
    mut v___y_400_: *mut leanh::LeanObject,
    mut v___y_401_: *mut leanh::LeanObject,
    mut v___y_402_: *mut leanh::LeanObject,
    mut v___y_403_: *mut leanh::LeanObject,
    mut v___y_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0;
    v___x_407_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_406_, v___f_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_,
        v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_,
    );
    return v___x_407_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed(
    mut v___f_408_: *mut leanh::LeanObject,
    mut v___y_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
    mut v___y_414_: *mut leanh::LeanObject,
    mut v___y_415_: *mut leanh::LeanObject,
    mut v___y_416_: *mut leanh::LeanObject,
    mut v___y_417_: *mut leanh::LeanObject,
    mut v___y_418_: *mut leanh::LeanObject,
    mut v___y_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
    mut v___y_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4(
        v___f_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_,
        v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_,
    );
    leanh::lean_dec(v___y_420_);
    leanh::lean_dec_ref(v___y_419_);
    leanh::lean_dec(v___y_418_);
    leanh::lean_dec_ref(v___y_417_);
    leanh::lean_dec(v___y_416_);
    leanh::lean_dec_ref(v___y_415_);
    leanh::lean_dec(v___y_414_);
    leanh::lean_dec_ref(v___y_413_);
    leanh::lean_dec(v___y_412_);
    return v_res_422_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__5(
    mut v___f_425_: *mut leanh::LeanObject,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
    mut v___y_428_: *mut leanh::LeanObject,
    mut v___y_429_: *mut leanh::LeanObject,
    mut v___y_430_: *mut leanh::LeanObject,
    mut v___y_431_: *mut leanh::LeanObject,
    mut v___y_432_: *mut leanh::LeanObject,
    mut v___y_433_: *mut leanh::LeanObject,
    mut v___y_434_: *mut leanh::LeanObject,
    mut v___y_435_: *mut leanh::LeanObject,
    mut v___y_436_: *mut leanh::LeanObject,
    mut v___y_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0;
    v___x_440_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_439_, v___f_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_,
        v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_,
    );
    return v___x_440_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed(
    mut v___f_441_: *mut leanh::LeanObject,
    mut v___y_442_: *mut leanh::LeanObject,
    mut v___y_443_: *mut leanh::LeanObject,
    mut v___y_444_: *mut leanh::LeanObject,
    mut v___y_445_: *mut leanh::LeanObject,
    mut v___y_446_: *mut leanh::LeanObject,
    mut v___y_447_: *mut leanh::LeanObject,
    mut v___y_448_: *mut leanh::LeanObject,
    mut v___y_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
    mut v___y_454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_455_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5(
        v___f_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_,
        v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_,
    );
    leanh::lean_dec(v___y_453_);
    leanh::lean_dec_ref(v___y_452_);
    leanh::lean_dec(v___y_451_);
    leanh::lean_dec_ref(v___y_450_);
    leanh::lean_dec(v___y_449_);
    leanh::lean_dec_ref(v___y_448_);
    leanh::lean_dec(v___y_447_);
    leanh::lean_dec_ref(v___y_446_);
    leanh::lean_dec(v___y_445_);
    return v_res_455_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__6(
    mut v___x_456_: *mut leanh::LeanObject,
    mut v___f_457_: *mut leanh::LeanObject,
    mut v___y_458_: *mut leanh::LeanObject,
    mut v___y_459_: *mut leanh::LeanObject,
    mut v___y_460_: *mut leanh::LeanObject,
    mut v___y_461_: *mut leanh::LeanObject,
    mut v___y_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_456_, v___f_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_,
        v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_,
    );
    return v___x_471_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed(
    mut v___x_472_: *mut leanh::LeanObject,
    mut v___f_473_: *mut leanh::LeanObject,
    mut v___y_474_: *mut leanh::LeanObject,
    mut v___y_475_: *mut leanh::LeanObject,
    mut v___y_476_: *mut leanh::LeanObject,
    mut v___y_477_: *mut leanh::LeanObject,
    mut v___y_478_: *mut leanh::LeanObject,
    mut v___y_479_: *mut leanh::LeanObject,
    mut v___y_480_: *mut leanh::LeanObject,
    mut v___y_481_: *mut leanh::LeanObject,
    mut v___y_482_: *mut leanh::LeanObject,
    mut v___y_483_: *mut leanh::LeanObject,
    mut v___y_484_: *mut leanh::LeanObject,
    mut v___y_485_: *mut leanh::LeanObject,
    mut v___y_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Lean_Meta_Grind_Action_mkFinish___lam__6(
        v___x_472_, v___f_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_,
        v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_,
    );
    leanh::lean_dec(v___y_485_);
    leanh::lean_dec_ref(v___y_484_);
    leanh::lean_dec(v___y_483_);
    leanh::lean_dec_ref(v___y_482_);
    leanh::lean_dec(v___y_481_);
    leanh::lean_dec_ref(v___y_480_);
    leanh::lean_dec(v___y_479_);
    leanh::lean_dec_ref(v___y_478_);
    leanh::lean_dec(v___y_477_);
    return v_res_487_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkFinish(
    mut v_maxIterations_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_502_: u8 = 0;
    let mut v___f_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_498_ = l_Lean_Meta_Grind_Solvers_mkAction();
                if leanh::lean_obj_tag(v___x_498_) == 0 {
                    v_a_499_ = leanh::lean_ctor_get(v___x_498_, 0);
                    v_isSharedCheck_513_ = (!leanh::lean_is_exclusive(v___x_498_)) as u8;
                    if v_isSharedCheck_513_ == 0 {
                        v___x_501_ = v___x_498_;
                        v_isShared_502_ = v_isSharedCheck_513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_499_);
                        leanh::lean_dec(v___x_498_);
                        v___x_501_ = leanh::lean_box(0);
                        v_isShared_502_ = v_isSharedCheck_513_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_maxIterations_496_);
                    return v___x_498_;
                }
            }
            1 => {
                v___f_503_ = l_Lean_Meta_Grind_Action_mkFinish___closed__2;
                v___f_504_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                leanh::lean_closure_set(v___f_504_, 0, v_a_499_);
                leanh::lean_closure_set(v___f_504_, 1, v___f_503_);
                v___f_505_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                leanh::lean_closure_set(v___f_505_, 0, v_maxIterations_496_);
                leanh::lean_closure_set(v___f_505_, 1, v___f_504_);
                v___f_506_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed as *mut core::ffi::c_void,
                    14,
                    1,
                );
                leanh::lean_closure_set(v___f_506_, 0, v___f_505_);
                v___f_507_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed as *mut core::ffi::c_void,
                    14,
                    1,
                );
                leanh::lean_closure_set(v___f_507_, 0, v___f_506_);
                v___x_508_ = l_Lean_Meta_Grind_Action_mkFinish___closed__3;
                v___f_509_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                leanh::lean_closure_set(v___f_509_, 0, v___x_508_);
                leanh::lean_closure_set(v___f_509_, 1, v___f_507_);
                if v_isShared_502_ == 0 {
                    leanh::lean_ctor_set(v___x_501_, 0, v___f_509_);
                    v___x_511_ = v___x_501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_512_, 0, v___f_509_);
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
    mut v_maxIterations_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Meta_Grind_Action_mkFinish(v_maxIterations_514_);
    return v_res_516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Finish(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Action_maxIterationsDefault =
        _init_l_Lean_Meta_Grind_Action_maxIterationsDefault();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Action_maxIterationsDefault);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Finish(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Finish(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
}