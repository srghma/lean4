// Lean compiler output
// Module: Init.Data.Iterators.PostconditionMonad
// Imports: Init.Control.Lawful.Basic Init.Control.Lawful.MonadLift.Basic Init.Ext Init.NotationExtra Init.Data.Subtype.Basic Init.PropLemmas
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::Lawful::MonadLift::Basic::{
    initialize_Init_Control_Lawful_MonadLift_Basic,
    runtime_initialize_Init_Control_Lawful_MonadLift_Basic,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static l_Std_Iterators_PostconditionT_lift___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_PostconditionT_lift___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_PostconditionT_lift___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Iterators_PostconditionT_bind___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_PostconditionT_bind___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_PostconditionT_bind___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Iterators_PostconditionT_run___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_PostconditionT_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_PostconditionT_run___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Iterators_PostconditionT_lift___redArg___lam__0(
    mut v_x_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_292_);
    return v_x_292_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_lift___redArg___lam__0___boxed(
    mut v_x_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Iterators_PostconditionT_lift___redArg___lam__0(v_x_293_);
    crate::leanh::lean_dec(v_x_293_);
    return v_res_294_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_lift___redArg(
    mut v_inst_296_: *mut crate::leanh::LeanObject,
    mut v_x_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_298_ = crate::leanh::lean_ctor_get(v_inst_296_, 0);
    crate::leanh::lean_inc(v_map_298_);
    crate::leanh::lean_dec_ref(v_inst_296_);
    v___f_299_ = l_Std_Iterators_PostconditionT_lift___redArg___closed__0;
    v___x_300_ = crate::leanh::lean_apply_4(
        v_map_298_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_299_,
        v_x_297_,
    );
    return v___x_300_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_lift(
    mut v_00_u03b1_301_: *mut crate::leanh::LeanObject,
    mut v_m_302_: *mut crate::leanh::LeanObject,
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_x_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_305_ = crate::leanh::lean_ctor_get(v_inst_303_, 0);
    crate::leanh::lean_inc(v_map_305_);
    crate::leanh::lean_dec_ref(v_inst_303_);
    v___f_306_ = l_Std_Iterators_PostconditionT_lift___redArg___closed__0;
    v___x_307_ = crate::leanh::lean_apply_4(
        v_map_305_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_306_,
        v_x_304_,
    );
    return v___x_307_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_attachLift___redArg(
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_x_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = crate::leanh::lean_apply_2(v_inst_308_, crate::leanh::lean_box(0), v_x_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_attachLift(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_m_312_: *mut crate::leanh::LeanObject,
    mut v_inst_313_: *mut crate::leanh::LeanObject,
    mut v_x_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = crate::leanh::lean_apply_2(v_inst_313_, crate::leanh::lean_box(0), v_x_314_);
    return v___x_315_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_pure___redArg(
    mut v_inst_316_: *mut crate::leanh::LeanObject,
    mut v_a_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = crate::leanh::lean_apply_2(v_inst_316_, crate::leanh::lean_box(0), v_a_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_pure(
    mut v_m_319_: *mut crate::leanh::LeanObject,
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_321_: *mut crate::leanh::LeanObject,
    mut v_a_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = crate::leanh::lean_apply_2(v_inst_320_, crate::leanh::lean_box(0), v_a_322_);
    return v___x_323_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftWithProperty___redArg(
    mut v_x_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_324_);
    return v_x_324_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftWithProperty___redArg___boxed(
    mut v_x_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Iterators_PostconditionT_liftWithProperty___redArg(v_x_325_);
    crate::leanh::lean_dec(v_x_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftWithProperty(
    mut v_00_u03b1_327_: *mut crate::leanh::LeanObject,
    mut v_m_328_: *mut crate::leanh::LeanObject,
    mut v_P_329_: *mut crate::leanh::LeanObject,
    mut v_x_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_330_);
    return v_x_330_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftWithProperty___boxed(
    mut v_00_u03b1_331_: *mut crate::leanh::LeanObject,
    mut v_m_332_: *mut crate::leanh::LeanObject,
    mut v_P_333_: *mut crate::leanh::LeanObject,
    mut v_x_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_335_ = l_Std_Iterators_PostconditionT_liftWithProperty(
        v_00_u03b1_331_,
        v_m_332_,
        v_P_333_,
        v_x_334_,
    );
    crate::leanh::lean_dec(v_x_334_);
    return v_res_335_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_map___redArg___lam__0(
    mut v_f_336_: *mut crate::leanh::LeanObject,
    mut v_a_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = crate::leanh::lean_apply_1(v_f_336_, v_a_337_);
    return v___x_338_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_map___redArg(
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_f_340_: *mut crate::leanh::LeanObject,
    mut v_x_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_342_ = crate::leanh::lean_ctor_get(v_inst_339_, 0);
    crate::leanh::lean_inc(v_map_342_);
    crate::leanh::lean_dec_ref(v_inst_339_);
    v___f_343_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_343_, 0, v_f_340_);
    v___x_344_ = crate::leanh::lean_apply_4(
        v_map_342_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_343_,
        v_x_341_,
    );
    return v___x_344_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_map(
    mut v_m_345_: *mut crate::leanh::LeanObject,
    mut v_inst_346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_347_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_348_: *mut crate::leanh::LeanObject,
    mut v_f_349_: *mut crate::leanh::LeanObject,
    mut v_x_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_351_ = crate::leanh::lean_ctor_get(v_inst_346_, 0);
    crate::leanh::lean_inc(v_map_351_);
    crate::leanh::lean_dec_ref(v_inst_346_);
    v___f_352_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_352_, 0, v_f_349_);
    v___x_353_ = crate::leanh::lean_apply_4(
        v_map_351_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_352_,
        v_x_350_,
    );
    return v___x_353_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_bind___redArg___lam__0(
    mut v_b_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_b_354_);
    return v_b_354_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_bind___redArg___lam__0___boxed(
    mut v_b_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Iterators_PostconditionT_bind___redArg___lam__0(v_b_355_);
    crate::leanh::lean_dec(v_b_355_);
    return v_res_356_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_bind___redArg___lam__1(
    mut v_toFunctor_357_: *mut crate::leanh::LeanObject,
    mut v_f_358_: *mut crate::leanh::LeanObject,
    mut v___f_359_: *mut crate::leanh::LeanObject,
    mut v_a_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_361_ = crate::leanh::lean_ctor_get(v_toFunctor_357_, 0);
    crate::leanh::lean_inc(v_map_361_);
    crate::leanh::lean_dec_ref(v_toFunctor_357_);
    v___x_362_ = crate::leanh::lean_apply_1(v_f_358_, v_a_360_);
    v___x_363_ = crate::leanh::lean_apply_4(
        v_map_361_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_359_,
        v___x_362_,
    );
    return v___x_363_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_bind___redArg(
    mut v_inst_365_: *mut crate::leanh::LeanObject,
    mut v_x_366_: *mut crate::leanh::LeanObject,
    mut v_f_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = crate::leanh::lean_ctor_get(v_inst_365_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_368_);
    v_toBind_369_ = crate::leanh::lean_ctor_get(v_inst_365_, 1);
    crate::leanh::lean_inc(v_toBind_369_);
    crate::leanh::lean_dec_ref(v_inst_365_);
    v_toFunctor_370_ = crate::leanh::lean_ctor_get(v_toApplicative_368_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_370_);
    crate::leanh::lean_dec_ref(v_toApplicative_368_);
    v___f_371_ = l_Std_Iterators_PostconditionT_bind___redArg___closed__0;
    v___f_372_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_bind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_372_, 0, v_toFunctor_370_);
    crate::leanh::lean_closure_set(v___f_372_, 1, v_f_367_);
    crate::leanh::lean_closure_set(v___f_372_, 2, v___f_371_);
    v___x_373_ = crate::leanh::lean_apply_4(
        v_toBind_369_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_366_,
        v___f_372_,
    );
    return v___x_373_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_bind(
    mut v_m_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_376_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_377_: *mut crate::leanh::LeanObject,
    mut v_x_378_: *mut crate::leanh::LeanObject,
    mut v_f_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_380_ = crate::leanh::lean_ctor_get(v_inst_375_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_380_);
    v_toBind_381_ = crate::leanh::lean_ctor_get(v_inst_375_, 1);
    crate::leanh::lean_inc(v_toBind_381_);
    crate::leanh::lean_dec_ref(v_inst_375_);
    v_toFunctor_382_ = crate::leanh::lean_ctor_get(v_toApplicative_380_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_382_);
    crate::leanh::lean_dec_ref(v_toApplicative_380_);
    v___f_383_ = l_Std_Iterators_PostconditionT_bind___redArg___closed__0;
    v___f_384_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_bind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_384_, 0, v_toFunctor_382_);
    crate::leanh::lean_closure_set(v___f_384_, 1, v_f_379_);
    crate::leanh::lean_closure_set(v___f_384_, 2, v___f_383_);
    v___x_385_ = crate::leanh::lean_apply_4(
        v_toBind_381_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_378_,
        v___f_384_,
    );
    return v___x_385_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_pbind___redArg(
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_f_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_389_ = crate::leanh::lean_ctor_get(v_inst_386_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_389_);
    v_toBind_390_ = crate::leanh::lean_ctor_get(v_inst_386_, 1);
    crate::leanh::lean_inc(v_toBind_390_);
    crate::leanh::lean_dec_ref(v_inst_386_);
    v_toFunctor_391_ = crate::leanh::lean_ctor_get(v_toApplicative_389_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_391_);
    crate::leanh::lean_dec_ref(v_toApplicative_389_);
    v___f_392_ = l_Std_Iterators_PostconditionT_bind___redArg___closed__0;
    v___f_393_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_bind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_393_, 0, v_toFunctor_391_);
    crate::leanh::lean_closure_set(v___f_393_, 1, v_f_388_);
    crate::leanh::lean_closure_set(v___f_393_, 2, v___f_392_);
    v___x_394_ = crate::leanh::lean_apply_4(
        v_toBind_390_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_387_,
        v___f_393_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_pbind(
    mut v_m_395_: *mut crate::leanh::LeanObject,
    mut v_inst_396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_398_: *mut crate::leanh::LeanObject,
    mut v_x_399_: *mut crate::leanh::LeanObject,
    mut v_f_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_401_ = crate::leanh::lean_ctor_get(v_inst_396_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_401_);
    v_toBind_402_ = crate::leanh::lean_ctor_get(v_inst_396_, 1);
    crate::leanh::lean_inc(v_toBind_402_);
    crate::leanh::lean_dec_ref(v_inst_396_);
    v_toFunctor_403_ = crate::leanh::lean_ctor_get(v_toApplicative_401_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_403_);
    crate::leanh::lean_dec_ref(v_toApplicative_401_);
    v___f_404_ = l_Std_Iterators_PostconditionT_bind___redArg___closed__0;
    v___f_405_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_bind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_405_, 0, v_toFunctor_403_);
    crate::leanh::lean_closure_set(v___f_405_, 1, v_f_400_);
    crate::leanh::lean_closure_set(v___f_405_, 2, v___f_404_);
    v___x_406_ = crate::leanh::lean_apply_4(
        v_toBind_402_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_399_,
        v___f_405_,
    );
    return v___x_406_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftMap___redArg(
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_f_408_: *mut crate::leanh::LeanObject,
    mut v_x_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_410_ = crate::leanh::lean_ctor_get(v_inst_407_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_410_);
    crate::leanh::lean_dec_ref(v_inst_407_);
    v_toFunctor_411_ = crate::leanh::lean_ctor_get(v_toApplicative_410_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_411_);
    crate::leanh::lean_dec_ref(v_toApplicative_410_);
    v_map_412_ = crate::leanh::lean_ctor_get(v_toFunctor_411_, 0);
    crate::leanh::lean_inc(v_map_412_);
    crate::leanh::lean_dec_ref(v_toFunctor_411_);
    v___f_413_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_413_, 0, v_f_408_);
    v___x_414_ = crate::leanh::lean_apply_4(
        v_map_412_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_413_,
        v_x_409_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_liftMap(
    mut v_m_415_: *mut crate::leanh::LeanObject,
    mut v_inst_416_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_418_: *mut crate::leanh::LeanObject,
    mut v_f_419_: *mut crate::leanh::LeanObject,
    mut v_x_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_421_ = crate::leanh::lean_ctor_get(v_inst_416_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_421_);
    crate::leanh::lean_dec_ref(v_inst_416_);
    v_toFunctor_422_ = crate::leanh::lean_ctor_get(v_toApplicative_421_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_422_);
    crate::leanh::lean_dec_ref(v_toApplicative_421_);
    v_map_423_ = crate::leanh::lean_ctor_get(v_toFunctor_422_, 0);
    crate::leanh::lean_inc(v_map_423_);
    crate::leanh::lean_dec_ref(v_toFunctor_422_);
    v___f_424_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_424_, 0, v_f_419_);
    v___x_425_ = crate::leanh::lean_apply_4(
        v_map_423_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_424_,
        v_x_420_,
    );
    return v___x_425_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_run___redArg___lam__0(
    mut v_a_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_426_);
    return v_a_426_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_run___redArg___lam__0___boxed(
    mut v_a_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Std_Iterators_PostconditionT_run___redArg___lam__0(v_a_427_);
    crate::leanh::lean_dec(v_a_427_);
    return v_res_428_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_run___redArg(
    mut v_inst_430_: *mut crate::leanh::LeanObject,
    mut v_x_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_432_ = crate::leanh::lean_ctor_get(v_inst_430_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_432_);
    crate::leanh::lean_dec_ref(v_inst_430_);
    v_toFunctor_433_ = crate::leanh::lean_ctor_get(v_toApplicative_432_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_433_);
    crate::leanh::lean_dec_ref(v_toApplicative_432_);
    v_map_434_ = crate::leanh::lean_ctor_get(v_toFunctor_433_, 0);
    crate::leanh::lean_inc(v_map_434_);
    crate::leanh::lean_dec_ref(v_toFunctor_433_);
    v___f_435_ = l_Std_Iterators_PostconditionT_run___redArg___closed__0;
    v___x_436_ = crate::leanh::lean_apply_4(
        v_map_434_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_435_,
        v_x_431_,
    );
    return v___x_436_;
}
pub unsafe fn l_Std_Iterators_PostconditionT_run(
    mut v_m_437_: *mut crate::leanh::LeanObject,
    mut v_inst_438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_439_: *mut crate::leanh::LeanObject,
    mut v_x_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_441_ = crate::leanh::lean_ctor_get(v_inst_438_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_441_);
    crate::leanh::lean_dec_ref(v_inst_438_);
    v_toFunctor_442_ = crate::leanh::lean_ctor_get(v_toApplicative_441_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_442_);
    crate::leanh::lean_dec_ref(v_toApplicative_441_);
    v_map_443_ = crate::leanh::lean_ctor_get(v_toFunctor_442_, 0);
    crate::leanh::lean_inc(v_map_443_);
    crate::leanh::lean_dec_ref(v_toFunctor_442_);
    v___f_444_ = l_Std_Iterators_PostconditionT_run___redArg___closed__0;
    v___x_445_ = crate::leanh::lean_apply_4(
        v_map_443_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_444_,
        v_x_440_,
    );
    return v___x_445_;
}
pub unsafe fn l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(
    mut v___y_446_: *mut crate::leanh::LeanObject,
    mut v_a_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_446_);
    return v___y_446_;
}
pub unsafe fn l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed(
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v_a_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0(v___y_448_, v_a_449_);
    crate::leanh::lean_dec(v_a_449_);
    crate::leanh::lean_dec(v___y_448_);
    return v_res_450_;
}
pub unsafe fn l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1(
    mut v_inst_451_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_453_: *mut crate::leanh::LeanObject,
    mut v___y_454_: *mut crate::leanh::LeanObject,
    mut v___y_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_456_ = crate::leanh::lean_ctor_get(v_inst_451_, 0);
    crate::leanh::lean_inc(v_map_456_);
    crate::leanh::lean_dec_ref(v_inst_451_);
    v___f_457_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instFunctorPostconditionT___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_457_, 0, v___y_454_);
    v___x_458_ = crate::leanh::lean_apply_4(
        v_map_456_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_457_,
        v___y_455_,
    );
    return v___x_458_;
}
pub unsafe fn l_Std_Iterators_instFunctorPostconditionT___redArg(
    mut v_inst_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_459_);
    v___f_460_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instFunctorPostconditionT___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_460_, 0, v_inst_459_);
    v___x_461_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_PostconditionT_map as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___x_461_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_461_, 1, v_inst_459_);
    v___x_462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_462_, 0, v___x_461_);
    crate::leanh::lean_ctor_set(v___x_462_, 1, v___f_460_);
    return v___x_462_;
}
pub unsafe fn l_Std_Iterators_instFunctorPostconditionT(
    mut v_m_463_: *mut crate::leanh::LeanObject,
    mut v_inst_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Std_Iterators_instFunctorPostconditionT___redArg(v_inst_464_);
    return v___x_465_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(
    mut v_toFunctor_466_: *mut crate::leanh::LeanObject,
    mut v_y_467_: *mut crate::leanh::LeanObject,
    mut v___f_468_: *mut crate::leanh::LeanObject,
    mut v_a_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_470_ = crate::leanh::lean_ctor_get(v_toFunctor_466_, 0);
    crate::leanh::lean_inc(v_map_470_);
    crate::leanh::lean_dec_ref(v_toFunctor_466_);
    v___x_471_ = crate::leanh::lean_box(0);
    v___x_472_ = crate::leanh::lean_apply_1(v_y_467_, v___x_471_);
    v___x_473_ = crate::leanh::lean_apply_4(
        v_map_470_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_468_,
        v___x_472_,
    );
    return v___x_473_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed(
    mut v_toFunctor_474_: *mut crate::leanh::LeanObject,
    mut v_y_475_: *mut crate::leanh::LeanObject,
    mut v___f_476_: *mut crate::leanh::LeanObject,
    mut v_a_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Iterators_instMonadPostconditionT___redArg___lam__4(
        v_toFunctor_474_,
        v_y_475_,
        v___f_476_,
        v_a_477_,
    );
    crate::leanh::lean_dec(v_a_477_);
    return v_res_478_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__0(
    mut v_toFunctor_479_: *mut crate::leanh::LeanObject,
    mut v___f_480_: *mut crate::leanh::LeanObject,
    mut v_toBind_481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_482_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_483_: *mut crate::leanh::LeanObject,
    mut v_x_484_: *mut crate::leanh::LeanObject,
    mut v_y_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_486_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadPostconditionT___redArg___lam__4___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_486_, 0, v_toFunctor_479_);
    crate::leanh::lean_closure_set(v___f_486_, 1, v_y_485_);
    crate::leanh::lean_closure_set(v___f_486_, 2, v___f_480_);
    v___x_487_ = crate::leanh::lean_apply_4(
        v_toBind_481_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_484_,
        v___f_486_,
    );
    return v___x_487_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(
    mut v_toPure_488_: *mut crate::leanh::LeanObject,
    mut v_a_489_: *mut crate::leanh::LeanObject,
    mut v_map_490_: *mut crate::leanh::LeanObject,
    mut v___f_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = crate::leanh::lean_apply_2(v_toPure_488_, crate::leanh::lean_box(0), v_a_489_);
    v___x_494_ = crate::leanh::lean_apply_4(
        v_map_490_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_491_,
        v___x_493_,
    );
    return v___x_494_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed(
    mut v_toPure_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
    mut v_map_497_: *mut crate::leanh::LeanObject,
    mut v___f_498_: *mut crate::leanh::LeanObject,
    mut v_a_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Std_Iterators_instMonadPostconditionT___redArg___lam__1(
        v_toPure_495_,
        v_a_496_,
        v_map_497_,
        v___f_498_,
        v_a_499_,
    );
    crate::leanh::lean_dec(v_a_499_);
    return v_res_500_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__2(
    mut v_toFunctor_501_: *mut crate::leanh::LeanObject,
    mut v_toPure_502_: *mut crate::leanh::LeanObject,
    mut v___f_503_: *mut crate::leanh::LeanObject,
    mut v_y_504_: *mut crate::leanh::LeanObject,
    mut v_toBind_505_: *mut crate::leanh::LeanObject,
    mut v___f_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_508_ = crate::leanh::lean_ctor_get(v_toFunctor_501_, 0);
    crate::leanh::lean_inc_n(v_map_508_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_501_);
    v___f_509_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadPostconditionT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_509_, 0, v_toPure_502_);
    crate::leanh::lean_closure_set(v___f_509_, 1, v_a_507_);
    crate::leanh::lean_closure_set(v___f_509_, 2, v_map_508_);
    crate::leanh::lean_closure_set(v___f_509_, 3, v___f_503_);
    v___x_510_ = crate::leanh::lean_box(0);
    v___x_511_ = crate::leanh::lean_apply_1(v_y_504_, v___x_510_);
    v___x_512_ = crate::leanh::lean_apply_4(
        v_toBind_505_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_511_,
        v___f_509_,
    );
    v___x_513_ = crate::leanh::lean_apply_4(
        v_map_508_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_506_,
        v___x_512_,
    );
    return v___x_513_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__3(
    mut v_toFunctor_514_: *mut crate::leanh::LeanObject,
    mut v_toPure_515_: *mut crate::leanh::LeanObject,
    mut v___f_516_: *mut crate::leanh::LeanObject,
    mut v_toBind_517_: *mut crate::leanh::LeanObject,
    mut v___f_518_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_519_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_520_: *mut crate::leanh::LeanObject,
    mut v_x_521_: *mut crate::leanh::LeanObject,
    mut v_y_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_517_);
    v___f_523_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadPostconditionT___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_523_, 0, v_toFunctor_514_);
    crate::leanh::lean_closure_set(v___f_523_, 1, v_toPure_515_);
    crate::leanh::lean_closure_set(v___f_523_, 2, v___f_516_);
    crate::leanh::lean_closure_set(v___f_523_, 3, v_y_522_);
    crate::leanh::lean_closure_set(v___f_523_, 4, v_toBind_517_);
    crate::leanh::lean_closure_set(v___f_523_, 5, v___f_518_);
    v___x_524_ = crate::leanh::lean_apply_4(
        v_toBind_517_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_521_,
        v___f_523_,
    );
    return v___x_524_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__5(
    mut v_a_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = crate::leanh::lean_apply_1(v_a_525_, v_a_526_);
    return v___x_527_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__6(
    mut v_toFunctor_528_: *mut crate::leanh::LeanObject,
    mut v_x_529_: *mut crate::leanh::LeanObject,
    mut v___f_530_: *mut crate::leanh::LeanObject,
    mut v_a_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_532_ = crate::leanh::lean_ctor_get(v_toFunctor_528_, 0);
    crate::leanh::lean_inc_n(v_map_532_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_528_);
    v___f_533_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadPostconditionT___redArg___lam__5 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_533_, 0, v_a_531_);
    v___x_534_ = crate::leanh::lean_box(0);
    v___x_535_ = crate::leanh::lean_apply_1(v_x_529_, v___x_534_);
    v___x_536_ = crate::leanh::lean_apply_4(
        v_map_532_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_533_,
        v___x_535_,
    );
    v___x_537_ = crate::leanh::lean_apply_4(
        v_map_532_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_530_,
        v___x_536_,
    );
    return v___x_537_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg___lam__7(
    mut v_toFunctor_538_: *mut crate::leanh::LeanObject,
    mut v___f_539_: *mut crate::leanh::LeanObject,
    mut v_toBind_540_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_541_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_542_: *mut crate::leanh::LeanObject,
    mut v_f_543_: *mut crate::leanh::LeanObject,
    mut v_x_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_545_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadPostconditionT___redArg___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_545_, 0, v_toFunctor_538_);
    crate::leanh::lean_closure_set(v___f_545_, 1, v_x_544_);
    crate::leanh::lean_closure_set(v___f_545_, 2, v___f_539_);
    v___x_546_ = crate::leanh::lean_apply_4(
        v_toBind_540_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_543_,
        v___f_545_,
    );
    return v___x_546_;
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT___redArg(
    mut v_inst_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___f_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_unused_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_548_ = crate::leanh::lean_ctor_get(v_inst_547_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_548_);
                v_toBind_549_ = crate::leanh::lean_ctor_get(v_inst_547_, 1);
                v_toFunctor_550_ = crate::leanh::lean_ctor_get(v_toApplicative_548_, 0);
                v_toPure_551_ = crate::leanh::lean_ctor_get(v_toApplicative_548_, 1);
                v_isSharedCheck_566_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_548_)) as u8;
                if v_isSharedCheck_566_ == 0 {
                    v_unused_567_ = crate::leanh::lean_ctor_get(v_toApplicative_548_, 4);
                    crate::leanh::lean_dec(v_unused_567_);
                    v_unused_568_ = crate::leanh::lean_ctor_get(v_toApplicative_548_, 3);
                    crate::leanh::lean_dec(v_unused_568_);
                    v_unused_569_ = crate::leanh::lean_ctor_get(v_toApplicative_548_, 2);
                    crate::leanh::lean_dec(v_unused_569_);
                    v___x_553_ = v_toApplicative_548_;
                    v_isShared_554_ = v_isSharedCheck_566_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toPure_551_);
                    crate::leanh::lean_inc(v_toFunctor_550_);
                    crate::leanh::lean_dec(v_toApplicative_548_);
                    v___x_553_ = crate::leanh::lean_box(0);
                    v_isShared_554_ = v_isSharedCheck_566_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_555_ = l_Std_Iterators_PostconditionT_bind___redArg___closed__0;
                crate::leanh::lean_inc_n(v_toBind_549_, 3);
                crate::leanh::lean_inc_ref_n(v_toFunctor_550_, 3);
                v___f_556_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadPostconditionT___redArg___lam__0
                        as *mut core::ffi::c_void,
                    7,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_556_, 0, v_toFunctor_550_);
                crate::leanh::lean_closure_set(v___f_556_, 1, v___f_555_);
                crate::leanh::lean_closure_set(v___f_556_, 2, v_toBind_549_);
                crate::leanh::lean_inc(v_toPure_551_);
                v___f_557_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadPostconditionT___redArg___lam__3
                        as *mut core::ffi::c_void,
                    9,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_557_, 0, v_toFunctor_550_);
                crate::leanh::lean_closure_set(v___f_557_, 1, v_toPure_551_);
                crate::leanh::lean_closure_set(v___f_557_, 2, v___f_555_);
                crate::leanh::lean_closure_set(v___f_557_, 3, v_toBind_549_);
                crate::leanh::lean_closure_set(v___f_557_, 4, v___f_555_);
                v___f_558_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadPostconditionT___redArg___lam__7
                        as *mut core::ffi::c_void,
                    7,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_558_, 0, v_toFunctor_550_);
                crate::leanh::lean_closure_set(v___f_558_, 1, v___f_555_);
                crate::leanh::lean_closure_set(v___f_558_, 2, v_toBind_549_);
                v___x_559_ = l_Std_Iterators_instFunctorPostconditionT___redArg(v_toFunctor_550_);
                v___x_560_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_PostconditionT_pure as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_560_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_560_, 1, v_toPure_551_);
                if v_isShared_554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_553_, 4, v___f_556_);
                    crate::leanh::lean_ctor_set(v___x_553_, 3, v___f_557_);
                    crate::leanh::lean_ctor_set(v___x_553_, 2, v___f_558_);
                    crate::leanh::lean_ctor_set(v___x_553_, 1, v___x_560_);
                    crate::leanh::lean_ctor_set(v___x_553_, 0, v___x_559_);
                    v___x_562_ = v___x_553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_565_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 2, v___f_558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 3, v___f_557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 4, v___f_556_);
                    v___x_562_ = v_reuseFailAlloc_565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_563_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_PostconditionT_bind as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_563_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_563_, 1, v_inst_547_);
                v___x_564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_564_, 0, v___x_562_);
                crate::leanh::lean_ctor_set(v___x_564_, 1, v___x_563_);
                return v___x_564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_instMonadPostconditionT(
    mut v_m_570_: *mut crate::leanh::LeanObject,
    mut v_inst_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Std_Iterators_instMonadPostconditionT___redArg(v_inst_571_);
    return v___x_572_;
}
pub unsafe fn l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0(
    mut v_inst_573_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_574_: *mut crate::leanh::LeanObject,
    mut v_x_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = crate::leanh::lean_apply_2(v_inst_573_, crate::leanh::lean_box(0), v_x_575_);
    return v___x_576_;
}
pub unsafe fn l_Std_Iterators_instMonadLiftPostconditionT___redArg(
    mut v_inst_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_578_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_578_, 0, v_inst_577_);
    return v___f_578_;
}
pub unsafe fn l_Std_Iterators_instMonadLiftPostconditionT(
    mut v_m_579_: *mut crate::leanh::LeanObject,
    mut v_n_580_: *mut crate::leanh::LeanObject,
    mut v_inst_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_582_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadLiftPostconditionT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_582_, 0, v_inst_581_);
    return v___f_582_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_PostconditionMonad(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_PostconditionMonad(
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
pub unsafe fn initialize_Init_Data_Iterators_PostconditionMonad(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_PostconditionMonad(builtin);
}
