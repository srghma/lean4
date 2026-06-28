// Lean compiler output
// Module: Init.Control.ExceptCps
// Imports: Init.Control.Lawful.Basic Init.SimpLemmas
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::MonadAttach::l_MonadAttach_trivial___redArg;
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_7, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
};
pub static l_ExceptCpsT_instMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptCpsT_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__2 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value) as *mut LeanObject],
};
static mut l_ExceptCpsT_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__1_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptCpsT_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__2_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__3_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__5 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value) as *mut LeanObject],
};
static mut l_ExceptCpsT_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__3_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__7 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptCpsT_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__5_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__10 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value) as *mut LeanObject],
};
static mut l_ExceptCpsT_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__5_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ExceptCpsT_instMonad___lam__12 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ExceptCpsT_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__6_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_ExceptCpsT_instMonad___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__7_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_ExceptCpsT_instMonad___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__8_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonad___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_ExceptCpsT_instMonad___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__9_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonadExceptOf___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonadExceptOf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__0_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonadExceptOf___lam__2 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonadExceptOf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__1_value) as *mut LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_ExceptCpsT_instMonadExceptOf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__2_value) as *mut LeanObject;
static mut l_ExceptCpsT_instMonadAttach___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ExceptCpsT_instMonadAttach___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_ExceptCpsT_run___redArg___lam__0(
    mut v_toPure_307_: *mut LeanObject,
    mut v_a_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_309_, 0, v_a_308_);
    v___x_310_ = lean_apply_2(v_toPure_307_, lean_box(0), v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_ExceptCpsT_run___redArg___lam__1(
    mut v_toPure_311_: *mut LeanObject,
    mut v_e_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_313_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_313_, 0, v_e_312_);
    v___x_314_ = lean_apply_2(v_toPure_311_, lean_box(0), v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_ExceptCpsT_run___redArg(
    mut v_inst_315_: *mut LeanObject,
    mut v_x_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_317_ = lean_ctor_get(v_inst_315_, 0);
    lean_inc_ref(v_toApplicative_317_);
    lean_dec_ref(v_inst_315_);
    v_toPure_318_ = lean_ctor_get(v_toApplicative_317_, 1);
    lean_inc_n(v_toPure_318_, 2);
    lean_dec_ref(v_toApplicative_317_);
    v___f_319_ = lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_319_, 0, v_toPure_318_);
    v___f_320_ = lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_320_, 0, v_toPure_318_);
    v___x_321_ = lean_apply_3(v_x_316_, lean_box(0), v___f_319_, v___f_320_);
    return v___x_321_;
}
pub unsafe fn l_ExceptCpsT_run(
    mut v_m_322_: *mut LeanObject,
    mut v_00_u03b5_323_: *mut LeanObject,
    mut v_00_u03b1_324_: *mut LeanObject,
    mut v_inst_325_: *mut LeanObject,
    mut v_x_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_327_ = lean_ctor_get(v_inst_325_, 0);
    lean_inc_ref(v_toApplicative_327_);
    lean_dec_ref(v_inst_325_);
    v_toPure_328_ = lean_ctor_get(v_toApplicative_327_, 1);
    lean_inc_n(v_toPure_328_, 2);
    lean_dec_ref(v_toApplicative_327_);
    v___f_329_ = lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_329_, 0, v_toPure_328_);
    v___f_330_ = lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_330_, 0, v_toPure_328_);
    v___x_331_ = lean_apply_3(v_x_326_, lean_box(0), v___f_329_, v___f_330_);
    return v___x_331_;
}
pub unsafe fn l_ExceptCpsT_runK___redArg(
    mut v_x_332_: *mut LeanObject,
    mut v_ok_333_: *mut LeanObject,
    mut v_error_334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_335_ = lean_apply_3(v_x_332_, lean_box(0), v_ok_333_, v_error_334_);
    return v___x_335_;
}
pub unsafe fn l_ExceptCpsT_runK(
    mut v_m_336_: *mut LeanObject,
    mut v_00_u03b2_337_: *mut LeanObject,
    mut v_00_u03b5_338_: *mut LeanObject,
    mut v_00_u03b1_339_: *mut LeanObject,
    mut v_x_340_: *mut LeanObject,
    mut v_s_341_: *mut LeanObject,
    mut v_ok_342_: *mut LeanObject,
    mut v_error_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v___x_344_ = lean_apply_3(v_x_340_, lean_box(0), v_ok_342_, v_error_343_);
    return v___x_344_;
}
pub unsafe fn l_ExceptCpsT_runK___boxed(
    mut v_m_345_: *mut LeanObject,
    mut v_00_u03b2_346_: *mut LeanObject,
    mut v_00_u03b5_347_: *mut LeanObject,
    mut v_00_u03b1_348_: *mut LeanObject,
    mut v_x_349_: *mut LeanObject,
    mut v_s_350_: *mut LeanObject,
    mut v_ok_351_: *mut LeanObject,
    mut v_error_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_353_: *mut LeanObject = core::ptr::null_mut();
    v_res_353_ = l_ExceptCpsT_runK(
        v_m_345_,
        v_00_u03b2_346_,
        v_00_u03b5_347_,
        v_00_u03b1_348_,
        v_x_349_,
        v_s_350_,
        v_ok_351_,
        v_error_352_,
    );
    lean_dec(v_s_350_);
    return v_res_353_;
}
pub unsafe fn l_ExceptCpsT_runCatch___redArg(
    mut v_inst_354_: *mut LeanObject,
    mut v_x_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_356_ = lean_ctor_get(v_inst_354_, 0);
    lean_inc_ref(v_toApplicative_356_);
    lean_dec_ref(v_inst_354_);
    v_toPure_357_ = lean_ctor_get(v_toApplicative_356_, 1);
    lean_inc(v_toPure_357_);
    lean_dec_ref(v_toApplicative_356_);
    v___x_358_ = lean_apply_1(v_toPure_357_, lean_box(0));
    lean_inc(v___x_358_);
    v___x_359_ = lean_apply_3(v_x_355_, lean_box(0), v___x_358_, v___x_358_);
    return v___x_359_;
}
pub unsafe fn l_ExceptCpsT_runCatch(
    mut v_m_360_: *mut LeanObject,
    mut v_00_u03b1_361_: *mut LeanObject,
    mut v_inst_362_: *mut LeanObject,
    mut v_x_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_364_ = lean_ctor_get(v_inst_362_, 0);
    lean_inc_ref(v_toApplicative_364_);
    lean_dec_ref(v_inst_362_);
    v_toPure_365_ = lean_ctor_get(v_toApplicative_364_, 1);
    lean_inc(v_toPure_365_);
    lean_dec_ref(v_toApplicative_364_);
    v___x_366_ = lean_apply_1(v_toPure_365_, lean_box(0));
    lean_inc(v___x_366_);
    v___x_367_ = lean_apply_3(v_x_363_, lean_box(0), v___x_366_, v___x_366_);
    return v___x_367_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__0(
    mut v_f_368_: *mut LeanObject,
    mut v_k_u2081_369_: *mut LeanObject,
    mut v_a_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = lean_apply_1(v_f_368_, v_a_370_);
    v___x_372_ = lean_apply_1(v_k_u2081_369_, v___x_371_);
    return v___x_372_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__1(
    mut v_00_u03b1_373_: *mut LeanObject,
    mut v_00_u03b2_374_: *mut LeanObject,
    mut v_f_375_: *mut LeanObject,
    mut v_x_376_: *mut LeanObject,
    mut v_x_377_: *mut LeanObject,
    mut v_k_u2081_378_: *mut LeanObject,
    mut v_k_u2082_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___f_380_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_380_, 0, v_f_375_);
    lean_closure_set(v___f_380_, 1, v_k_u2081_378_);
    v___x_381_ = lean_apply_3(v_x_376_, lean_box(0), v___f_380_, v_k_u2082_379_);
    return v___x_381_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__2(
    mut v___f_382_: *mut LeanObject,
    mut v_00_u03b1_383_: *mut LeanObject,
    mut v_00_u03b2_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
    mut v___y_388_: *mut LeanObject,
    mut v___y_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_390_, 0, lean_box(0));
    lean_closure_set(v___x_390_, 1, lean_box(0));
    lean_closure_set(v___x_390_, 2, v___y_385_);
    v___x_391_ = lean_apply_7(
        v___f_382_,
        lean_box(0),
        lean_box(0),
        v___x_390_,
        v___y_386_,
        lean_box(0),
        v___y_388_,
        v___y_389_,
    );
    return v___x_391_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__3(
    mut v_00_u03b1_392_: *mut LeanObject,
    mut v_a_393_: *mut LeanObject,
    mut v_x_394_: *mut LeanObject,
    mut v_k_395_: *mut LeanObject,
    mut v_x_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_397_ = lean_apply_1(v_k_395_, v_a_393_);
    return v___x_397_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__3___boxed(
    mut v_00_u03b1_398_: *mut LeanObject,
    mut v_a_399_: *mut LeanObject,
    mut v_x_400_: *mut LeanObject,
    mut v_k_401_: *mut LeanObject,
    mut v_x_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_403_: *mut LeanObject = core::ptr::null_mut();
    v_res_403_ =
        l_ExceptCpsT_instMonad___lam__3(v_00_u03b1_398_, v_a_399_, v_x_400_, v_k_401_, v_x_402_);
    lean_dec(v_x_402_);
    return v_res_403_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__4(
    mut v_x_404_: *mut LeanObject,
    mut v___f_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
    mut v___y_407_: *mut LeanObject,
    mut v_a_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_409_ = lean_box(0);
    v___x_410_ = lean_apply_1(v_x_404_, v___x_409_);
    v___x_411_ = lean_apply_7(
        v___f_405_,
        lean_box(0),
        lean_box(0),
        v_a_408_,
        v___x_410_,
        lean_box(0),
        v___y_406_,
        v___y_407_,
    );
    return v___x_411_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__5(
    mut v___f_412_: *mut LeanObject,
    mut v_00_u03b1_413_: *mut LeanObject,
    mut v_00_u03b2_414_: *mut LeanObject,
    mut v_f_415_: *mut LeanObject,
    mut v_x_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_419_);
    v___f_420_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_420_, 0, v_x_416_);
    lean_closure_set(v___f_420_, 1, v___f_412_);
    lean_closure_set(v___f_420_, 2, v___y_418_);
    lean_closure_set(v___f_420_, 3, v___y_419_);
    v___x_421_ = lean_apply_3(v_f_415_, lean_box(0), v___f_420_, v___y_419_);
    return v___x_421_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__6(
    mut v_f_422_: *mut LeanObject,
    mut v_k_u2081_423_: *mut LeanObject,
    mut v_k_u2082_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    v___x_426_ = lean_apply_4(
        v_f_422_,
        v_a_425_,
        lean_box(0),
        v_k_u2081_423_,
        v_k_u2082_424_,
    );
    return v___x_426_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__7(
    mut v_00_u03b1_427_: *mut LeanObject,
    mut v_00_u03b2_428_: *mut LeanObject,
    mut v_x_429_: *mut LeanObject,
    mut v_f_430_: *mut LeanObject,
    mut v_x_431_: *mut LeanObject,
    mut v_k_u2081_432_: *mut LeanObject,
    mut v_k_u2082_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_k_u2082_433_);
    v___f_434_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_434_, 0, v_f_430_);
    lean_closure_set(v___f_434_, 1, v_k_u2081_432_);
    lean_closure_set(v___f_434_, 2, v_k_u2082_433_);
    v___x_435_ = lean_apply_3(v_x_429_, lean_box(0), v___f_434_, v_k_u2082_433_);
    return v___x_435_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__8(
    mut v_a_436_: *mut LeanObject,
    mut v_x_437_: *mut LeanObject,
    mut v___y_438_: *mut LeanObject,
    mut v___y_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_apply_1(v___y_439_, v_a_436_);
    return v___x_441_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__8___boxed(
    mut v_a_442_: *mut LeanObject,
    mut v_x_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_res_447_ =
        l_ExceptCpsT_instMonad___lam__8(v_a_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_);
    lean_dec(v___y_446_);
    lean_dec(v_x_443_);
    return v_res_447_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__9(
    mut v_y_448_: *mut LeanObject,
    mut v___f_449_: *mut LeanObject,
    mut v_a_450_: *mut LeanObject,
    mut v___y_451_: *mut LeanObject,
    mut v___y_452_: *mut LeanObject,
    mut v___y_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    v___f_454_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__8___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_454_, 0, v_a_450_);
    v___x_455_ = lean_box(0);
    v___x_456_ = lean_apply_1(v_y_448_, v___x_455_);
    v___x_457_ = lean_apply_7(
        v___f_449_,
        lean_box(0),
        lean_box(0),
        v___x_456_,
        v___f_454_,
        lean_box(0),
        v___y_452_,
        v___y_453_,
    );
    return v___x_457_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__10(
    mut v___f_458_: *mut LeanObject,
    mut v_00_u03b1_459_: *mut LeanObject,
    mut v_00_u03b2_460_: *mut LeanObject,
    mut v_x_461_: *mut LeanObject,
    mut v_y_462_: *mut LeanObject,
    mut v___y_463_: *mut LeanObject,
    mut v___y_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___f_458_);
    v___f_466_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__9 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_466_, 0, v_y_462_);
    lean_closure_set(v___f_466_, 1, v___f_458_);
    v___x_467_ = lean_apply_7(
        v___f_458_,
        lean_box(0),
        lean_box(0),
        v_x_461_,
        v___f_466_,
        lean_box(0),
        v___y_464_,
        v___y_465_,
    );
    return v___x_467_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__11(
    mut v_y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
    mut v___y_470_: *mut LeanObject,
    mut v_a_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_box(0);
    v___x_473_ = lean_apply_4(v_y_468_, v___x_472_, lean_box(0), v___y_469_, v___y_470_);
    return v___x_473_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__11___boxed(
    mut v_y_474_: *mut LeanObject,
    mut v___y_475_: *mut LeanObject,
    mut v___y_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_ExceptCpsT_instMonad___lam__11(v_y_474_, v___y_475_, v___y_476_, v_a_477_);
    lean_dec(v_a_477_);
    return v_res_478_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__12(
    mut v_00_u03b1_479_: *mut LeanObject,
    mut v_00_u03b2_480_: *mut LeanObject,
    mut v_x_481_: *mut LeanObject,
    mut v_y_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
    mut v___y_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_485_);
    v___f_486_ = lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__11___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_486_, 0, v_y_482_);
    lean_closure_set(v___f_486_, 1, v___y_484_);
    lean_closure_set(v___f_486_, 2, v___y_485_);
    v___x_487_ = lean_apply_3(v_x_481_, lean_box(0), v___f_486_, v___y_485_);
    return v___x_487_;
}
pub unsafe fn l_ExceptCpsT_instMonad(
    mut v_00_u03b5_510_: *mut LeanObject,
    mut v_m_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_512_ = l_ExceptCpsT_instMonad___closed__9;
    return v___x_512_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__0(
    mut v_00_u03b1_513_: *mut LeanObject,
    mut v_e_514_: *mut LeanObject,
    mut v_x_515_: *mut LeanObject,
    mut v_x_516_: *mut LeanObject,
    mut v_k_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    v___x_518_ = lean_apply_1(v_k_517_, v_e_514_);
    return v___x_518_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__0___boxed(
    mut v_00_u03b1_519_: *mut LeanObject,
    mut v_e_520_: *mut LeanObject,
    mut v_x_521_: *mut LeanObject,
    mut v_x_522_: *mut LeanObject,
    mut v_k_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v_res_524_ = l_ExceptCpsT_instMonadExceptOf___lam__0(
        v_00_u03b1_519_,
        v_e_520_,
        v_x_521_,
        v_x_522_,
        v_k_523_,
    );
    lean_dec(v_x_522_);
    return v_res_524_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__1(
    mut v_handle_525_: *mut LeanObject,
    mut v_k_u2081_526_: *mut LeanObject,
    mut v_k_u2082_527_: *mut LeanObject,
    mut v_e_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_apply_4(
        v_handle_525_,
        v_e_528_,
        lean_box(0),
        v_k_u2081_526_,
        v_k_u2082_527_,
    );
    return v___x_529_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__2(
    mut v_00_u03b1_530_: *mut LeanObject,
    mut v_x_531_: *mut LeanObject,
    mut v_handle_532_: *mut LeanObject,
    mut v_x_533_: *mut LeanObject,
    mut v_k_u2081_534_: *mut LeanObject,
    mut v_k_u2082_535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_k_u2081_534_);
    v___f_536_ = lean_alloc_closure(
        l_ExceptCpsT_instMonadExceptOf___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_536_, 0, v_handle_532_);
    lean_closure_set(v___f_536_, 1, v_k_u2081_534_);
    lean_closure_set(v___f_536_, 2, v_k_u2082_535_);
    v___x_537_ = lean_apply_3(v_x_531_, lean_box(0), v_k_u2081_534_, v___f_536_);
    return v___x_537_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf(
    mut v_00_u03b5_543_: *mut LeanObject,
    mut v_m_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_545_ = l_ExceptCpsT_instMonadExceptOf___closed__2;
    return v___x_545_;
}
pub unsafe fn l_ExceptCpsT_lift___redArg(
    mut v_inst_546_: *mut LeanObject,
    mut v_x_547_: *mut LeanObject,
    mut v_k_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_549_ = lean_ctor_get(v_inst_546_, 1);
    lean_inc(v_toBind_549_);
    lean_dec_ref(v_inst_546_);
    v___x_550_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v_x_547_, v_k_548_);
    return v___x_550_;
}
pub unsafe fn l_ExceptCpsT_lift(
    mut v_m_551_: *mut LeanObject,
    mut v_00_u03b1_552_: *mut LeanObject,
    mut v_00_u03b5_553_: *mut LeanObject,
    mut v_inst_554_: *mut LeanObject,
    mut v_x_555_: *mut LeanObject,
    mut v_x_556_: *mut LeanObject,
    mut v_k_557_: *mut LeanObject,
    mut v_x_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_559_ = lean_ctor_get(v_inst_554_, 1);
    lean_inc(v_toBind_559_);
    lean_dec_ref(v_inst_554_);
    v___x_560_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v_x_555_, v_k_557_);
    return v___x_560_;
}
pub unsafe fn l_ExceptCpsT_lift___boxed(
    mut v_m_561_: *mut LeanObject,
    mut v_00_u03b1_562_: *mut LeanObject,
    mut v_00_u03b5_563_: *mut LeanObject,
    mut v_inst_564_: *mut LeanObject,
    mut v_x_565_: *mut LeanObject,
    mut v_x_566_: *mut LeanObject,
    mut v_k_567_: *mut LeanObject,
    mut v_x_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_569_: *mut LeanObject = core::ptr::null_mut();
    v_res_569_ = l_ExceptCpsT_lift(
        v_m_561_,
        v_00_u03b1_562_,
        v_00_u03b5_563_,
        v_inst_564_,
        v_x_565_,
        v_x_566_,
        v_k_567_,
        v_x_568_,
    );
    lean_dec(v_x_568_);
    return v_res_569_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(
    mut v_inst_570_: *mut LeanObject,
    mut v_00_u03b1_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
    mut v___y_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_576_ = lean_ctor_get(v_inst_570_, 1);
    lean_inc(v_toBind_576_);
    lean_dec_ref(v_inst_570_);
    v___x_577_ = lean_apply_4(
        v_toBind_576_,
        lean_box(0),
        lean_box(0),
        v___y_572_,
        v___y_574_,
    );
    return v___x_577_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed(
    mut v_inst_578_: *mut LeanObject,
    mut v_00_u03b1_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(
        v_inst_578_,
        v_00_u03b1_579_,
        v___y_580_,
        v___y_581_,
        v___y_582_,
        v___y_583_,
    );
    lean_dec(v___y_583_);
    return v_res_584_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg(
    mut v_inst_585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_586_: *mut LeanObject = core::ptr::null_mut();
    v___f_586_ = lean_alloc_closure(
        l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_586_, 0, v_inst_585_);
    return v___f_586_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad(
    mut v_m_587_: *mut LeanObject,
    mut v_00_u03c3_588_: *mut LeanObject,
    mut v_inst_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_590_: *mut LeanObject = core::ptr::null_mut();
    v___f_590_ = lean_alloc_closure(
        l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_590_, 0, v_inst_589_);
    return v___f_590_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg___lam__0(
    mut v_inst_591_: *mut LeanObject,
    mut v_x_592_: *mut LeanObject,
    mut v_x_593_: *mut LeanObject,
    mut v_k_u2082_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = lean_apply_1(v_k_u2082_594_, v_inst_591_);
    return v___x_595_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg___lam__0___boxed(
    mut v_inst_596_: *mut LeanObject,
    mut v_x_597_: *mut LeanObject,
    mut v_x_598_: *mut LeanObject,
    mut v_k_u2082_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_600_: *mut LeanObject = core::ptr::null_mut();
    v_res_600_ = l_ExceptCpsT_instInhabited___redArg___lam__0(
        v_inst_596_,
        v_x_597_,
        v_x_598_,
        v_k_u2082_599_,
    );
    lean_dec(v_x_598_);
    return v_res_600_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg(
    mut v_inst_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_602_: *mut LeanObject = core::ptr::null_mut();
    v___f_602_ = lean_alloc_closure(
        l_ExceptCpsT_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_602_, 0, v_inst_601_);
    return v___f_602_;
}
pub unsafe fn l_ExceptCpsT_instInhabited(
    mut v_00_u03b5_603_: *mut LeanObject,
    mut v_m_604_: *mut LeanObject,
    mut v_00_u03b1_605_: *mut LeanObject,
    mut v_inst_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_607_: *mut LeanObject = core::ptr::null_mut();
    v___f_607_ = lean_alloc_closure(
        l_ExceptCpsT_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_607_, 0, v_inst_606_);
    return v___f_607_;
}
pub unsafe fn _init_l_ExceptCpsT_instMonadAttach___closed__0() -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = l_ExceptCpsT_instMonad___closed__9;
    v___x_609_ = l_MonadAttach_trivial___redArg(v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_ExceptCpsT_instMonadAttach(
    mut v_00_u03b5_610_: *mut LeanObject,
    mut v_m_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    v___x_612_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ExceptCpsT_instMonadAttach___closed__0),
        core::ptr::addr_of_mut!(l_ExceptCpsT_instMonadAttach___closed__0_once),
        _init_l_ExceptCpsT_instMonadAttach___closed__0,
    );
    return v___x_612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_ExceptCps(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_ExceptCps(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_ExceptCps(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_ExceptCps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_ExceptCps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_ExceptCps(builtin);
}
