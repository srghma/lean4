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
pub static l_ExceptCpsT_instMonad___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__1_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonad___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__2_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__3_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__3_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__7 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonad___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__5_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__10 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__5_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonad___lam__12 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonad___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__6_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__7_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__8_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonad___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonad___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonad___closed__9_value) as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonadExceptOf___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonadExceptOf___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ExceptCpsT_instMonadExceptOf___lam__2 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ExceptCpsT_instMonadExceptOf___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_ExceptCpsT_instMonadExceptOf___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ExceptCpsT_instMonadExceptOf___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ExceptCpsT_instMonadExceptOf___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_ExceptCpsT_instMonadAttach___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ExceptCpsT_instMonadAttach___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_ExceptCpsT_run___redArg___lam__0(
    mut v_toPure_307_: *mut leanh::LeanObject,
    mut v_a_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_309_, 0, v_a_308_);
    v___x_310_ = leanh::lean_apply_2(v_toPure_307_, leanh::lean_box(0), v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_ExceptCpsT_run___redArg___lam__1(
    mut v_toPure_311_: *mut leanh::LeanObject,
    mut v_e_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_313_, 0, v_e_312_);
    v___x_314_ = leanh::lean_apply_2(v_toPure_311_, leanh::lean_box(0), v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_ExceptCpsT_run___redArg(
    mut v_inst_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_317_ = leanh::lean_ctor_get(v_inst_315_, 0);
    leanh::lean_inc_ref(v_toApplicative_317_);
    leanh::lean_dec_ref(v_inst_315_);
    v_toPure_318_ = leanh::lean_ctor_get(v_toApplicative_317_, 1);
    leanh::lean_inc_n(v_toPure_318_, 2);
    leanh::lean_dec_ref(v_toApplicative_317_);
    v___f_319_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_319_, 0, v_toPure_318_);
    v___f_320_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_320_, 0, v_toPure_318_);
    v___x_321_ =
        leanh::lean_apply_3(v_x_316_, leanh::lean_box(0), v___f_319_, v___f_320_);
    return v___x_321_;
}
pub unsafe fn l_ExceptCpsT_run(
    mut v_m_322_: *mut leanh::LeanObject,
    mut v_00_u03b5_323_: *mut leanh::LeanObject,
    mut v_00_u03b1_324_: *mut leanh::LeanObject,
    mut v_inst_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_327_ = leanh::lean_ctor_get(v_inst_325_, 0);
    leanh::lean_inc_ref(v_toApplicative_327_);
    leanh::lean_dec_ref(v_inst_325_);
    v_toPure_328_ = leanh::lean_ctor_get(v_toApplicative_327_, 1);
    leanh::lean_inc_n(v_toPure_328_, 2);
    leanh::lean_dec_ref(v_toApplicative_327_);
    v___f_329_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_329_, 0, v_toPure_328_);
    v___f_330_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_run___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_330_, 0, v_toPure_328_);
    v___x_331_ =
        leanh::lean_apply_3(v_x_326_, leanh::lean_box(0), v___f_329_, v___f_330_);
    return v___x_331_;
}
pub unsafe fn l_ExceptCpsT_runK___redArg(
    mut v_x_332_: *mut leanh::LeanObject,
    mut v_ok_333_: *mut leanh::LeanObject,
    mut v_error_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ =
        leanh::lean_apply_3(v_x_332_, leanh::lean_box(0), v_ok_333_, v_error_334_);
    return v___x_335_;
}
pub unsafe fn l_ExceptCpsT_runK(
    mut v_m_336_: *mut leanh::LeanObject,
    mut v_00_u03b2_337_: *mut leanh::LeanObject,
    mut v_00_u03b5_338_: *mut leanh::LeanObject,
    mut v_00_u03b1_339_: *mut leanh::LeanObject,
    mut v_x_340_: *mut leanh::LeanObject,
    mut v_s_341_: *mut leanh::LeanObject,
    mut v_ok_342_: *mut leanh::LeanObject,
    mut v_error_343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ =
        leanh::lean_apply_3(v_x_340_, leanh::lean_box(0), v_ok_342_, v_error_343_);
    return v___x_344_;
}
pub unsafe fn l_ExceptCpsT_runK___boxed(
    mut v_m_345_: *mut leanh::LeanObject,
    mut v_00_u03b2_346_: *mut leanh::LeanObject,
    mut v_00_u03b5_347_: *mut leanh::LeanObject,
    mut v_00_u03b1_348_: *mut leanh::LeanObject,
    mut v_x_349_: *mut leanh::LeanObject,
    mut v_s_350_: *mut leanh::LeanObject,
    mut v_ok_351_: *mut leanh::LeanObject,
    mut v_error_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_s_350_);
    return v_res_353_;
}
pub unsafe fn l_ExceptCpsT_runCatch___redArg(
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_x_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_356_ = leanh::lean_ctor_get(v_inst_354_, 0);
    leanh::lean_inc_ref(v_toApplicative_356_);
    leanh::lean_dec_ref(v_inst_354_);
    v_toPure_357_ = leanh::lean_ctor_get(v_toApplicative_356_, 1);
    leanh::lean_inc(v_toPure_357_);
    leanh::lean_dec_ref(v_toApplicative_356_);
    v___x_358_ = leanh::lean_apply_1(v_toPure_357_, leanh::lean_box(0));
    leanh::lean_inc(v___x_358_);
    v___x_359_ =
        leanh::lean_apply_3(v_x_355_, leanh::lean_box(0), v___x_358_, v___x_358_);
    return v___x_359_;
}
pub unsafe fn l_ExceptCpsT_runCatch(
    mut v_m_360_: *mut leanh::LeanObject,
    mut v_00_u03b1_361_: *mut leanh::LeanObject,
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_x_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_364_ = leanh::lean_ctor_get(v_inst_362_, 0);
    leanh::lean_inc_ref(v_toApplicative_364_);
    leanh::lean_dec_ref(v_inst_362_);
    v_toPure_365_ = leanh::lean_ctor_get(v_toApplicative_364_, 1);
    leanh::lean_inc(v_toPure_365_);
    leanh::lean_dec_ref(v_toApplicative_364_);
    v___x_366_ = leanh::lean_apply_1(v_toPure_365_, leanh::lean_box(0));
    leanh::lean_inc(v___x_366_);
    v___x_367_ =
        leanh::lean_apply_3(v_x_363_, leanh::lean_box(0), v___x_366_, v___x_366_);
    return v___x_367_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__0(
    mut v_f_368_: *mut leanh::LeanObject,
    mut v_k_u2081_369_: *mut leanh::LeanObject,
    mut v_a_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = leanh::lean_apply_1(v_f_368_, v_a_370_);
    v___x_372_ = leanh::lean_apply_1(v_k_u2081_369_, v___x_371_);
    return v___x_372_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__1(
    mut v_00_u03b1_373_: *mut leanh::LeanObject,
    mut v_00_u03b2_374_: *mut leanh::LeanObject,
    mut v_f_375_: *mut leanh::LeanObject,
    mut v_x_376_: *mut leanh::LeanObject,
    mut v_x_377_: *mut leanh::LeanObject,
    mut v_k_u2081_378_: *mut leanh::LeanObject,
    mut v_k_u2082_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_380_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_380_, 0, v_f_375_);
    leanh::lean_closure_set(v___f_380_, 1, v_k_u2081_378_);
    v___x_381_ = leanh::lean_apply_3(
        v_x_376_,
        leanh::lean_box(0),
        v___f_380_,
        v_k_u2082_379_,
    );
    return v___x_381_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__2(
    mut v___f_382_: *mut leanh::LeanObject,
    mut v_00_u03b1_383_: *mut leanh::LeanObject,
    mut v_00_u03b2_384_: *mut leanh::LeanObject,
    mut v___y_385_: *mut leanh::LeanObject,
    mut v___y_386_: *mut leanh::LeanObject,
    mut v___y_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
    mut v___y_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_390_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_390_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_390_, 2, v___y_385_);
    v___x_391_ = leanh::lean_apply_7(
        v___f_382_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_390_,
        v___y_386_,
        leanh::lean_box(0),
        v___y_388_,
        v___y_389_,
    );
    return v___x_391_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__3(
    mut v_00_u03b1_392_: *mut leanh::LeanObject,
    mut v_a_393_: *mut leanh::LeanObject,
    mut v_x_394_: *mut leanh::LeanObject,
    mut v_k_395_: *mut leanh::LeanObject,
    mut v_x_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = leanh::lean_apply_1(v_k_395_, v_a_393_);
    return v___x_397_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__3___boxed(
    mut v_00_u03b1_398_: *mut leanh::LeanObject,
    mut v_a_399_: *mut leanh::LeanObject,
    mut v_x_400_: *mut leanh::LeanObject,
    mut v_k_401_: *mut leanh::LeanObject,
    mut v_x_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_403_ =
        l_ExceptCpsT_instMonad___lam__3(v_00_u03b1_398_, v_a_399_, v_x_400_, v_k_401_, v_x_402_);
    leanh::lean_dec(v_x_402_);
    return v_res_403_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__4(
    mut v_x_404_: *mut leanh::LeanObject,
    mut v___f_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
    mut v___y_407_: *mut leanh::LeanObject,
    mut v_a_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = leanh::lean_box(0);
    v___x_410_ = leanh::lean_apply_1(v_x_404_, v___x_409_);
    v___x_411_ = leanh::lean_apply_7(
        v___f_405_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_408_,
        v___x_410_,
        leanh::lean_box(0),
        v___y_406_,
        v___y_407_,
    );
    return v___x_411_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__5(
    mut v___f_412_: *mut leanh::LeanObject,
    mut v_00_u03b1_413_: *mut leanh::LeanObject,
    mut v_00_u03b2_414_: *mut leanh::LeanObject,
    mut v_f_415_: *mut leanh::LeanObject,
    mut v_x_416_: *mut leanh::LeanObject,
    mut v___y_417_: *mut leanh::LeanObject,
    mut v___y_418_: *mut leanh::LeanObject,
    mut v___y_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_419_);
    v___f_420_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_420_, 0, v_x_416_);
    leanh::lean_closure_set(v___f_420_, 1, v___f_412_);
    leanh::lean_closure_set(v___f_420_, 2, v___y_418_);
    leanh::lean_closure_set(v___f_420_, 3, v___y_419_);
    v___x_421_ =
        leanh::lean_apply_3(v_f_415_, leanh::lean_box(0), v___f_420_, v___y_419_);
    return v___x_421_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__6(
    mut v_f_422_: *mut leanh::LeanObject,
    mut v_k_u2081_423_: *mut leanh::LeanObject,
    mut v_k_u2082_424_: *mut leanh::LeanObject,
    mut v_a_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_426_ = leanh::lean_apply_4(
        v_f_422_,
        v_a_425_,
        leanh::lean_box(0),
        v_k_u2081_423_,
        v_k_u2082_424_,
    );
    return v___x_426_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__7(
    mut v_00_u03b1_427_: *mut leanh::LeanObject,
    mut v_00_u03b2_428_: *mut leanh::LeanObject,
    mut v_x_429_: *mut leanh::LeanObject,
    mut v_f_430_: *mut leanh::LeanObject,
    mut v_x_431_: *mut leanh::LeanObject,
    mut v_k_u2081_432_: *mut leanh::LeanObject,
    mut v_k_u2082_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_k_u2082_433_);
    v___f_434_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_434_, 0, v_f_430_);
    leanh::lean_closure_set(v___f_434_, 1, v_k_u2081_432_);
    leanh::lean_closure_set(v___f_434_, 2, v_k_u2082_433_);
    v___x_435_ = leanh::lean_apply_3(
        v_x_429_,
        leanh::lean_box(0),
        v___f_434_,
        v_k_u2082_433_,
    );
    return v___x_435_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__8(
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_x_437_: *mut leanh::LeanObject,
    mut v___y_438_: *mut leanh::LeanObject,
    mut v___y_439_: *mut leanh::LeanObject,
    mut v___y_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = leanh::lean_apply_1(v___y_439_, v_a_436_);
    return v___x_441_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__8___boxed(
    mut v_a_442_: *mut leanh::LeanObject,
    mut v_x_443_: *mut leanh::LeanObject,
    mut v___y_444_: *mut leanh::LeanObject,
    mut v___y_445_: *mut leanh::LeanObject,
    mut v___y_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_447_ =
        l_ExceptCpsT_instMonad___lam__8(v_a_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_);
    leanh::lean_dec(v___y_446_);
    leanh::lean_dec(v_x_443_);
    return v_res_447_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__9(
    mut v_y_448_: *mut leanh::LeanObject,
    mut v___f_449_: *mut leanh::LeanObject,
    mut v_a_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_454_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__8___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_454_, 0, v_a_450_);
    v___x_455_ = leanh::lean_box(0);
    v___x_456_ = leanh::lean_apply_1(v_y_448_, v___x_455_);
    v___x_457_ = leanh::lean_apply_7(
        v___f_449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_456_,
        v___f_454_,
        leanh::lean_box(0),
        v___y_452_,
        v___y_453_,
    );
    return v___x_457_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__10(
    mut v___f_458_: *mut leanh::LeanObject,
    mut v_00_u03b1_459_: *mut leanh::LeanObject,
    mut v_00_u03b2_460_: *mut leanh::LeanObject,
    mut v_x_461_: *mut leanh::LeanObject,
    mut v_y_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___f_458_);
    v___f_466_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__9 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_466_, 0, v_y_462_);
    leanh::lean_closure_set(v___f_466_, 1, v___f_458_);
    v___x_467_ = leanh::lean_apply_7(
        v___f_458_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_461_,
        v___f_466_,
        leanh::lean_box(0),
        v___y_464_,
        v___y_465_,
    );
    return v___x_467_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__11(
    mut v_y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
    mut v_a_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = leanh::lean_box(0);
    v___x_473_ = leanh::lean_apply_4(
        v_y_468_,
        v___x_472_,
        leanh::lean_box(0),
        v___y_469_,
        v___y_470_,
    );
    return v___x_473_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__11___boxed(
    mut v_y_474_: *mut leanh::LeanObject,
    mut v___y_475_: *mut leanh::LeanObject,
    mut v___y_476_: *mut leanh::LeanObject,
    mut v_a_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_ExceptCpsT_instMonad___lam__11(v_y_474_, v___y_475_, v___y_476_, v_a_477_);
    leanh::lean_dec(v_a_477_);
    return v_res_478_;
}
pub unsafe fn l_ExceptCpsT_instMonad___lam__12(
    mut v_00_u03b1_479_: *mut leanh::LeanObject,
    mut v_00_u03b2_480_: *mut leanh::LeanObject,
    mut v_x_481_: *mut leanh::LeanObject,
    mut v_y_482_: *mut leanh::LeanObject,
    mut v___y_483_: *mut leanh::LeanObject,
    mut v___y_484_: *mut leanh::LeanObject,
    mut v___y_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_485_);
    v___f_486_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonad___lam__11___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_486_, 0, v_y_482_);
    leanh::lean_closure_set(v___f_486_, 1, v___y_484_);
    leanh::lean_closure_set(v___f_486_, 2, v___y_485_);
    v___x_487_ =
        leanh::lean_apply_3(v_x_481_, leanh::lean_box(0), v___f_486_, v___y_485_);
    return v___x_487_;
}
pub unsafe fn l_ExceptCpsT_instMonad(
    mut v_00_u03b5_510_: *mut leanh::LeanObject,
    mut v_m_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = l_ExceptCpsT_instMonad___closed__9;
    return v___x_512_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__0(
    mut v_00_u03b1_513_: *mut leanh::LeanObject,
    mut v_e_514_: *mut leanh::LeanObject,
    mut v_x_515_: *mut leanh::LeanObject,
    mut v_x_516_: *mut leanh::LeanObject,
    mut v_k_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = leanh::lean_apply_1(v_k_517_, v_e_514_);
    return v___x_518_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__0___boxed(
    mut v_00_u03b1_519_: *mut leanh::LeanObject,
    mut v_e_520_: *mut leanh::LeanObject,
    mut v_x_521_: *mut leanh::LeanObject,
    mut v_x_522_: *mut leanh::LeanObject,
    mut v_k_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_ExceptCpsT_instMonadExceptOf___lam__0(
        v_00_u03b1_519_,
        v_e_520_,
        v_x_521_,
        v_x_522_,
        v_k_523_,
    );
    leanh::lean_dec(v_x_522_);
    return v_res_524_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__1(
    mut v_handle_525_: *mut leanh::LeanObject,
    mut v_k_u2081_526_: *mut leanh::LeanObject,
    mut v_k_u2082_527_: *mut leanh::LeanObject,
    mut v_e_528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = leanh::lean_apply_4(
        v_handle_525_,
        v_e_528_,
        leanh::lean_box(0),
        v_k_u2081_526_,
        v_k_u2082_527_,
    );
    return v___x_529_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf___lam__2(
    mut v_00_u03b1_530_: *mut leanh::LeanObject,
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_handle_532_: *mut leanh::LeanObject,
    mut v_x_533_: *mut leanh::LeanObject,
    mut v_k_u2081_534_: *mut leanh::LeanObject,
    mut v_k_u2082_535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_k_u2081_534_);
    v___f_536_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonadExceptOf___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_536_, 0, v_handle_532_);
    leanh::lean_closure_set(v___f_536_, 1, v_k_u2081_534_);
    leanh::lean_closure_set(v___f_536_, 2, v_k_u2082_535_);
    v___x_537_ = leanh::lean_apply_3(
        v_x_531_,
        leanh::lean_box(0),
        v_k_u2081_534_,
        v___f_536_,
    );
    return v___x_537_;
}
pub unsafe fn l_ExceptCpsT_instMonadExceptOf(
    mut v_00_u03b5_543_: *mut leanh::LeanObject,
    mut v_m_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_545_ = l_ExceptCpsT_instMonadExceptOf___closed__2;
    return v___x_545_;
}
pub unsafe fn l_ExceptCpsT_lift___redArg(
    mut v_inst_546_: *mut leanh::LeanObject,
    mut v_x_547_: *mut leanh::LeanObject,
    mut v_k_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_549_ = leanh::lean_ctor_get(v_inst_546_, 1);
    leanh::lean_inc(v_toBind_549_);
    leanh::lean_dec_ref(v_inst_546_);
    v___x_550_ = leanh::lean_apply_4(
        v_toBind_549_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_547_,
        v_k_548_,
    );
    return v___x_550_;
}
pub unsafe fn l_ExceptCpsT_lift(
    mut v_m_551_: *mut leanh::LeanObject,
    mut v_00_u03b1_552_: *mut leanh::LeanObject,
    mut v_00_u03b5_553_: *mut leanh::LeanObject,
    mut v_inst_554_: *mut leanh::LeanObject,
    mut v_x_555_: *mut leanh::LeanObject,
    mut v_x_556_: *mut leanh::LeanObject,
    mut v_k_557_: *mut leanh::LeanObject,
    mut v_x_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_559_ = leanh::lean_ctor_get(v_inst_554_, 1);
    leanh::lean_inc(v_toBind_559_);
    leanh::lean_dec_ref(v_inst_554_);
    v___x_560_ = leanh::lean_apply_4(
        v_toBind_559_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_555_,
        v_k_557_,
    );
    return v___x_560_;
}
pub unsafe fn l_ExceptCpsT_lift___boxed(
    mut v_m_561_: *mut leanh::LeanObject,
    mut v_00_u03b1_562_: *mut leanh::LeanObject,
    mut v_00_u03b5_563_: *mut leanh::LeanObject,
    mut v_inst_564_: *mut leanh::LeanObject,
    mut v_x_565_: *mut leanh::LeanObject,
    mut v_x_566_: *mut leanh::LeanObject,
    mut v_k_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_569_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_x_568_);
    return v_res_569_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(
    mut v_inst_570_: *mut leanh::LeanObject,
    mut v_00_u03b1_571_: *mut leanh::LeanObject,
    mut v___y_572_: *mut leanh::LeanObject,
    mut v___y_573_: *mut leanh::LeanObject,
    mut v___y_574_: *mut leanh::LeanObject,
    mut v___y_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_576_ = leanh::lean_ctor_get(v_inst_570_, 1);
    leanh::lean_inc(v_toBind_576_);
    leanh::lean_dec_ref(v_inst_570_);
    v___x_577_ = leanh::lean_apply_4(
        v_toBind_576_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___y_572_,
        v___y_574_,
    );
    return v___x_577_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed(
    mut v_inst_578_: *mut leanh::LeanObject,
    mut v_00_u03b1_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0(
        v_inst_578_,
        v_00_u03b1_579_,
        v___y_580_,
        v___y_581_,
        v___y_582_,
        v___y_583_,
    );
    leanh::lean_dec(v___y_583_);
    return v_res_584_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad___redArg(
    mut v_inst_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_586_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_586_, 0, v_inst_585_);
    return v___f_586_;
}
pub unsafe fn l_ExceptCpsT_instMonadLiftOfMonad(
    mut v_m_587_: *mut leanh::LeanObject,
    mut v_00_u03c3_588_: *mut leanh::LeanObject,
    mut v_inst_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_590_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instMonadLiftOfMonad___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_590_, 0, v_inst_589_);
    return v___f_590_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg___lam__0(
    mut v_inst_591_: *mut leanh::LeanObject,
    mut v_x_592_: *mut leanh::LeanObject,
    mut v_x_593_: *mut leanh::LeanObject,
    mut v_k_u2082_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = leanh::lean_apply_1(v_k_u2082_594_, v_inst_591_);
    return v___x_595_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg___lam__0___boxed(
    mut v_inst_596_: *mut leanh::LeanObject,
    mut v_x_597_: *mut leanh::LeanObject,
    mut v_x_598_: *mut leanh::LeanObject,
    mut v_k_u2082_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_ExceptCpsT_instInhabited___redArg___lam__0(
        v_inst_596_,
        v_x_597_,
        v_x_598_,
        v_k_u2082_599_,
    );
    leanh::lean_dec(v_x_598_);
    return v_res_600_;
}
pub unsafe fn l_ExceptCpsT_instInhabited___redArg(
    mut v_inst_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_602_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_602_, 0, v_inst_601_);
    return v___f_602_;
}
pub unsafe fn l_ExceptCpsT_instInhabited(
    mut v_00_u03b5_603_: *mut leanh::LeanObject,
    mut v_m_604_: *mut leanh::LeanObject,
    mut v_00_u03b1_605_: *mut leanh::LeanObject,
    mut v_inst_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_607_ = leanh::lean_alloc_closure(
        l_ExceptCpsT_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_607_, 0, v_inst_606_);
    return v___f_607_;
}
pub unsafe fn _init_l_ExceptCpsT_instMonadAttach___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = l_ExceptCpsT_instMonad___closed__9;
    v___x_609_ = l_MonadAttach_trivial___redArg(v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_ExceptCpsT_instMonadAttach(
    mut v_00_u03b5_610_: *mut leanh::LeanObject,
    mut v_m_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ExceptCpsT_instMonadAttach___closed__0),
        core::ptr::addr_of_mut!(l_ExceptCpsT_instMonadAttach___closed__0_once),
        _init_l_ExceptCpsT_instMonadAttach___closed__0,
    );
    return v___x_612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_ExceptCps(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_ExceptCps(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_ExceptCps(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_ExceptCps(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_ExceptCps(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_ExceptCps(builtin);
}