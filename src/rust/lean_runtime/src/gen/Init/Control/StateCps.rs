// Lean compiler output
// Module: Init.Control.StateCps
// Imports: Init.Control.Lawful.Basic Init.Ext
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::MonadAttach::l_MonadAttach_trivial___redArg;
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_7, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
};
pub static l_StateCpsT_instMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateCpsT_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__2 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value) as *mut LeanObject],
};
static mut l_StateCpsT_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__1_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateCpsT_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__2_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__3_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__5 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value) as *mut LeanObject],
};
static mut l_StateCpsT_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__3_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__7 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateCpsT_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__5_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__10 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value) as *mut LeanObject],
};
static mut l_StateCpsT_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__5_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateCpsT_instMonad___lam__12 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_StateCpsT_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__6_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_StateCpsT_instMonad___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__7_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_StateCpsT_instMonad___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__8_value) as *mut LeanObject;
pub static l_StateCpsT_instMonad___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_StateCpsT_instMonad___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__9_value) as *mut LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__0_value) as *mut LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__1_value) as *mut LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__2 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__2_value) as *mut LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_StateCpsT_instMonadStateOf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__3_value) as *mut LeanObject;
static mut l_StateCpsT_instMonadAttach___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_StateCpsT_instMonadAttach___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_StateCpsT_runK___redArg(
    mut v_x_280_: *mut LeanObject,
    mut v_s_281_: *mut LeanObject,
    mut v_k_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_283_ = lean_apply_3(v_x_280_, lean_box(0), v_s_281_, v_k_282_);
    return v___x_283_;
}
pub unsafe fn l_StateCpsT_runK(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_00_u03c3_285_: *mut LeanObject,
    mut v_m_286_: *mut LeanObject,
    mut v_00_u03b2_287_: *mut LeanObject,
    mut v_x_288_: *mut LeanObject,
    mut v_s_289_: *mut LeanObject,
    mut v_k_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_apply_3(v_x_288_, lean_box(0), v_s_289_, v_k_290_);
    return v___x_291_;
}
pub unsafe fn l_StateCpsT_run___redArg___lam__0(
    mut v_toPure_292_: *mut LeanObject,
    mut v_a_293_: *mut LeanObject,
    mut v_s_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    v___x_295_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_295_, 0, v_a_293_);
    lean_ctor_set(v___x_295_, 1, v_s_294_);
    v___x_296_ = lean_apply_2(v_toPure_292_, lean_box(0), v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_StateCpsT_run___redArg(
    mut v_inst_297_: *mut LeanObject,
    mut v_x_298_: *mut LeanObject,
    mut v_s_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_300_ = lean_ctor_get(v_inst_297_, 0);
    lean_inc_ref(v_toApplicative_300_);
    lean_dec_ref(v_inst_297_);
    v_toPure_301_ = lean_ctor_get(v_toApplicative_300_, 1);
    lean_inc(v_toPure_301_);
    lean_dec_ref(v_toApplicative_300_);
    v___f_302_ = lean_alloc_closure(
        l_StateCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_302_, 0, v_toPure_301_);
    v___x_303_ = lean_apply_3(v_x_298_, lean_box(0), v_s_299_, v___f_302_);
    return v___x_303_;
}
pub unsafe fn l_StateCpsT_run(
    mut v_00_u03b1_304_: *mut LeanObject,
    mut v_00_u03c3_305_: *mut LeanObject,
    mut v_m_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
    mut v_x_308_: *mut LeanObject,
    mut v_s_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_310_ = lean_ctor_get(v_inst_307_, 0);
    lean_inc_ref(v_toApplicative_310_);
    lean_dec_ref(v_inst_307_);
    v_toPure_311_ = lean_ctor_get(v_toApplicative_310_, 1);
    lean_inc(v_toPure_311_);
    lean_dec_ref(v_toApplicative_310_);
    v___f_312_ = lean_alloc_closure(
        l_StateCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_312_, 0, v_toPure_311_);
    v___x_313_ = lean_apply_3(v_x_308_, lean_box(0), v_s_309_, v___f_312_);
    return v___x_313_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg___lam__0(
    mut v_toPure_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_x_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = lean_apply_2(v_toPure_314_, lean_box(0), v_a_315_);
    return v___x_317_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg___lam__0___boxed(
    mut v_toPure_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_x_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_321_: *mut LeanObject = core::ptr::null_mut();
    v_res_321_ = l_StateCpsT_run_x27___redArg___lam__0(v_toPure_318_, v_a_319_, v_x_320_);
    lean_dec(v_x_320_);
    return v_res_321_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg(
    mut v_inst_322_: *mut LeanObject,
    mut v_x_323_: *mut LeanObject,
    mut v_s_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_325_ = lean_ctor_get(v_inst_322_, 0);
    lean_inc_ref(v_toApplicative_325_);
    lean_dec_ref(v_inst_322_);
    v_toPure_326_ = lean_ctor_get(v_toApplicative_325_, 1);
    lean_inc(v_toPure_326_);
    lean_dec_ref(v_toApplicative_325_);
    v___f_327_ = lean_alloc_closure(
        l_StateCpsT_run_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_327_, 0, v_toPure_326_);
    v___x_328_ = lean_apply_3(v_x_323_, lean_box(0), v_s_324_, v___f_327_);
    return v___x_328_;
}
pub unsafe fn l_StateCpsT_run_x27(
    mut v_00_u03b1_329_: *mut LeanObject,
    mut v_00_u03c3_330_: *mut LeanObject,
    mut v_m_331_: *mut LeanObject,
    mut v_inst_332_: *mut LeanObject,
    mut v_x_333_: *mut LeanObject,
    mut v_s_334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_335_ = lean_ctor_get(v_inst_332_, 0);
    lean_inc_ref(v_toApplicative_335_);
    lean_dec_ref(v_inst_332_);
    v_toPure_336_ = lean_ctor_get(v_toApplicative_335_, 1);
    lean_inc(v_toPure_336_);
    lean_dec_ref(v_toApplicative_335_);
    v___f_337_ = lean_alloc_closure(
        l_StateCpsT_run_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_337_, 0, v_toPure_336_);
    v___x_338_ = lean_apply_3(v_x_333_, lean_box(0), v_s_334_, v___f_337_);
    return v___x_338_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__0(
    mut v_f_339_: *mut LeanObject,
    mut v_k_340_: *mut LeanObject,
    mut v_a_341_: *mut LeanObject,
    mut v_s_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v___x_343_ = lean_apply_1(v_f_339_, v_a_341_);
    v___x_344_ = lean_apply_2(v_k_340_, v___x_343_, v_s_342_);
    return v___x_344_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__1(
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_00_u03b2_346_: *mut LeanObject,
    mut v_f_347_: *mut LeanObject,
    mut v_x_348_: *mut LeanObject,
    mut v_00_u03b4_349_: *mut LeanObject,
    mut v_s_350_: *mut LeanObject,
    mut v_k_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    v___f_352_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_352_, 0, v_f_347_);
    lean_closure_set(v___f_352_, 1, v_k_351_);
    v___x_353_ = lean_apply_3(v_x_348_, lean_box(0), v_s_350_, v___f_352_);
    return v___x_353_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__2(
    mut v___f_354_: *mut LeanObject,
    mut v_00_u03b1_355_: *mut LeanObject,
    mut v_00_u03b2_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
    mut v___y_359_: *mut LeanObject,
    mut v___y_360_: *mut LeanObject,
    mut v___y_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_362_, 0, lean_box(0));
    lean_closure_set(v___x_362_, 1, lean_box(0));
    lean_closure_set(v___x_362_, 2, v___y_357_);
    v___x_363_ = lean_apply_7(
        v___f_354_,
        lean_box(0),
        lean_box(0),
        v___x_362_,
        v___y_358_,
        lean_box(0),
        v___y_360_,
        v___y_361_,
    );
    return v___x_363_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__3(
    mut v_00_u03b1_364_: *mut LeanObject,
    mut v_a_365_: *mut LeanObject,
    mut v_x_366_: *mut LeanObject,
    mut v_s_367_: *mut LeanObject,
    mut v_k_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    v___x_369_ = lean_apply_2(v_k_368_, v_a_365_, v_s_367_);
    return v___x_369_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__4(
    mut v_x_370_: *mut LeanObject,
    mut v___f_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
    mut v_a_373_: *mut LeanObject,
    mut v_s_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    v___x_375_ = lean_box(0);
    v___x_376_ = lean_apply_1(v_x_370_, v___x_375_);
    v___x_377_ = lean_apply_7(
        v___f_371_,
        lean_box(0),
        lean_box(0),
        v_a_373_,
        v___x_376_,
        lean_box(0),
        v_s_374_,
        v___y_372_,
    );
    return v___x_377_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__5(
    mut v___f_378_: *mut LeanObject,
    mut v_00_u03b1_379_: *mut LeanObject,
    mut v_00_u03b2_380_: *mut LeanObject,
    mut v_f_381_: *mut LeanObject,
    mut v_x_382_: *mut LeanObject,
    mut v___y_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___f_386_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__4 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_386_, 0, v_x_382_);
    lean_closure_set(v___f_386_, 1, v___f_378_);
    lean_closure_set(v___f_386_, 2, v___y_385_);
    v___x_387_ = lean_apply_3(v_f_381_, lean_box(0), v___y_384_, v___f_386_);
    return v___x_387_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__6(
    mut v_f_388_: *mut LeanObject,
    mut v_k_389_: *mut LeanObject,
    mut v_a_390_: *mut LeanObject,
    mut v_s_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = lean_apply_4(v_f_388_, v_a_390_, lean_box(0), v_s_391_, v_k_389_);
    return v___x_392_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__7(
    mut v_00_u03b1_393_: *mut LeanObject,
    mut v_00_u03b2_394_: *mut LeanObject,
    mut v_x_395_: *mut LeanObject,
    mut v_f_396_: *mut LeanObject,
    mut v_00_u03b4_397_: *mut LeanObject,
    mut v_s_398_: *mut LeanObject,
    mut v_k_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___f_400_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__6 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_400_, 0, v_f_396_);
    lean_closure_set(v___f_400_, 1, v_k_399_);
    v___x_401_ = lean_apply_3(v_x_395_, lean_box(0), v_s_398_, v___f_400_);
    return v___x_401_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__8(
    mut v_a_402_: *mut LeanObject,
    mut v_x_403_: *mut LeanObject,
    mut v___y_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_apply_2(v___y_406_, v_a_402_, v___y_405_);
    return v___x_407_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__8___boxed(
    mut v_a_408_: *mut LeanObject,
    mut v_x_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_413_: *mut LeanObject = core::ptr::null_mut();
    v_res_413_ =
        l_StateCpsT_instMonad___lam__8(v_a_408_, v_x_409_, v___y_410_, v___y_411_, v___y_412_);
    lean_dec(v_x_409_);
    return v_res_413_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__9(
    mut v_y_414_: *mut LeanObject,
    mut v___f_415_: *mut LeanObject,
    mut v_a_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___f_420_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__8___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_420_, 0, v_a_416_);
    v___x_421_ = lean_box(0);
    v___x_422_ = lean_apply_1(v_y_414_, v___x_421_);
    v___x_423_ = lean_apply_7(
        v___f_415_,
        lean_box(0),
        lean_box(0),
        v___x_422_,
        v___f_420_,
        lean_box(0),
        v___y_418_,
        v___y_419_,
    );
    return v___x_423_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__10(
    mut v___f_424_: *mut LeanObject,
    mut v_00_u03b1_425_: *mut LeanObject,
    mut v_00_u03b2_426_: *mut LeanObject,
    mut v_x_427_: *mut LeanObject,
    mut v_y_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___f_424_);
    v___f_432_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__9 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_432_, 0, v_y_428_);
    lean_closure_set(v___f_432_, 1, v___f_424_);
    v___x_433_ = lean_apply_7(
        v___f_424_,
        lean_box(0),
        lean_box(0),
        v_x_427_,
        v___f_432_,
        lean_box(0),
        v___y_430_,
        v___y_431_,
    );
    return v___x_433_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__11(
    mut v_y_434_: *mut LeanObject,
    mut v___y_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_s_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_box(0);
    v___x_439_ = lean_apply_4(v_y_434_, v___x_438_, lean_box(0), v_s_437_, v___y_435_);
    return v___x_439_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__11___boxed(
    mut v_y_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v_a_442_: *mut LeanObject,
    mut v_s_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_444_: *mut LeanObject = core::ptr::null_mut();
    v_res_444_ = l_StateCpsT_instMonad___lam__11(v_y_440_, v___y_441_, v_a_442_, v_s_443_);
    lean_dec(v_a_442_);
    return v_res_444_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__12(
    mut v_00_u03b1_445_: *mut LeanObject,
    mut v_00_u03b2_446_: *mut LeanObject,
    mut v_x_447_: *mut LeanObject,
    mut v_y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
    mut v___y_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___f_452_ = lean_alloc_closure(
        l_StateCpsT_instMonad___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_452_, 0, v_y_448_);
    lean_closure_set(v___f_452_, 1, v___y_451_);
    v___x_453_ = lean_apply_3(v_x_447_, lean_box(0), v___y_450_, v___f_452_);
    return v___x_453_;
}
pub unsafe fn l_StateCpsT_instMonad(
    mut v_00_u03c3_476_: *mut LeanObject,
    mut v_m_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = l_StateCpsT_instMonad___closed__9;
    return v___x_478_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__0(
    mut v_x_479_: *mut LeanObject,
    mut v_s_480_: *mut LeanObject,
    mut v_k_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_480_);
    v___x_482_ = lean_apply_2(v_k_481_, v_s_480_, v_s_480_);
    return v___x_482_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__1(
    mut v_s_483_: *mut LeanObject,
    mut v_x_484_: *mut LeanObject,
    mut v_x_485_: *mut LeanObject,
    mut v_k_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = lean_box(0);
    v___x_488_ = lean_apply_2(v_k_486_, v___x_487_, v_s_483_);
    return v___x_488_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__1___boxed(
    mut v_s_489_: *mut LeanObject,
    mut v_x_490_: *mut LeanObject,
    mut v_x_491_: *mut LeanObject,
    mut v_k_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_493_: *mut LeanObject = core::ptr::null_mut();
    v_res_493_ = l_StateCpsT_instMonadStateOf___lam__1(v_s_489_, v_x_490_, v_x_491_, v_k_492_);
    lean_dec(v_x_491_);
    return v_res_493_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__2(
    mut v_00_u03b1_494_: *mut LeanObject,
    mut v_f_495_: *mut LeanObject,
    mut v_x_496_: *mut LeanObject,
    mut v_s_497_: *mut LeanObject,
    mut v_k_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_apply_1(v_f_495_, v_s_497_);
    v_fst_500_ = lean_ctor_get(v___x_499_, 0);
    lean_inc(v_fst_500_);
    v_snd_501_ = lean_ctor_get(v___x_499_, 1);
    lean_inc(v_snd_501_);
    lean_dec_ref(v___x_499_);
    v___x_502_ = lean_apply_2(v_k_498_, v_fst_500_, v_snd_501_);
    return v___x_502_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf(
    mut v_00_u03c3_510_: *mut LeanObject,
    mut v_m_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_512_ = l_StateCpsT_instMonadStateOf___closed__3;
    return v___x_512_;
}
pub unsafe fn _init_l_StateCpsT_instMonadAttach___closed__0() -> *mut LeanObject {
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    v___x_513_ = l_StateCpsT_instMonad___closed__9;
    v___x_514_ = l_MonadAttach_trivial___redArg(v___x_513_);
    return v___x_514_;
}
pub unsafe fn l_StateCpsT_instMonadAttach(
    mut v_m_515_: *mut LeanObject,
    mut v_00_u03b5_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___x_517_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_StateCpsT_instMonadAttach___closed__0),
        core::ptr::addr_of_mut!(l_StateCpsT_instMonadAttach___closed__0_once),
        _init_l_StateCpsT_instMonadAttach___closed__0,
    );
    return v___x_517_;
}
pub unsafe fn l_StateCpsT_lift___redArg___lam__0(
    mut v_k_518_: *mut LeanObject,
    mut v_s_519_: *mut LeanObject,
    mut v_x_520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    v___x_521_ = lean_apply_2(v_k_518_, v_x_520_, v_s_519_);
    return v___x_521_;
}
pub unsafe fn l_StateCpsT_lift___redArg(
    mut v_inst_522_: *mut LeanObject,
    mut v_x_523_: *mut LeanObject,
    mut v_s_524_: *mut LeanObject,
    mut v_k_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_526_ = lean_ctor_get(v_inst_522_, 1);
    lean_inc(v_toBind_526_);
    lean_dec_ref(v_inst_522_);
    v___f_527_ = lean_alloc_closure(
        l_StateCpsT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_527_, 0, v_k_525_);
    lean_closure_set(v___f_527_, 1, v_s_524_);
    v___x_528_ = lean_apply_4(
        v_toBind_526_,
        lean_box(0),
        lean_box(0),
        v_x_523_,
        v___f_527_,
    );
    return v___x_528_;
}
pub unsafe fn l_StateCpsT_lift(
    mut v_00_u03b1_529_: *mut LeanObject,
    mut v_00_u03c3_530_: *mut LeanObject,
    mut v_m_531_: *mut LeanObject,
    mut v_inst_532_: *mut LeanObject,
    mut v_x_533_: *mut LeanObject,
    mut v_x_534_: *mut LeanObject,
    mut v_s_535_: *mut LeanObject,
    mut v_k_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_537_ = lean_ctor_get(v_inst_532_, 1);
    lean_inc(v_toBind_537_);
    lean_dec_ref(v_inst_532_);
    v___f_538_ = lean_alloc_closure(
        l_StateCpsT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_538_, 0, v_k_536_);
    lean_closure_set(v___f_538_, 1, v_s_535_);
    v___x_539_ = lean_apply_4(
        v_toBind_537_,
        lean_box(0),
        lean_box(0),
        v_x_533_,
        v___f_538_,
    );
    return v___x_539_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0(
    mut v___y_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
    mut v_x_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = lean_apply_2(v___y_540_, v_x_542_, v___y_541_);
    return v___x_543_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1(
    mut v_inst_544_: *mut LeanObject,
    mut v_00_u03b1_545_: *mut LeanObject,
    mut v___y_546_: *mut LeanObject,
    mut v___y_547_: *mut LeanObject,
    mut v___y_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_550_ = lean_ctor_get(v_inst_544_, 1);
    lean_inc(v_toBind_550_);
    lean_dec_ref(v_inst_544_);
    v___f_551_ = lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_551_, 0, v___y_549_);
    lean_closure_set(v___f_551_, 1, v___y_548_);
    v___x_552_ = lean_apply_4(
        v_toBind_550_,
        lean_box(0),
        lean_box(0),
        v___y_546_,
        v___f_551_,
    );
    return v___x_552_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg(
    mut v_inst_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_554_: *mut LeanObject = core::ptr::null_mut();
    v___f_554_ = lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_554_, 0, v_inst_553_);
    return v___f_554_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad(
    mut v_00_u03c3_555_: *mut LeanObject,
    mut v_m_556_: *mut LeanObject,
    mut v_inst_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_558_: *mut LeanObject = core::ptr::null_mut();
    v___f_558_ = lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_558_, 0, v_inst_557_);
    return v___f_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_StateCps(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_StateCps(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_StateCps(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateCps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_StateCps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_StateCps(builtin);
}
