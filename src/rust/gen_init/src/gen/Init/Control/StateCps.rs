// Lean compiler output
// Module: Init.Control.StateCps
// Imports: Init.Control.Lawful.Basic Init.Ext
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::MonadAttach::l_MonadAttach_trivial___redArg;
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
pub static l_StateCpsT_instMonad___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_StateCpsT_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_StateCpsT_instMonad___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__1_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonad___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__2_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__3_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_StateCpsT_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_StateCpsT_instMonad___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__3_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonad___lam__7 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonad___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__5_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_StateCpsT_instMonad___lam__10 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_StateCpsT_instMonad___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__5_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonad___lam__12 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonad___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__6_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_StateCpsT_instMonad___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__7_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_StateCpsT_instMonad___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__8_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonad___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonad___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_StateCpsT_instMonad___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonad___closed__9_value) as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_StateCpsT_instMonadStateOf___lam__2 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_StateCpsT_instMonadStateOf___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_StateCpsT_instMonadStateOf___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_StateCpsT_instMonadStateOf___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_StateCpsT_instMonadStateOf___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_StateCpsT_instMonadAttach___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_StateCpsT_instMonadAttach___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_StateCpsT_runK___redArg(
    mut v_x_280_: *mut leanh::LeanObject,
    mut v_s_281_: *mut leanh::LeanObject,
    mut v_k_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ =
        leanh::lean_apply_3(v_x_280_, leanh::lean_box(0), v_s_281_, v_k_282_);
    return v___x_283_;
}
pub unsafe fn l_StateCpsT_runK(
    mut v_00_u03b1_284_: *mut leanh::LeanObject,
    mut v_00_u03c3_285_: *mut leanh::LeanObject,
    mut v_m_286_: *mut leanh::LeanObject,
    mut v_00_u03b2_287_: *mut leanh::LeanObject,
    mut v_x_288_: *mut leanh::LeanObject,
    mut v_s_289_: *mut leanh::LeanObject,
    mut v_k_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ =
        leanh::lean_apply_3(v_x_288_, leanh::lean_box(0), v_s_289_, v_k_290_);
    return v___x_291_;
}
pub unsafe fn l_StateCpsT_run___redArg___lam__0(
    mut v_toPure_292_: *mut leanh::LeanObject,
    mut v_a_293_: *mut leanh::LeanObject,
    mut v_s_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_295_, 0, v_a_293_);
    leanh::lean_ctor_set(v___x_295_, 1, v_s_294_);
    v___x_296_ = leanh::lean_apply_2(v_toPure_292_, leanh::lean_box(0), v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_StateCpsT_run___redArg(
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_x_298_: *mut leanh::LeanObject,
    mut v_s_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_300_ = leanh::lean_ctor_get(v_inst_297_, 0);
    leanh::lean_inc_ref(v_toApplicative_300_);
    leanh::lean_dec_ref(v_inst_297_);
    v_toPure_301_ = leanh::lean_ctor_get(v_toApplicative_300_, 1);
    leanh::lean_inc(v_toPure_301_);
    leanh::lean_dec_ref(v_toApplicative_300_);
    v___f_302_ = leanh::lean_alloc_closure(
        l_StateCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_302_, 0, v_toPure_301_);
    v___x_303_ =
        leanh::lean_apply_3(v_x_298_, leanh::lean_box(0), v_s_299_, v___f_302_);
    return v___x_303_;
}
pub unsafe fn l_StateCpsT_run(
    mut v_00_u03b1_304_: *mut leanh::LeanObject,
    mut v_00_u03c3_305_: *mut leanh::LeanObject,
    mut v_m_306_: *mut leanh::LeanObject,
    mut v_inst_307_: *mut leanh::LeanObject,
    mut v_x_308_: *mut leanh::LeanObject,
    mut v_s_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_310_ = leanh::lean_ctor_get(v_inst_307_, 0);
    leanh::lean_inc_ref(v_toApplicative_310_);
    leanh::lean_dec_ref(v_inst_307_);
    v_toPure_311_ = leanh::lean_ctor_get(v_toApplicative_310_, 1);
    leanh::lean_inc(v_toPure_311_);
    leanh::lean_dec_ref(v_toApplicative_310_);
    v___f_312_ = leanh::lean_alloc_closure(
        l_StateCpsT_run___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_312_, 0, v_toPure_311_);
    v___x_313_ =
        leanh::lean_apply_3(v_x_308_, leanh::lean_box(0), v_s_309_, v___f_312_);
    return v___x_313_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg___lam__0(
    mut v_toPure_314_: *mut leanh::LeanObject,
    mut v_a_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = leanh::lean_apply_2(v_toPure_314_, leanh::lean_box(0), v_a_315_);
    return v___x_317_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg___lam__0___boxed(
    mut v_toPure_318_: *mut leanh::LeanObject,
    mut v_a_319_: *mut leanh::LeanObject,
    mut v_x_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l_StateCpsT_run_x27___redArg___lam__0(v_toPure_318_, v_a_319_, v_x_320_);
    leanh::lean_dec(v_x_320_);
    return v_res_321_;
}
pub unsafe fn l_StateCpsT_run_x27___redArg(
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_x_323_: *mut leanh::LeanObject,
    mut v_s_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_325_ = leanh::lean_ctor_get(v_inst_322_, 0);
    leanh::lean_inc_ref(v_toApplicative_325_);
    leanh::lean_dec_ref(v_inst_322_);
    v_toPure_326_ = leanh::lean_ctor_get(v_toApplicative_325_, 1);
    leanh::lean_inc(v_toPure_326_);
    leanh::lean_dec_ref(v_toApplicative_325_);
    v___f_327_ = leanh::lean_alloc_closure(
        l_StateCpsT_run_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_327_, 0, v_toPure_326_);
    v___x_328_ =
        leanh::lean_apply_3(v_x_323_, leanh::lean_box(0), v_s_324_, v___f_327_);
    return v___x_328_;
}
pub unsafe fn l_StateCpsT_run_x27(
    mut v_00_u03b1_329_: *mut leanh::LeanObject,
    mut v_00_u03c3_330_: *mut leanh::LeanObject,
    mut v_m_331_: *mut leanh::LeanObject,
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_x_333_: *mut leanh::LeanObject,
    mut v_s_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_335_ = leanh::lean_ctor_get(v_inst_332_, 0);
    leanh::lean_inc_ref(v_toApplicative_335_);
    leanh::lean_dec_ref(v_inst_332_);
    v_toPure_336_ = leanh::lean_ctor_get(v_toApplicative_335_, 1);
    leanh::lean_inc(v_toPure_336_);
    leanh::lean_dec_ref(v_toApplicative_335_);
    v___f_337_ = leanh::lean_alloc_closure(
        l_StateCpsT_run_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_337_, 0, v_toPure_336_);
    v___x_338_ =
        leanh::lean_apply_3(v_x_333_, leanh::lean_box(0), v_s_334_, v___f_337_);
    return v___x_338_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__0(
    mut v_f_339_: *mut leanh::LeanObject,
    mut v_k_340_: *mut leanh::LeanObject,
    mut v_a_341_: *mut leanh::LeanObject,
    mut v_s_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = leanh::lean_apply_1(v_f_339_, v_a_341_);
    v___x_344_ = leanh::lean_apply_2(v_k_340_, v___x_343_, v_s_342_);
    return v___x_344_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__1(
    mut v_00_u03b1_345_: *mut leanh::LeanObject,
    mut v_00_u03b2_346_: *mut leanh::LeanObject,
    mut v_f_347_: *mut leanh::LeanObject,
    mut v_x_348_: *mut leanh::LeanObject,
    mut v_00_u03b4_349_: *mut leanh::LeanObject,
    mut v_s_350_: *mut leanh::LeanObject,
    mut v_k_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_352_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_352_, 0, v_f_347_);
    leanh::lean_closure_set(v___f_352_, 1, v_k_351_);
    v___x_353_ =
        leanh::lean_apply_3(v_x_348_, leanh::lean_box(0), v_s_350_, v___f_352_);
    return v___x_353_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__2(
    mut v___f_354_: *mut leanh::LeanObject,
    mut v_00_u03b1_355_: *mut leanh::LeanObject,
    mut v_00_u03b2_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
    mut v___y_358_: *mut leanh::LeanObject,
    mut v___y_359_: *mut leanh::LeanObject,
    mut v___y_360_: *mut leanh::LeanObject,
    mut v___y_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_362_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_362_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_362_, 2, v___y_357_);
    v___x_363_ = leanh::lean_apply_7(
        v___f_354_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_362_,
        v___y_358_,
        leanh::lean_box(0),
        v___y_360_,
        v___y_361_,
    );
    return v___x_363_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__3(
    mut v_00_u03b1_364_: *mut leanh::LeanObject,
    mut v_a_365_: *mut leanh::LeanObject,
    mut v_x_366_: *mut leanh::LeanObject,
    mut v_s_367_: *mut leanh::LeanObject,
    mut v_k_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = leanh::lean_apply_2(v_k_368_, v_a_365_, v_s_367_);
    return v___x_369_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__4(
    mut v_x_370_: *mut leanh::LeanObject,
    mut v___f_371_: *mut leanh::LeanObject,
    mut v___y_372_: *mut leanh::LeanObject,
    mut v_a_373_: *mut leanh::LeanObject,
    mut v_s_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = leanh::lean_box(0);
    v___x_376_ = leanh::lean_apply_1(v_x_370_, v___x_375_);
    v___x_377_ = leanh::lean_apply_7(
        v___f_371_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_a_373_,
        v___x_376_,
        leanh::lean_box(0),
        v_s_374_,
        v___y_372_,
    );
    return v___x_377_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__5(
    mut v___f_378_: *mut leanh::LeanObject,
    mut v_00_u03b1_379_: *mut leanh::LeanObject,
    mut v_00_u03b2_380_: *mut leanh::LeanObject,
    mut v_f_381_: *mut leanh::LeanObject,
    mut v_x_382_: *mut leanh::LeanObject,
    mut v___y_383_: *mut leanh::LeanObject,
    mut v___y_384_: *mut leanh::LeanObject,
    mut v___y_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_386_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__4 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_386_, 0, v_x_382_);
    leanh::lean_closure_set(v___f_386_, 1, v___f_378_);
    leanh::lean_closure_set(v___f_386_, 2, v___y_385_);
    v___x_387_ =
        leanh::lean_apply_3(v_f_381_, leanh::lean_box(0), v___y_384_, v___f_386_);
    return v___x_387_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__6(
    mut v_f_388_: *mut leanh::LeanObject,
    mut v_k_389_: *mut leanh::LeanObject,
    mut v_a_390_: *mut leanh::LeanObject,
    mut v_s_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = leanh::lean_apply_4(
        v_f_388_,
        v_a_390_,
        leanh::lean_box(0),
        v_s_391_,
        v_k_389_,
    );
    return v___x_392_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__7(
    mut v_00_u03b1_393_: *mut leanh::LeanObject,
    mut v_00_u03b2_394_: *mut leanh::LeanObject,
    mut v_x_395_: *mut leanh::LeanObject,
    mut v_f_396_: *mut leanh::LeanObject,
    mut v_00_u03b4_397_: *mut leanh::LeanObject,
    mut v_s_398_: *mut leanh::LeanObject,
    mut v_k_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_400_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__6 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_400_, 0, v_f_396_);
    leanh::lean_closure_set(v___f_400_, 1, v_k_399_);
    v___x_401_ =
        leanh::lean_apply_3(v_x_395_, leanh::lean_box(0), v_s_398_, v___f_400_);
    return v___x_401_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__8(
    mut v_a_402_: *mut leanh::LeanObject,
    mut v_x_403_: *mut leanh::LeanObject,
    mut v___y_404_: *mut leanh::LeanObject,
    mut v___y_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_apply_2(v___y_406_, v_a_402_, v___y_405_);
    return v___x_407_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__8___boxed(
    mut v_a_408_: *mut leanh::LeanObject,
    mut v_x_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ =
        l_StateCpsT_instMonad___lam__8(v_a_408_, v_x_409_, v___y_410_, v___y_411_, v___y_412_);
    leanh::lean_dec(v_x_409_);
    return v_res_413_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__9(
    mut v_y_414_: *mut leanh::LeanObject,
    mut v___f_415_: *mut leanh::LeanObject,
    mut v_a_416_: *mut leanh::LeanObject,
    mut v___y_417_: *mut leanh::LeanObject,
    mut v___y_418_: *mut leanh::LeanObject,
    mut v___y_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_420_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__8___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_420_, 0, v_a_416_);
    v___x_421_ = leanh::lean_box(0);
    v___x_422_ = leanh::lean_apply_1(v_y_414_, v___x_421_);
    v___x_423_ = leanh::lean_apply_7(
        v___f_415_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_422_,
        v___f_420_,
        leanh::lean_box(0),
        v___y_418_,
        v___y_419_,
    );
    return v___x_423_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__10(
    mut v___f_424_: *mut leanh::LeanObject,
    mut v_00_u03b1_425_: *mut leanh::LeanObject,
    mut v_00_u03b2_426_: *mut leanh::LeanObject,
    mut v_x_427_: *mut leanh::LeanObject,
    mut v_y_428_: *mut leanh::LeanObject,
    mut v___y_429_: *mut leanh::LeanObject,
    mut v___y_430_: *mut leanh::LeanObject,
    mut v___y_431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___f_424_);
    v___f_432_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__9 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_432_, 0, v_y_428_);
    leanh::lean_closure_set(v___f_432_, 1, v___f_424_);
    v___x_433_ = leanh::lean_apply_7(
        v___f_424_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_427_,
        v___f_432_,
        leanh::lean_box(0),
        v___y_430_,
        v___y_431_,
    );
    return v___x_433_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__11(
    mut v_y_434_: *mut leanh::LeanObject,
    mut v___y_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_s_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = leanh::lean_box(0);
    v___x_439_ = leanh::lean_apply_4(
        v_y_434_,
        v___x_438_,
        leanh::lean_box(0),
        v_s_437_,
        v___y_435_,
    );
    return v___x_439_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__11___boxed(
    mut v_y_440_: *mut leanh::LeanObject,
    mut v___y_441_: *mut leanh::LeanObject,
    mut v_a_442_: *mut leanh::LeanObject,
    mut v_s_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l_StateCpsT_instMonad___lam__11(v_y_440_, v___y_441_, v_a_442_, v_s_443_);
    leanh::lean_dec(v_a_442_);
    return v_res_444_;
}
pub unsafe fn l_StateCpsT_instMonad___lam__12(
    mut v_00_u03b1_445_: *mut leanh::LeanObject,
    mut v_00_u03b2_446_: *mut leanh::LeanObject,
    mut v_x_447_: *mut leanh::LeanObject,
    mut v_y_448_: *mut leanh::LeanObject,
    mut v___y_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_452_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonad___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_452_, 0, v_y_448_);
    leanh::lean_closure_set(v___f_452_, 1, v___y_451_);
    v___x_453_ =
        leanh::lean_apply_3(v_x_447_, leanh::lean_box(0), v___y_450_, v___f_452_);
    return v___x_453_;
}
pub unsafe fn l_StateCpsT_instMonad(
    mut v_00_u03c3_476_: *mut leanh::LeanObject,
    mut v_m_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = l_StateCpsT_instMonad___closed__9;
    return v___x_478_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__0(
    mut v_x_479_: *mut leanh::LeanObject,
    mut v_s_480_: *mut leanh::LeanObject,
    mut v_k_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_480_);
    v___x_482_ = leanh::lean_apply_2(v_k_481_, v_s_480_, v_s_480_);
    return v___x_482_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__1(
    mut v_s_483_: *mut leanh::LeanObject,
    mut v_x_484_: *mut leanh::LeanObject,
    mut v_x_485_: *mut leanh::LeanObject,
    mut v_k_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = leanh::lean_box(0);
    v___x_488_ = leanh::lean_apply_2(v_k_486_, v___x_487_, v_s_483_);
    return v___x_488_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__1___boxed(
    mut v_s_489_: *mut leanh::LeanObject,
    mut v_x_490_: *mut leanh::LeanObject,
    mut v_x_491_: *mut leanh::LeanObject,
    mut v_k_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = l_StateCpsT_instMonadStateOf___lam__1(v_s_489_, v_x_490_, v_x_491_, v_k_492_);
    leanh::lean_dec(v_x_491_);
    return v_res_493_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf___lam__2(
    mut v_00_u03b1_494_: *mut leanh::LeanObject,
    mut v_f_495_: *mut leanh::LeanObject,
    mut v_x_496_: *mut leanh::LeanObject,
    mut v_s_497_: *mut leanh::LeanObject,
    mut v_k_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = leanh::lean_apply_1(v_f_495_, v_s_497_);
    v_fst_500_ = leanh::lean_ctor_get(v___x_499_, 0);
    leanh::lean_inc(v_fst_500_);
    v_snd_501_ = leanh::lean_ctor_get(v___x_499_, 1);
    leanh::lean_inc(v_snd_501_);
    leanh::lean_dec_ref(v___x_499_);
    v___x_502_ = leanh::lean_apply_2(v_k_498_, v_fst_500_, v_snd_501_);
    return v___x_502_;
}
pub unsafe fn l_StateCpsT_instMonadStateOf(
    mut v_00_u03c3_510_: *mut leanh::LeanObject,
    mut v_m_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = l_StateCpsT_instMonadStateOf___closed__3;
    return v___x_512_;
}
pub unsafe fn _init_l_StateCpsT_instMonadAttach___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l_StateCpsT_instMonad___closed__9;
    v___x_514_ = l_MonadAttach_trivial___redArg(v___x_513_);
    return v___x_514_;
}
pub unsafe fn l_StateCpsT_instMonadAttach(
    mut v_m_515_: *mut leanh::LeanObject,
    mut v_00_u03b5_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_StateCpsT_instMonadAttach___closed__0),
        core::ptr::addr_of_mut!(l_StateCpsT_instMonadAttach___closed__0_once),
        _init_l_StateCpsT_instMonadAttach___closed__0,
    );
    return v___x_517_;
}
pub unsafe fn l_StateCpsT_lift___redArg___lam__0(
    mut v_k_518_: *mut leanh::LeanObject,
    mut v_s_519_: *mut leanh::LeanObject,
    mut v_x_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ = leanh::lean_apply_2(v_k_518_, v_x_520_, v_s_519_);
    return v___x_521_;
}
pub unsafe fn l_StateCpsT_lift___redArg(
    mut v_inst_522_: *mut leanh::LeanObject,
    mut v_x_523_: *mut leanh::LeanObject,
    mut v_s_524_: *mut leanh::LeanObject,
    mut v_k_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_526_ = leanh::lean_ctor_get(v_inst_522_, 1);
    leanh::lean_inc(v_toBind_526_);
    leanh::lean_dec_ref(v_inst_522_);
    v___f_527_ = leanh::lean_alloc_closure(
        l_StateCpsT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_527_, 0, v_k_525_);
    leanh::lean_closure_set(v___f_527_, 1, v_s_524_);
    v___x_528_ = leanh::lean_apply_4(
        v_toBind_526_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_523_,
        v___f_527_,
    );
    return v___x_528_;
}
pub unsafe fn l_StateCpsT_lift(
    mut v_00_u03b1_529_: *mut leanh::LeanObject,
    mut v_00_u03c3_530_: *mut leanh::LeanObject,
    mut v_m_531_: *mut leanh::LeanObject,
    mut v_inst_532_: *mut leanh::LeanObject,
    mut v_x_533_: *mut leanh::LeanObject,
    mut v_x_534_: *mut leanh::LeanObject,
    mut v_s_535_: *mut leanh::LeanObject,
    mut v_k_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_537_ = leanh::lean_ctor_get(v_inst_532_, 1);
    leanh::lean_inc(v_toBind_537_);
    leanh::lean_dec_ref(v_inst_532_);
    v___f_538_ = leanh::lean_alloc_closure(
        l_StateCpsT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_538_, 0, v_k_536_);
    leanh::lean_closure_set(v___f_538_, 1, v_s_535_);
    v___x_539_ = leanh::lean_apply_4(
        v_toBind_537_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_533_,
        v___f_538_,
    );
    return v___x_539_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0(
    mut v___y_540_: *mut leanh::LeanObject,
    mut v___y_541_: *mut leanh::LeanObject,
    mut v_x_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = leanh::lean_apply_2(v___y_540_, v_x_542_, v___y_541_);
    return v___x_543_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1(
    mut v_inst_544_: *mut leanh::LeanObject,
    mut v_00_u03b1_545_: *mut leanh::LeanObject,
    mut v___y_546_: *mut leanh::LeanObject,
    mut v___y_547_: *mut leanh::LeanObject,
    mut v___y_548_: *mut leanh::LeanObject,
    mut v___y_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_550_ = leanh::lean_ctor_get(v_inst_544_, 1);
    leanh::lean_inc(v_toBind_550_);
    leanh::lean_dec_ref(v_inst_544_);
    v___f_551_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_551_, 0, v___y_549_);
    leanh::lean_closure_set(v___f_551_, 1, v___y_548_);
    v___x_552_ = leanh::lean_apply_4(
        v_toBind_550_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___y_546_,
        v___f_551_,
    );
    return v___x_552_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad___redArg(
    mut v_inst_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_554_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_554_, 0, v_inst_553_);
    return v___f_554_;
}
pub unsafe fn l_StateCpsT_instMonadLiftOfMonad(
    mut v_00_u03c3_555_: *mut leanh::LeanObject,
    mut v_m_556_: *mut leanh::LeanObject,
    mut v_inst_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = leanh::lean_alloc_closure(
        l_StateCpsT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_558_, 0, v_inst_557_);
    return v___f_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_StateCps(
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
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_StateCps(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_StateCps(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateCps(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_StateCps(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_StateCps(builtin);
}