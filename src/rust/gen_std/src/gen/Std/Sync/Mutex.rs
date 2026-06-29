// Lean compiler output
// Module: Std.Sync.Mutex
// Imports: Std.Sync.Basic Init.While
use crate::ffi::{
    lean_io_basemutex_lock, lean_io_basemutex_new, lean_io_basemutex_try_lock,
    lean_io_basemutex_unlock, lean_io_condvar_new, lean_io_condvar_notify_all,
    lean_io_condvar_notify_one, lean_io_condvar_wait, lean_st_mk_ref,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___aux__13___boxed, l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_instMonadLiftT___lam__0___boxed, l_instMonadLiftTOfMonadLift___redArg___lam__0, l_liftM,
};
use crate::r#gen::Init::While::{
    initialize_Init_While, l___private_Init_While_0__whileM_erased___redArg,
    runtime_initialize_Init_While,
};
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
pub static mut l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Std_Sync_Mutex_0__Std_CondvarImpl: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_instCoeOutMutexBaseMutex___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instCoeOutMutexBaseMutex___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instCoeOutMutexBaseMutex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutMutexBaseMutex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Mutex_atomically___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Mutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Mutex_atomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Mutex_tryAtomically___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Mutex_tryAtomically___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Mutex_tryAtomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_tryAtomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Mutex_tryAtomically___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Mutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Mutex_tryAtomically___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_tryAtomically___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Mutex_atomicallyOnce___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Mutex_atomicallyOnce___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomicallyOnce___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Mutex_atomicallyOnce___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Mutex_atomicallyOnce___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomicallyOnce___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl()
-> *mut crate::leanh::LeanObject {
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = crate::leanh::lean_box(0);
    return v___x_299_;
}
pub unsafe fn l_Std_BaseMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = lean_io_basemutex_new();
    return v_res_302_;
}
pub unsafe fn l_Std_BaseMutex_lock___boxed(
    mut v_mutex_305_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = lean_io_basemutex_lock(v_mutex_305_);
    crate::leanh::lean_dec(v_mutex_305_);
    return v_res_307_;
}
pub unsafe fn l_Std_BaseMutex_tryLock___boxed(
    mut v_mutex_310_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: u8 = 0;
    let mut v_r_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = lean_io_basemutex_try_lock(v_mutex_310_);
    crate::leanh::lean_dec(v_mutex_310_);
    v_r_313_ = crate::leanh::lean_box((v_res_312_) as usize);
    return v_r_313_;
}
pub unsafe fn l_Std_BaseMutex_unlock___boxed(
    mut v_mutex_316_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = lean_io_basemutex_unlock(v_mutex_316_);
    crate::leanh::lean_dec(v_mutex_316_);
    return v_res_318_;
}
pub unsafe fn _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl() -> *mut crate::leanh::LeanObject
{
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = crate::leanh::lean_box(0);
    return v___x_319_;
}
pub unsafe fn l_Std_Condvar_new___boxed(
    mut v_a_00___x40___internal___hyg_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_io_condvar_new();
    return v_res_322_;
}
pub unsafe fn l_Std_Condvar_wait___boxed(
    mut v_condvar_326_: *mut crate::leanh::LeanObject,
    mut v_mutex_327_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_329_ = lean_io_condvar_wait(v_condvar_326_, v_mutex_327_);
    crate::leanh::lean_dec(v_mutex_327_);
    crate::leanh::lean_dec(v_condvar_326_);
    return v_res_329_;
}
pub unsafe fn l_Std_Condvar_notifyOne___boxed(
    mut v_condvar_332_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = lean_io_condvar_notify_one(v_condvar_332_);
    crate::leanh::lean_dec(v_condvar_332_);
    return v_res_334_;
}
pub unsafe fn l_Std_Condvar_notifyAll___boxed(
    mut v_condvar_337_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = lean_io_condvar_notify_all(v_condvar_337_);
    crate::leanh::lean_dec(v_condvar_337_);
    return v_res_339_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__0(
    mut v_toPure_340_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_350_: u8 = 0;
    let mut v_a_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_354_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_341_) == 0 {
                    v_a_342_ = crate::leanh::lean_ctor_get(v_____do__lift_341_, 0);
                    v_isSharedCheck_350_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_341_)) as u8;
                    if v_isSharedCheck_350_ == 0 {
                        v___x_344_ = v_____do__lift_341_;
                        v_isShared_345_ = v_isSharedCheck_350_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_342_);
                        crate::leanh::lean_dec(v_____do__lift_341_);
                        v___x_344_ = crate::leanh::lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_350_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_351_ = crate::leanh::lean_ctor_get(v_____do__lift_341_, 0);
                    v_isSharedCheck_359_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_341_)) as u8;
                    if v_isSharedCheck_359_ == 0 {
                        v___x_353_ = v_____do__lift_341_;
                        v_isShared_354_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_351_);
                        crate::leanh::lean_dec(v_____do__lift_341_);
                        v___x_353_ = crate::leanh::lean_box(0);
                        v_isShared_354_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_345_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_344_, 1);
                    v___x_347_ = v___x_344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_342_);
                    v___x_347_ = v_reuseFailAlloc_349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_348_ = crate::leanh::lean_apply_2(
                    v_toPure_340_,
                    crate::leanh::lean_box(0),
                    v___x_347_,
                );
                return v___x_348_;
            }
            3 => {
                if v_isShared_354_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_353_, 0);
                    v___x_356_ = v___x_353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_351_);
                    v___x_356_ = v_reuseFailAlloc_358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_357_ = crate::leanh::lean_apply_2(
                    v_toPure_340_,
                    crate::leanh::lean_box(0),
                    v___x_356_,
                );
                return v___x_357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__1(
    mut v___x_360_: *mut crate::leanh::LeanObject,
    mut v_toPure_361_: *mut crate::leanh::LeanObject,
    mut v_r_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_363_, 0, v___x_360_);
    v___x_364_ = crate::leanh::lean_apply_2(v_toPure_361_, crate::leanh::lean_box(0), v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__2(
    mut v_condvar_365_: *mut crate::leanh::LeanObject,
    mut v_mutex_366_: *mut crate::leanh::LeanObject,
    mut v_inst_367_: *mut crate::leanh::LeanObject,
    mut v_toBind_368_: *mut crate::leanh::LeanObject,
    mut v___f_369_: *mut crate::leanh::LeanObject,
    mut v___x_370_: *mut crate::leanh::LeanObject,
    mut v_toPure_371_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_372_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_372_ == 0 {
        let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_371_);
        v___x_373_ = crate::leanh::lean_alloc_closure(
            l_Std_Condvar_wait___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___x_373_, 0, v_condvar_365_);
        crate::leanh::lean_closure_set(v___x_373_, 1, v_mutex_366_);
        v___x_374_ = crate::leanh::lean_apply_2(v_inst_367_, crate::leanh::lean_box(0), v___x_373_);
        v___x_375_ = crate::leanh::lean_apply_4(
            v_toBind_368_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_374_,
            v___f_369_,
        );
        return v___x_375_;
    } else {
        let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_369_);
        crate::leanh::lean_dec(v_toBind_368_);
        crate::leanh::lean_dec(v_inst_367_);
        crate::leanh::lean_dec(v_mutex_366_);
        crate::leanh::lean_dec(v_condvar_365_);
        v___x_376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_376_, 0, v___x_370_);
        v___x_377_ =
            crate::leanh::lean_apply_2(v_toPure_371_, crate::leanh::lean_box(0), v___x_376_);
        return v___x_377_;
    }
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__2___boxed(
    mut v_condvar_378_: *mut crate::leanh::LeanObject,
    mut v_mutex_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
    mut v_toBind_381_: *mut crate::leanh::LeanObject,
    mut v___f_382_: *mut crate::leanh::LeanObject,
    mut v___x_383_: *mut crate::leanh::LeanObject,
    mut v_toPure_384_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_261__boxed_386_: u8 = 0;
    let mut v_res_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_261__boxed_386_ = (crate::leanh::lean_unbox(v_____do__lift_385_) as u8);
    v_res_387_ = l_Std_Condvar_waitUntil___redArg___lam__2(
        v_condvar_378_,
        v_mutex_379_,
        v_inst_380_,
        v_toBind_381_,
        v___f_382_,
        v___x_383_,
        v_toPure_384_,
        v_____do__lift_261__boxed_386_,
    );
    return v_res_387_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__3(
    mut v_toBind_388_: *mut crate::leanh::LeanObject,
    mut v_pred_389_: *mut crate::leanh::LeanObject,
    mut v___f_390_: *mut crate::leanh::LeanObject,
    mut v___f_391_: *mut crate::leanh::LeanObject,
    mut v_b_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_388_);
    v___x_393_ = crate::leanh::lean_apply_4(
        v_toBind_388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_pred_389_,
        v___f_390_,
    );
    v___x_394_ = crate::leanh::lean_apply_4(
        v_toBind_388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_393_,
        v___f_391_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__4(
    mut v_toPure_395_: *mut crate::leanh::LeanObject,
    mut v___x_396_: *mut crate::leanh::LeanObject,
    mut v_____s_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_apply_2(v_toPure_395_, crate::leanh::lean_box(0), v___x_396_);
    return v___x_398_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg(
    mut v_inst_399_: *mut crate::leanh::LeanObject,
    mut v_inst_400_: *mut crate::leanh::LeanObject,
    mut v_condvar_401_: *mut crate::leanh::LeanObject,
    mut v_mutex_402_: *mut crate::leanh::LeanObject,
    mut v_pred_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_404_ = crate::leanh::lean_ctor_get(v_inst_399_, 0);
    v_toBind_405_ = crate::leanh::lean_ctor_get(v_inst_399_, 1);
    crate::leanh::lean_inc_n(v_toBind_405_, 3);
    v_toPure_406_ = crate::leanh::lean_ctor_get(v_toApplicative_404_, 1);
    v___x_407_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_n(v_toPure_406_, 4);
    v___f_408_ = crate::leanh::lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_408_, 0, v_toPure_406_);
    v___f_409_ = crate::leanh::lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_409_, 0, v___x_407_);
    crate::leanh::lean_closure_set(v___f_409_, 1, v_toPure_406_);
    v___f_410_ = crate::leanh::lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_410_, 0, v_condvar_401_);
    crate::leanh::lean_closure_set(v___f_410_, 1, v_mutex_402_);
    crate::leanh::lean_closure_set(v___f_410_, 2, v_inst_400_);
    crate::leanh::lean_closure_set(v___f_410_, 3, v_toBind_405_);
    crate::leanh::lean_closure_set(v___f_410_, 4, v___f_409_);
    crate::leanh::lean_closure_set(v___f_410_, 5, v___x_407_);
    crate::leanh::lean_closure_set(v___f_410_, 6, v_toPure_406_);
    v___f_411_ = crate::leanh::lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_411_, 0, v_toBind_405_);
    crate::leanh::lean_closure_set(v___f_411_, 1, v_pred_403_);
    crate::leanh::lean_closure_set(v___f_411_, 2, v___f_410_);
    crate::leanh::lean_closure_set(v___f_411_, 3, v___f_408_);
    v___f_412_ = crate::leanh::lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__4 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_412_, 0, v_toPure_406_);
    crate::leanh::lean_closure_set(v___f_412_, 1, v___x_407_);
    v___x_413_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_399_, v___f_411_, v___x_407_);
    v___x_414_ = crate::leanh::lean_apply_4(
        v_toBind_405_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_413_,
        v___f_412_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_Condvar_waitUntil(
    mut v_m_415_: *mut crate::leanh::LeanObject,
    mut v_inst_416_: *mut crate::leanh::LeanObject,
    mut v_inst_417_: *mut crate::leanh::LeanObject,
    mut v_condvar_418_: *mut crate::leanh::LeanObject,
    mut v_mutex_419_: *mut crate::leanh::LeanObject,
    mut v_pred_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Std_Condvar_waitUntil___redArg(
        v_inst_416_,
        v_inst_417_,
        v_condvar_418_,
        v_mutex_419_,
        v_pred_420_,
    );
    return v___x_421_;
}
pub unsafe fn l_Std_instCoeOutMutexBaseMutex___lam__0(
    mut v_self_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mutex_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mutex_423_ = crate::leanh::lean_ctor_get(v_self_422_, 1);
    crate::leanh::lean_inc(v_mutex_423_);
    return v_mutex_423_;
}
pub unsafe fn l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(
    mut v_self_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Std_instCoeOutMutexBaseMutex___lam__0(v_self_424_);
    crate::leanh::lean_dec_ref(v_self_424_);
    return v_res_425_;
}
pub unsafe fn l_Std_instCoeOutMutexBaseMutex(
    mut v_00_u03b1_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_428_ = l_Std_instCoeOutMutexBaseMutex___closed__0;
    return v___f_428_;
}
pub unsafe fn l_Std_Mutex_new___redArg(
    mut v_a_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_st_mk_ref(v_a_429_);
    v___x_432_ = lean_io_basemutex_new();
    v___x_433_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_433_, 0, v___x_431_);
    crate::leanh::lean_ctor_set(v___x_433_, 1, v___x_432_);
    return v___x_433_;
}
pub unsafe fn l_Std_Mutex_new___redArg___boxed(
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Mutex_new___redArg(v_a_434_);
    return v_res_436_;
}
pub unsafe fn l_Std_Mutex_new(
    mut v_00_u03b1_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Std_Mutex_new___redArg(v_a_438_);
    return v___x_440_;
}
pub unsafe fn l_Std_Mutex_new___boxed(
    mut v_00_u03b1_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
    mut v_a_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l_Std_Mutex_new(v_00_u03b1_441_, v_a_442_);
    return v_res_444_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__0(
    mut v_k_445_: *mut crate::leanh::LeanObject,
    mut v_ref_446_: *mut crate::leanh::LeanObject,
    mut v_____r_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = crate::leanh::lean_apply_1(v_k_445_, v_ref_446_);
    return v___x_448_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__1(
    mut v_x_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_450_ = crate::leanh::lean_ctor_get(v_x_449_, 0);
    crate::leanh::lean_inc(v_fst_450_);
    return v_fst_450_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__1___boxed(
    mut v_x_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_451_);
    crate::leanh::lean_dec_ref(v_x_451_);
    return v_res_452_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__2(
    mut v___x_453_: *mut crate::leanh::LeanObject,
    mut v_x_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_453_);
    return v___x_453_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__2___boxed(
    mut v___x_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_455_, v_x_456_);
    crate::leanh::lean_dec(v_x_456_);
    crate::leanh::lean_dec(v___x_455_);
    return v_res_457_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg(
    mut v_inst_459_: *mut crate::leanh::LeanObject,
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_inst_461_: *mut crate::leanh::LeanObject,
    mut v_mutex_462_: *mut crate::leanh::LeanObject,
    mut v_k_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_464_ = crate::leanh::lean_ctor_get(v_inst_459_, 0);
    v_toFunctor_465_ = crate::leanh::lean_ctor_get(v_toApplicative_464_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_465_);
    v_toBind_466_ = crate::leanh::lean_ctor_get(v_inst_459_, 1);
    crate::leanh::lean_inc(v_toBind_466_);
    crate::leanh::lean_dec_ref(v_inst_459_);
    v_ref_467_ = crate::leanh::lean_ctor_get(v_mutex_462_, 0);
    crate::leanh::lean_inc(v_ref_467_);
    v_mutex_468_ = crate::leanh::lean_ctor_get(v_mutex_462_, 1);
    crate::leanh::lean_inc_n(v_mutex_468_, 2);
    crate::leanh::lean_dec_ref(v_mutex_462_);
    v_map_469_ = crate::leanh::lean_ctor_get(v_toFunctor_465_, 0);
    crate::leanh::lean_inc(v_map_469_);
    crate::leanh::lean_dec_ref(v_toFunctor_465_);
    v___x_470_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseMutex_lock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_470_, 0, v_mutex_468_);
    crate::leanh::lean_inc(v_inst_460_);
    v___x_471_ = crate::leanh::lean_apply_2(v_inst_460_, crate::leanh::lean_box(0), v___x_470_);
    v___f_472_ = crate::leanh::lean_alloc_closure(
        l_Std_Mutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_472_, 0, v_k_463_);
    crate::leanh::lean_closure_set(v___f_472_, 1, v_ref_467_);
    v___f_473_ = l_Std_Mutex_atomically___redArg___closed__0;
    v___x_474_ = crate::leanh::lean_apply_4(
        v_toBind_466_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_471_,
        v___f_472_,
    );
    v___x_475_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseMutex_unlock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_475_, 0, v_mutex_468_);
    v___x_476_ = crate::leanh::lean_apply_2(v_inst_460_, crate::leanh::lean_box(0), v___x_475_);
    v___f_477_ = crate::leanh::lean_alloc_closure(
        l_Std_Mutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_477_, 0, v___x_476_);
    v_y_478_ = crate::leanh::lean_apply_4(
        v_inst_461_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_474_,
        v___f_477_,
    );
    v___x_479_ = crate::leanh::lean_apply_4(
        v_map_469_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_473_,
        v_y_478_,
    );
    return v___x_479_;
}
pub unsafe fn l_Std_Mutex_atomically(
    mut v_m_480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_482_: *mut crate::leanh::LeanObject,
    mut v_inst_483_: *mut crate::leanh::LeanObject,
    mut v_inst_484_: *mut crate::leanh::LeanObject,
    mut v_inst_485_: *mut crate::leanh::LeanObject,
    mut v_mutex_486_: *mut crate::leanh::LeanObject,
    mut v_k_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Std_Mutex_atomically___redArg(
        v_inst_483_,
        v_inst_484_,
        v_inst_485_,
        v_mutex_486_,
        v_k_487_,
    );
    return v___x_488_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__0(
    mut v_x_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_490_ = crate::leanh::lean_ctor_get(v_x_489_, 0);
    crate::leanh::lean_inc(v_fst_490_);
    return v_fst_490_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_492_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_491_);
    crate::leanh::lean_dec_ref(v_x_491_);
    return v_res_492_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__1(
    mut v_val_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_494_, 0, v_val_493_);
    return v___x_494_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__2(
    mut v___x_495_: *mut crate::leanh::LeanObject,
    mut v_x_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_495_);
    return v___x_495_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_497_: *mut crate::leanh::LeanObject,
    mut v_x_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_497_, v_x_498_);
    crate::leanh::lean_dec(v_x_498_);
    crate::leanh::lean_dec(v___x_497_);
    return v_res_499_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_500_: *mut crate::leanh::LeanObject,
    mut v_k_501_: *mut crate::leanh::LeanObject,
    mut v_ref_502_: *mut crate::leanh::LeanObject,
    mut v___f_503_: *mut crate::leanh::LeanObject,
    mut v_mutex_504_: *mut crate::leanh::LeanObject,
    mut v_inst_505_: *mut crate::leanh::LeanObject,
    mut v_inst_506_: *mut crate::leanh::LeanObject,
    mut v___f_507_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_508_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_508_ == 0 {
        let mut v_toPure_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_507_);
        crate::leanh::lean_dec(v_inst_506_);
        crate::leanh::lean_dec(v_inst_505_);
        crate::leanh::lean_dec(v_mutex_504_);
        crate::leanh::lean_dec_ref(v___f_503_);
        crate::leanh::lean_dec(v_ref_502_);
        crate::leanh::lean_dec(v_k_501_);
        v_toPure_509_ = crate::leanh::lean_ctor_get(v_toApplicative_500_, 1);
        crate::leanh::lean_inc(v_toPure_509_);
        crate::leanh::lean_dec_ref(v_toApplicative_500_);
        v___x_510_ = crate::leanh::lean_box(0);
        v___x_511_ =
            crate::leanh::lean_apply_2(v_toPure_509_, crate::leanh::lean_box(0), v___x_510_);
        return v___x_511_;
    } else {
        let mut v_toFunctor_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_512_ = crate::leanh::lean_ctor_get(v_toApplicative_500_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_512_);
        crate::leanh::lean_dec_ref(v_toApplicative_500_);
        v_map_513_ = crate::leanh::lean_ctor_get(v_toFunctor_512_, 0);
        crate::leanh::lean_inc_n(v_map_513_, 2);
        crate::leanh::lean_dec_ref(v_toFunctor_512_);
        v___x_514_ = crate::leanh::lean_apply_1(v_k_501_, v_ref_502_);
        v___x_515_ = crate::leanh::lean_apply_4(
            v_map_513_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_503_,
            v___x_514_,
        );
        v___x_516_ = crate::leanh::lean_alloc_closure(
            l_Std_BaseMutex_unlock___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_516_, 0, v_mutex_504_);
        v___x_517_ = crate::leanh::lean_apply_2(v_inst_505_, crate::leanh::lean_box(0), v___x_516_);
        v___f_518_ = crate::leanh::lean_alloc_closure(
            l_Std_Mutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_518_, 0, v___x_517_);
        v_y_519_ = crate::leanh::lean_apply_4(
            v_inst_506_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_515_,
            v___f_518_,
        );
        v___x_520_ = crate::leanh::lean_apply_4(
            v_map_513_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_507_,
            v_y_519_,
        );
        return v___x_520_;
    }
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_521_: *mut crate::leanh::LeanObject,
    mut v_k_522_: *mut crate::leanh::LeanObject,
    mut v_ref_523_: *mut crate::leanh::LeanObject,
    mut v___f_524_: *mut crate::leanh::LeanObject,
    mut v_mutex_525_: *mut crate::leanh::LeanObject,
    mut v_inst_526_: *mut crate::leanh::LeanObject,
    mut v_inst_527_: *mut crate::leanh::LeanObject,
    mut v___f_528_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_140__boxed_530_: u8 = 0;
    let mut v_res_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_530_ = (crate::leanh::lean_unbox(v_____do__lift_529_) as u8);
    v_res_531_ = l_Std_Mutex_tryAtomically___redArg___lam__3(
        v_toApplicative_521_,
        v_k_522_,
        v_ref_523_,
        v___f_524_,
        v_mutex_525_,
        v_inst_526_,
        v_inst_527_,
        v___f_528_,
        v_____do__lift_140__boxed_530_,
    );
    return v_res_531_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg(
    mut v_inst_534_: *mut crate::leanh::LeanObject,
    mut v_inst_535_: *mut crate::leanh::LeanObject,
    mut v_inst_536_: *mut crate::leanh::LeanObject,
    mut v_mutex_537_: *mut crate::leanh::LeanObject,
    mut v_k_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_539_ = crate::leanh::lean_ctor_get(v_inst_534_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_539_);
    v_toBind_540_ = crate::leanh::lean_ctor_get(v_inst_534_, 1);
    crate::leanh::lean_inc(v_toBind_540_);
    crate::leanh::lean_dec_ref(v_inst_534_);
    v_ref_541_ = crate::leanh::lean_ctor_get(v_mutex_537_, 0);
    crate::leanh::lean_inc(v_ref_541_);
    v_mutex_542_ = crate::leanh::lean_ctor_get(v_mutex_537_, 1);
    crate::leanh::lean_inc_n(v_mutex_542_, 2);
    crate::leanh::lean_dec_ref(v_mutex_537_);
    v___f_543_ = l_Std_Mutex_tryAtomically___redArg___closed__0;
    v___f_544_ = l_Std_Mutex_tryAtomically___redArg___closed__1;
    crate::leanh::lean_inc(v_inst_535_);
    v___f_545_ = crate::leanh::lean_alloc_closure(
        l_Std_Mutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_545_, 0, v_toApplicative_539_);
    crate::leanh::lean_closure_set(v___f_545_, 1, v_k_538_);
    crate::leanh::lean_closure_set(v___f_545_, 2, v_ref_541_);
    crate::leanh::lean_closure_set(v___f_545_, 3, v___f_544_);
    crate::leanh::lean_closure_set(v___f_545_, 4, v_mutex_542_);
    crate::leanh::lean_closure_set(v___f_545_, 5, v_inst_535_);
    crate::leanh::lean_closure_set(v___f_545_, 6, v_inst_536_);
    crate::leanh::lean_closure_set(v___f_545_, 7, v___f_543_);
    v___x_546_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseMutex_tryLock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_546_, 0, v_mutex_542_);
    v___x_547_ = crate::leanh::lean_apply_2(v_inst_535_, crate::leanh::lean_box(0), v___x_546_);
    v___x_548_ = crate::leanh::lean_apply_4(
        v_toBind_540_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_547_,
        v___f_545_,
    );
    return v___x_548_;
}
pub unsafe fn l_Std_Mutex_tryAtomically(
    mut v_m_549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_550_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_551_: *mut crate::leanh::LeanObject,
    mut v_inst_552_: *mut crate::leanh::LeanObject,
    mut v_inst_553_: *mut crate::leanh::LeanObject,
    mut v_inst_554_: *mut crate::leanh::LeanObject,
    mut v_mutex_555_: *mut crate::leanh::LeanObject,
    mut v_k_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Std_Mutex_tryAtomically___redArg(
        v_inst_552_,
        v_inst_553_,
        v_inst_554_,
        v_mutex_555_,
        v_k_556_,
    );
    return v___x_557_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce___redArg___lam__0(
    mut v_k_558_: *mut crate::leanh::LeanObject,
    mut v_____r_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_560_);
    v___x_561_ = crate::leanh::lean_apply_1(v_k_558_, v___y_560_);
    return v___x_561_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(
    mut v_k_562_: *mut crate::leanh::LeanObject,
    mut v_____r_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Std_Mutex_atomicallyOnce___redArg___lam__0(v_k_562_, v_____r_563_, v___y_564_);
    crate::leanh::lean_dec(v___y_564_);
    return v_res_565_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce___redArg(
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_inst_569_: *mut crate::leanh::LeanObject,
    mut v_inst_570_: *mut crate::leanh::LeanObject,
    mut v_mutex_571_: *mut crate::leanh::LeanObject,
    mut v_condvar_572_: *mut crate::leanh::LeanObject,
    mut v_pred_573_: *mut crate::leanh::LeanObject,
    mut v_k_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_568_, 2);
    v___x_575_ = l_StateRefT_x27_instMonad___redArg(v_inst_568_);
    v_mutex_576_ = crate::leanh::lean_ctor_get(v_mutex_571_, 1);
    v___f_577_ = crate::leanh::lean_alloc_closure(
        l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_577_, 0, v_k_574_);
    v___f_578_ = l_Std_Mutex_atomicallyOnce___redArg___closed__0;
    v___x_579_ = l_Std_Mutex_atomicallyOnce___redArg___closed__1;
    crate::leanh::lean_inc(v_inst_569_);
    v___f_580_ = crate::leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_580_, 0, v_inst_569_);
    crate::leanh::lean_closure_set(v___f_580_, 1, v___x_579_);
    v_x_581_ = crate::leanh::lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v_x_581_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_x_581_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_x_581_, 2, v___f_580_);
    v___f_582_ = crate::leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_582_, 0, v___f_578_);
    crate::leanh::lean_closure_set(v___f_582_, 1, v_x_581_);
    crate::leanh::lean_inc(v_mutex_576_);
    v___x_583_ = l_Std_Condvar_waitUntil___redArg(
        v___x_575_,
        v___f_582_,
        v_condvar_572_,
        v_mutex_576_,
        v_pred_573_,
    );
    v___x_584_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_584_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_584_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_584_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_584_, 3, v_inst_568_);
    crate::leanh::lean_closure_set(v___x_584_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_584_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_584_, 6, v___x_583_);
    crate::leanh::lean_closure_set(v___x_584_, 7, v___f_577_);
    v___x_585_ = l_Std_Mutex_atomically___redArg(
        v_inst_568_,
        v_inst_569_,
        v_inst_570_,
        v_mutex_571_,
        v___x_584_,
    );
    return v___x_585_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce(
    mut v_m_586_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_588_: *mut crate::leanh::LeanObject,
    mut v_inst_589_: *mut crate::leanh::LeanObject,
    mut v_inst_590_: *mut crate::leanh::LeanObject,
    mut v_inst_591_: *mut crate::leanh::LeanObject,
    mut v_mutex_592_: *mut crate::leanh::LeanObject,
    mut v_condvar_593_: *mut crate::leanh::LeanObject,
    mut v_pred_594_: *mut crate::leanh::LeanObject,
    mut v_k_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Std_Mutex_atomicallyOnce___redArg(
        v_inst_589_,
        v_inst_590_,
        v_inst_591_,
        v_mutex_592_,
        v_condvar_593_,
        v_pred_594_,
        v_k_595_,
    );
    return v___x_596_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Mutex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl =
        _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl();
    l___private_Std_Sync_Mutex_0__Std_CondvarImpl =
        _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Mutex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Mutex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_Mutex(builtin);
}
