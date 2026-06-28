// Lean compiler output
// Module: Std.Sync.Mutex
// Imports: Std.Sync.Basic Init.While
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
use crate::lean_imports_rs::Init::System::ST::lean_st_mk_ref;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static mut l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Std_Sync_Mutex_0__Std_CondvarImpl: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_instCoeOutMutexBaseMutex___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_instCoeOutMutexBaseMutex___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instCoeOutMutexBaseMutex___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutMutexBaseMutex___closed__0_value) as *mut LeanObject;
pub static l_Std_Mutex_atomically___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Mutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Mutex_atomically___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomically___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Mutex_tryAtomically___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Mutex_tryAtomically___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Mutex_tryAtomically___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_tryAtomically___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Mutex_tryAtomically___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Mutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Mutex_tryAtomically___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_tryAtomically___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Mutex_atomicallyOnce___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Mutex_atomicallyOnce___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomicallyOnce___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Mutex_atomicallyOnce___redArg___closed__1_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Mutex_atomicallyOnce___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Mutex_atomicallyOnce___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl() -> *mut LeanObject {
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v___x_299_ = lean_box(0);
    return v___x_299_;
}
pub unsafe fn l_Std_BaseMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_res_302_ = lean_io_basemutex_new();
    return v_res_302_;
}
pub unsafe fn l_Std_BaseMutex_lock___boxed(
    mut v_mutex_305_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_307_: *mut LeanObject = core::ptr::null_mut();
    v_res_307_ = lean_io_basemutex_lock(v_mutex_305_);
    lean_dec(v_mutex_305_);
    return v_res_307_;
}
pub unsafe fn l_Std_BaseMutex_tryLock___boxed(
    mut v_mutex_310_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_312_: u8 = 0;
    let mut v_r_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_312_ = lean_io_basemutex_try_lock(v_mutex_310_);
    lean_dec(v_mutex_310_);
    v_r_313_ = lean_box((v_res_312_) as usize);
    return v_r_313_;
}
pub unsafe fn l_Std_BaseMutex_unlock___boxed(
    mut v_mutex_316_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_318_: *mut LeanObject = core::ptr::null_mut();
    v_res_318_ = lean_io_basemutex_unlock(v_mutex_316_);
    lean_dec(v_mutex_316_);
    return v_res_318_;
}
pub unsafe fn _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl() -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_box(0);
    return v___x_319_;
}
pub unsafe fn l_Std_Condvar_new___boxed(
    mut v_a_00___x40___internal___hyg_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_322_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_io_condvar_new();
    return v_res_322_;
}
pub unsafe fn l_Std_Condvar_wait___boxed(
    mut v_condvar_326_: *mut LeanObject,
    mut v_mutex_327_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_329_: *mut LeanObject = core::ptr::null_mut();
    v_res_329_ = lean_io_condvar_wait(v_condvar_326_, v_mutex_327_);
    lean_dec(v_mutex_327_);
    lean_dec(v_condvar_326_);
    return v_res_329_;
}
pub unsafe fn l_Std_Condvar_notifyOne___boxed(
    mut v_condvar_332_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = lean_io_condvar_notify_one(v_condvar_332_);
    lean_dec(v_condvar_332_);
    return v_res_334_;
}
pub unsafe fn l_Std_Condvar_notifyAll___boxed(
    mut v_condvar_337_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = lean_io_condvar_notify_all(v_condvar_337_);
    lean_dec(v_condvar_337_);
    return v_res_339_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__0(
    mut v_toPure_340_: *mut LeanObject,
    mut v_____do__lift_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_350_: u8 = 0;
    let mut v_a_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_354_: u8 = 0;
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_341_) == 0 {
                    v_a_342_ = lean_ctor_get(v_____do__lift_341_, 0);
                    v_isSharedCheck_350_ = (!lean_is_exclusive(v_____do__lift_341_)) as u8;
                    if v_isSharedCheck_350_ == 0 {
                        v___x_344_ = v_____do__lift_341_;
                        v_isShared_345_ = v_isSharedCheck_350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_342_);
                        lean_dec(v_____do__lift_341_);
                        v___x_344_ = lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_350_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_351_ = lean_ctor_get(v_____do__lift_341_, 0);
                    v_isSharedCheck_359_ = (!lean_is_exclusive(v_____do__lift_341_)) as u8;
                    if v_isSharedCheck_359_ == 0 {
                        v___x_353_ = v_____do__lift_341_;
                        v_isShared_354_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_351_);
                        lean_dec(v_____do__lift_341_);
                        v___x_353_ = lean_box(0);
                        v_isShared_354_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_345_ == 0 {
                    lean_ctor_set_tag(v___x_344_, 1);
                    v___x_347_ = v___x_344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_342_);
                    v___x_347_ = v_reuseFailAlloc_349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_348_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_347_);
                return v___x_348_;
            }
            3 => {
                if v_isShared_354_ == 0 {
                    lean_ctor_set_tag(v___x_353_, 0);
                    v___x_356_ = v___x_353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_351_);
                    v___x_356_ = v_reuseFailAlloc_358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_357_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_356_);
                return v___x_357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__1(
    mut v___x_360_: *mut LeanObject,
    mut v_toPure_361_: *mut LeanObject,
    mut v_r_362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_363_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_363_, 0, v___x_360_);
    v___x_364_ = lean_apply_2(v_toPure_361_, lean_box(0), v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__2(
    mut v_condvar_365_: *mut LeanObject,
    mut v_mutex_366_: *mut LeanObject,
    mut v_inst_367_: *mut LeanObject,
    mut v_toBind_368_: *mut LeanObject,
    mut v___f_369_: *mut LeanObject,
    mut v___x_370_: *mut LeanObject,
    mut v_toPure_371_: *mut LeanObject,
    mut v_____do__lift_372_: u8,
) -> *mut LeanObject {
    if v_____do__lift_372_ == 0 {
        let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_371_);
        v___x_373_ = lean_alloc_closure(l_Std_Condvar_wait___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___x_373_, 0, v_condvar_365_);
        lean_closure_set(v___x_373_, 1, v_mutex_366_);
        v___x_374_ = lean_apply_2(v_inst_367_, lean_box(0), v___x_373_);
        v___x_375_ = lean_apply_4(
            v_toBind_368_,
            lean_box(0),
            lean_box(0),
            v___x_374_,
            v___f_369_,
        );
        return v___x_375_;
    } else {
        let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_369_);
        lean_dec(v_toBind_368_);
        lean_dec(v_inst_367_);
        lean_dec(v_mutex_366_);
        lean_dec(v_condvar_365_);
        v___x_376_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_376_, 0, v___x_370_);
        v___x_377_ = lean_apply_2(v_toPure_371_, lean_box(0), v___x_376_);
        return v___x_377_;
    }
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__2___boxed(
    mut v_condvar_378_: *mut LeanObject,
    mut v_mutex_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_toBind_381_: *mut LeanObject,
    mut v___f_382_: *mut LeanObject,
    mut v___x_383_: *mut LeanObject,
    mut v_toPure_384_: *mut LeanObject,
    mut v_____do__lift_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_261__boxed_386_: u8 = 0;
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_261__boxed_386_ = (lean_unbox(v_____do__lift_385_) as u8);
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
    mut v_toBind_388_: *mut LeanObject,
    mut v_pred_389_: *mut LeanObject,
    mut v___f_390_: *mut LeanObject,
    mut v___f_391_: *mut LeanObject,
    mut v_b_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_388_);
    v___x_393_ = lean_apply_4(
        v_toBind_388_,
        lean_box(0),
        lean_box(0),
        v_pred_389_,
        v___f_390_,
    );
    v___x_394_ = lean_apply_4(
        v_toBind_388_,
        lean_box(0),
        lean_box(0),
        v___x_393_,
        v___f_391_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg___lam__4(
    mut v_toPure_395_: *mut LeanObject,
    mut v___x_396_: *mut LeanObject,
    mut v_____s_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_apply_2(v_toPure_395_, lean_box(0), v___x_396_);
    return v___x_398_;
}
pub unsafe fn l_Std_Condvar_waitUntil___redArg(
    mut v_inst_399_: *mut LeanObject,
    mut v_inst_400_: *mut LeanObject,
    mut v_condvar_401_: *mut LeanObject,
    mut v_mutex_402_: *mut LeanObject,
    mut v_pred_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_404_ = lean_ctor_get(v_inst_399_, 0);
    v_toBind_405_ = lean_ctor_get(v_inst_399_, 1);
    lean_inc_n(v_toBind_405_, 3);
    v_toPure_406_ = lean_ctor_get(v_toApplicative_404_, 1);
    v___x_407_ = lean_box(0);
    lean_inc_n(v_toPure_406_, 4);
    v___f_408_ = lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_408_, 0, v_toPure_406_);
    v___f_409_ = lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_409_, 0, v___x_407_);
    lean_closure_set(v___f_409_, 1, v_toPure_406_);
    v___f_410_ = lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_410_, 0, v_condvar_401_);
    lean_closure_set(v___f_410_, 1, v_mutex_402_);
    lean_closure_set(v___f_410_, 2, v_inst_400_);
    lean_closure_set(v___f_410_, 3, v_toBind_405_);
    lean_closure_set(v___f_410_, 4, v___f_409_);
    lean_closure_set(v___f_410_, 5, v___x_407_);
    lean_closure_set(v___f_410_, 6, v_toPure_406_);
    v___f_411_ = lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_411_, 0, v_toBind_405_);
    lean_closure_set(v___f_411_, 1, v_pred_403_);
    lean_closure_set(v___f_411_, 2, v___f_410_);
    lean_closure_set(v___f_411_, 3, v___f_408_);
    v___f_412_ = lean_alloc_closure(
        l_Std_Condvar_waitUntil___redArg___lam__4 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_412_, 0, v_toPure_406_);
    lean_closure_set(v___f_412_, 1, v___x_407_);
    v___x_413_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_399_, v___f_411_, v___x_407_);
    v___x_414_ = lean_apply_4(
        v_toBind_405_,
        lean_box(0),
        lean_box(0),
        v___x_413_,
        v___f_412_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_Condvar_waitUntil(
    mut v_m_415_: *mut LeanObject,
    mut v_inst_416_: *mut LeanObject,
    mut v_inst_417_: *mut LeanObject,
    mut v_condvar_418_: *mut LeanObject,
    mut v_mutex_419_: *mut LeanObject,
    mut v_pred_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_self_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mutex_423_: *mut LeanObject = core::ptr::null_mut();
    v_mutex_423_ = lean_ctor_get(v_self_422_, 1);
    lean_inc(v_mutex_423_);
    return v_mutex_423_;
}
pub unsafe fn l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(
    mut v_self_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_425_: *mut LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Std_instCoeOutMutexBaseMutex___lam__0(v_self_424_);
    lean_dec_ref(v_self_424_);
    return v_res_425_;
}
pub unsafe fn l_Std_instCoeOutMutexBaseMutex(
    mut v_00_u03b1_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_428_: *mut LeanObject = core::ptr::null_mut();
    v___f_428_ = l_Std_instCoeOutMutexBaseMutex___closed__0;
    return v___f_428_;
}
pub unsafe fn l_Std_Mutex_new___redArg(mut v_a_429_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_st_mk_ref(v_a_429_);
    v___x_432_ = lean_io_basemutex_new();
    v___x_433_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_433_, 0, v___x_431_);
    lean_ctor_set(v___x_433_, 1, v___x_432_);
    return v___x_433_;
}
pub unsafe fn l_Std_Mutex_new___redArg___boxed(
    mut v_a_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Mutex_new___redArg(v_a_434_);
    return v_res_436_;
}
pub unsafe fn l_Std_Mutex_new(
    mut v_00_u03b1_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Std_Mutex_new___redArg(v_a_438_);
    return v___x_440_;
}
pub unsafe fn l_Std_Mutex_new___boxed(
    mut v_00_u03b1_441_: *mut LeanObject,
    mut v_a_442_: *mut LeanObject,
    mut v_a_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_444_: *mut LeanObject = core::ptr::null_mut();
    v_res_444_ = l_Std_Mutex_new(v_00_u03b1_441_, v_a_442_);
    return v_res_444_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__0(
    mut v_k_445_: *mut LeanObject,
    mut v_ref_446_: *mut LeanObject,
    mut v_____r_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = lean_apply_1(v_k_445_, v_ref_446_);
    return v___x_448_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__1(
    mut v_x_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_450_: *mut LeanObject = core::ptr::null_mut();
    v_fst_450_ = lean_ctor_get(v_x_449_, 0);
    lean_inc(v_fst_450_);
    return v_fst_450_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__1___boxed(
    mut v_x_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_452_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_451_);
    lean_dec_ref(v_x_451_);
    return v_res_452_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__2(
    mut v___x_453_: *mut LeanObject,
    mut v_x_454_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_453_);
    return v___x_453_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg___lam__2___boxed(
    mut v___x_455_: *mut LeanObject,
    mut v_x_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_457_: *mut LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_455_, v_x_456_);
    lean_dec(v_x_456_);
    lean_dec(v___x_455_);
    return v_res_457_;
}
pub unsafe fn l_Std_Mutex_atomically___redArg(
    mut v_inst_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_inst_461_: *mut LeanObject,
    mut v_mutex_462_: *mut LeanObject,
    mut v_k_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_464_ = lean_ctor_get(v_inst_459_, 0);
    v_toFunctor_465_ = lean_ctor_get(v_toApplicative_464_, 0);
    lean_inc_ref(v_toFunctor_465_);
    v_toBind_466_ = lean_ctor_get(v_inst_459_, 1);
    lean_inc(v_toBind_466_);
    lean_dec_ref(v_inst_459_);
    v_ref_467_ = lean_ctor_get(v_mutex_462_, 0);
    lean_inc(v_ref_467_);
    v_mutex_468_ = lean_ctor_get(v_mutex_462_, 1);
    lean_inc_n(v_mutex_468_, 2);
    lean_dec_ref(v_mutex_462_);
    v_map_469_ = lean_ctor_get(v_toFunctor_465_, 0);
    lean_inc(v_map_469_);
    lean_dec_ref(v_toFunctor_465_);
    v___x_470_ = lean_alloc_closure(l_Std_BaseMutex_lock___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_470_, 0, v_mutex_468_);
    lean_inc(v_inst_460_);
    v___x_471_ = lean_apply_2(v_inst_460_, lean_box(0), v___x_470_);
    v___f_472_ = lean_alloc_closure(
        l_Std_Mutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_472_, 0, v_k_463_);
    lean_closure_set(v___f_472_, 1, v_ref_467_);
    v___f_473_ = l_Std_Mutex_atomically___redArg___closed__0;
    v___x_474_ = lean_apply_4(
        v_toBind_466_,
        lean_box(0),
        lean_box(0),
        v___x_471_,
        v___f_472_,
    );
    v___x_475_ = lean_alloc_closure(
        l_Std_BaseMutex_unlock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_475_, 0, v_mutex_468_);
    v___x_476_ = lean_apply_2(v_inst_460_, lean_box(0), v___x_475_);
    v___f_477_ = lean_alloc_closure(
        l_Std_Mutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_477_, 0, v___x_476_);
    v_y_478_ = lean_apply_4(
        v_inst_461_,
        lean_box(0),
        lean_box(0),
        v___x_474_,
        v___f_477_,
    );
    v___x_479_ = lean_apply_4(v_map_469_, lean_box(0), lean_box(0), v___f_473_, v_y_478_);
    return v___x_479_;
}
pub unsafe fn l_Std_Mutex_atomically(
    mut v_m_480_: *mut LeanObject,
    mut v_00_u03b1_481_: *mut LeanObject,
    mut v_00_u03b2_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
    mut v_inst_484_: *mut LeanObject,
    mut v_inst_485_: *mut LeanObject,
    mut v_mutex_486_: *mut LeanObject,
    mut v_k_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_490_: *mut LeanObject = core::ptr::null_mut();
    v_fst_490_ = lean_ctor_get(v_x_489_, 0);
    lean_inc(v_fst_490_);
    return v_fst_490_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_492_: *mut LeanObject = core::ptr::null_mut();
    v_res_492_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_491_);
    lean_dec_ref(v_x_491_);
    return v_res_492_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__1(
    mut v_val_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_494_, 0, v_val_493_);
    return v___x_494_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__2(
    mut v___x_495_: *mut LeanObject,
    mut v_x_496_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_495_);
    return v___x_495_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_497_: *mut LeanObject,
    mut v_x_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_497_, v_x_498_);
    lean_dec(v_x_498_);
    lean_dec(v___x_497_);
    return v_res_499_;
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_500_: *mut LeanObject,
    mut v_k_501_: *mut LeanObject,
    mut v_ref_502_: *mut LeanObject,
    mut v___f_503_: *mut LeanObject,
    mut v_mutex_504_: *mut LeanObject,
    mut v_inst_505_: *mut LeanObject,
    mut v_inst_506_: *mut LeanObject,
    mut v___f_507_: *mut LeanObject,
    mut v_____do__lift_508_: u8,
) -> *mut LeanObject {
    if v_____do__lift_508_ == 0 {
        let mut v_toPure_509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_507_);
        lean_dec(v_inst_506_);
        lean_dec(v_inst_505_);
        lean_dec(v_mutex_504_);
        lean_dec_ref(v___f_503_);
        lean_dec(v_ref_502_);
        lean_dec(v_k_501_);
        v_toPure_509_ = lean_ctor_get(v_toApplicative_500_, 1);
        lean_inc(v_toPure_509_);
        lean_dec_ref(v_toApplicative_500_);
        v___x_510_ = lean_box(0);
        v___x_511_ = lean_apply_2(v_toPure_509_, lean_box(0), v___x_510_);
        return v___x_511_;
    } else {
        let mut v_toFunctor_512_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_518_: *mut LeanObject = core::ptr::null_mut();
        let mut v_y_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_512_ = lean_ctor_get(v_toApplicative_500_, 0);
        lean_inc_ref(v_toFunctor_512_);
        lean_dec_ref(v_toApplicative_500_);
        v_map_513_ = lean_ctor_get(v_toFunctor_512_, 0);
        lean_inc_n(v_map_513_, 2);
        lean_dec_ref(v_toFunctor_512_);
        v___x_514_ = lean_apply_1(v_k_501_, v_ref_502_);
        v___x_515_ = lean_apply_4(v_map_513_, lean_box(0), lean_box(0), v___f_503_, v___x_514_);
        v___x_516_ = lean_alloc_closure(
            l_Std_BaseMutex_unlock___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___x_516_, 0, v_mutex_504_);
        v___x_517_ = lean_apply_2(v_inst_505_, lean_box(0), v___x_516_);
        v___f_518_ = lean_alloc_closure(
            l_Std_Mutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_518_, 0, v___x_517_);
        v_y_519_ = lean_apply_4(
            v_inst_506_,
            lean_box(0),
            lean_box(0),
            v___x_515_,
            v___f_518_,
        );
        v___x_520_ = lean_apply_4(v_map_513_, lean_box(0), lean_box(0), v___f_507_, v_y_519_);
        return v___x_520_;
    }
}
pub unsafe fn l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_521_: *mut LeanObject,
    mut v_k_522_: *mut LeanObject,
    mut v_ref_523_: *mut LeanObject,
    mut v___f_524_: *mut LeanObject,
    mut v_mutex_525_: *mut LeanObject,
    mut v_inst_526_: *mut LeanObject,
    mut v_inst_527_: *mut LeanObject,
    mut v___f_528_: *mut LeanObject,
    mut v_____do__lift_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_140__boxed_530_: u8 = 0;
    let mut v_res_531_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_530_ = (lean_unbox(v_____do__lift_529_) as u8);
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
    mut v_inst_534_: *mut LeanObject,
    mut v_inst_535_: *mut LeanObject,
    mut v_inst_536_: *mut LeanObject,
    mut v_mutex_537_: *mut LeanObject,
    mut v_k_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_539_ = lean_ctor_get(v_inst_534_, 0);
    lean_inc_ref(v_toApplicative_539_);
    v_toBind_540_ = lean_ctor_get(v_inst_534_, 1);
    lean_inc(v_toBind_540_);
    lean_dec_ref(v_inst_534_);
    v_ref_541_ = lean_ctor_get(v_mutex_537_, 0);
    lean_inc(v_ref_541_);
    v_mutex_542_ = lean_ctor_get(v_mutex_537_, 1);
    lean_inc_n(v_mutex_542_, 2);
    lean_dec_ref(v_mutex_537_);
    v___f_543_ = l_Std_Mutex_tryAtomically___redArg___closed__0;
    v___f_544_ = l_Std_Mutex_tryAtomically___redArg___closed__1;
    lean_inc(v_inst_535_);
    v___f_545_ = lean_alloc_closure(
        l_Std_Mutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_545_, 0, v_toApplicative_539_);
    lean_closure_set(v___f_545_, 1, v_k_538_);
    lean_closure_set(v___f_545_, 2, v_ref_541_);
    lean_closure_set(v___f_545_, 3, v___f_544_);
    lean_closure_set(v___f_545_, 4, v_mutex_542_);
    lean_closure_set(v___f_545_, 5, v_inst_535_);
    lean_closure_set(v___f_545_, 6, v_inst_536_);
    lean_closure_set(v___f_545_, 7, v___f_543_);
    v___x_546_ = lean_alloc_closure(
        l_Std_BaseMutex_tryLock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_546_, 0, v_mutex_542_);
    v___x_547_ = lean_apply_2(v_inst_535_, lean_box(0), v___x_546_);
    v___x_548_ = lean_apply_4(
        v_toBind_540_,
        lean_box(0),
        lean_box(0),
        v___x_547_,
        v___f_545_,
    );
    return v___x_548_;
}
pub unsafe fn l_Std_Mutex_tryAtomically(
    mut v_m_549_: *mut LeanObject,
    mut v_00_u03b1_550_: *mut LeanObject,
    mut v_00_u03b2_551_: *mut LeanObject,
    mut v_inst_552_: *mut LeanObject,
    mut v_inst_553_: *mut LeanObject,
    mut v_inst_554_: *mut LeanObject,
    mut v_mutex_555_: *mut LeanObject,
    mut v_k_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_k_558_: *mut LeanObject,
    mut v_____r_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_560_);
    v___x_561_ = lean_apply_1(v_k_558_, v___y_560_);
    return v___x_561_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(
    mut v_k_562_: *mut LeanObject,
    mut v_____r_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Std_Mutex_atomicallyOnce___redArg___lam__0(v_k_562_, v_____r_563_, v___y_564_);
    lean_dec(v___y_564_);
    return v_res_565_;
}
pub unsafe fn l_Std_Mutex_atomicallyOnce___redArg(
    mut v_inst_568_: *mut LeanObject,
    mut v_inst_569_: *mut LeanObject,
    mut v_inst_570_: *mut LeanObject,
    mut v_mutex_571_: *mut LeanObject,
    mut v_condvar_572_: *mut LeanObject,
    mut v_pred_573_: *mut LeanObject,
    mut v_k_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_568_, 2);
    v___x_575_ = l_StateRefT_x27_instMonad___redArg(v_inst_568_);
    v_mutex_576_ = lean_ctor_get(v_mutex_571_, 1);
    v___f_577_ = lean_alloc_closure(
        l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_577_, 0, v_k_574_);
    v___f_578_ = l_Std_Mutex_atomicallyOnce___redArg___closed__0;
    v___x_579_ = l_Std_Mutex_atomicallyOnce___redArg___closed__1;
    lean_inc(v_inst_569_);
    v___f_580_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_580_, 0, v_inst_569_);
    lean_closure_set(v___f_580_, 1, v___x_579_);
    v_x_581_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v_x_581_, 0, lean_box(0));
    lean_closure_set(v_x_581_, 1, lean_box(0));
    lean_closure_set(v_x_581_, 2, v___f_580_);
    v___f_582_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_582_, 0, v___f_578_);
    lean_closure_set(v___f_582_, 1, v_x_581_);
    lean_inc(v_mutex_576_);
    v___x_583_ = l_Std_Condvar_waitUntil___redArg(
        v___x_575_,
        v___f_582_,
        v_condvar_572_,
        v_mutex_576_,
        v_pred_573_,
    );
    v___x_584_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_584_, 0, lean_box(0));
    lean_closure_set(v___x_584_, 1, lean_box(0));
    lean_closure_set(v___x_584_, 2, lean_box(0));
    lean_closure_set(v___x_584_, 3, v_inst_568_);
    lean_closure_set(v___x_584_, 4, lean_box(0));
    lean_closure_set(v___x_584_, 5, lean_box(0));
    lean_closure_set(v___x_584_, 6, v___x_583_);
    lean_closure_set(v___x_584_, 7, v___f_577_);
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
    mut v_m_586_: *mut LeanObject,
    mut v_00_u03b1_587_: *mut LeanObject,
    mut v_00_u03b2_588_: *mut LeanObject,
    mut v_inst_589_: *mut LeanObject,
    mut v_inst_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
    mut v_mutex_592_: *mut LeanObject,
    mut v_condvar_593_: *mut LeanObject,
    mut v_pred_594_: *mut LeanObject,
    mut v_k_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Std_Sync_Mutex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl =
        _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl();
    l___private_Std_Sync_Mutex_0__Std_CondvarImpl =
        _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Mutex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Mutex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_Mutex(builtin);
}
