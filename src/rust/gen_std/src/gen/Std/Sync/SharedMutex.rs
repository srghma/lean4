// Lean compiler output
// Module: Std.Sync.SharedMutex
// Imports: Std.Sync.Basic
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get};
use crate::ffi::{
    lean_io_basesharedmutex_new, lean_io_basesharedmutex_read, lean_io_basesharedmutex_try_read,
    lean_io_basesharedmutex_try_write, lean_io_basesharedmutex_unlock_read,
    lean_io_basesharedmutex_unlock_write, lean_io_basesharedmutex_write,
};
pub static mut l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value:
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
    m_fun: l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_SharedMutex_atomically___redArg___closed__0_value:
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
    m_fun: l_Std_SharedMutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_atomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_atomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__0_value:
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
    m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__1_value:
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
    m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl()
-> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = crate::leanh::lean_box(0);
    return v___x_287_;
}
pub unsafe fn l_Std_BaseSharedMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_290_ = lean_io_basesharedmutex_new();
    return v_res_290_;
}
pub unsafe fn l_Std_BaseSharedMutex_write___boxed(
    mut v_mutex_293_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = lean_io_basesharedmutex_write(v_mutex_293_);
    crate::leanh::lean_dec(v_mutex_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryWrite___boxed(
    mut v_mutex_298_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: u8 = 0;
    let mut v_r_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = lean_io_basesharedmutex_try_write(v_mutex_298_);
    crate::leanh::lean_dec(v_mutex_298_);
    v_r_301_ = crate::leanh::lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockWrite___boxed(
    mut v_mutex_304_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = lean_io_basesharedmutex_unlock_write(v_mutex_304_);
    crate::leanh::lean_dec(v_mutex_304_);
    return v_res_306_;
}
pub unsafe fn l_Std_BaseSharedMutex_read___boxed(
    mut v_mutex_309_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = lean_io_basesharedmutex_read(v_mutex_309_);
    crate::leanh::lean_dec(v_mutex_309_);
    return v_res_311_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryRead___boxed(
    mut v_mutex_314_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: u8 = 0;
    let mut v_r_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = lean_io_basesharedmutex_try_read(v_mutex_314_);
    crate::leanh::lean_dec(v_mutex_314_);
    v_r_317_ = crate::leanh::lean_box((v_res_316_) as usize);
    return v_r_317_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockRead___boxed(
    mut v_mutex_320_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_io_basesharedmutex_unlock_read(v_mutex_320_);
    crate::leanh::lean_dec(v_mutex_320_);
    return v_res_322_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(
    mut v_self_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mutex_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mutex_324_ = crate::leanh::lean_ctor_get(v_self_323_, 1);
    crate::leanh::lean_inc(v_mutex_324_);
    return v_mutex_324_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed(
    mut v_self_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(v_self_325_);
    crate::leanh::lean_dec_ref(v_self_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex(
    mut v_00_u03b1_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_329_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0;
    return v___f_329_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg(
    mut v_a_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_st_mk_ref(v_a_330_);
    v___x_333_ = lean_io_basesharedmutex_new();
    v___x_334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_334_, 0, v___x_332_);
    crate::leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg___boxed(
    mut v_a_335_: *mut crate::leanh::LeanObject,
    mut v_a_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Std_SharedMutex_new___redArg(v_a_335_);
    return v_res_337_;
}
pub unsafe fn l_Std_SharedMutex_new(
    mut v_00_u03b1_338_: *mut crate::leanh::LeanObject,
    mut v_a_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = l_Std_SharedMutex_new___redArg(v_a_339_);
    return v___x_341_;
}
pub unsafe fn l_Std_SharedMutex_new___boxed(
    mut v_00_u03b1_342_: *mut crate::leanh::LeanObject,
    mut v_a_343_: *mut crate::leanh::LeanObject,
    mut v_a_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Std_SharedMutex_new(v_00_u03b1_342_, v_a_343_);
    return v_res_345_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__0(
    mut v_k_346_: *mut crate::leanh::LeanObject,
    mut v_ref_347_: *mut crate::leanh::LeanObject,
    mut v_____r_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = crate::leanh::lean_apply_1(v_k_346_, v_ref_347_);
    return v___x_349_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1(
    mut v_x_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_351_ = crate::leanh::lean_ctor_get(v_x_350_, 0);
    crate::leanh::lean_inc(v_fst_351_);
    return v_fst_351_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1___boxed(
    mut v_x_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_352_);
    crate::leanh::lean_dec_ref(v_x_352_);
    return v_res_353_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2(
    mut v___x_354_: *mut crate::leanh::LeanObject,
    mut v_x_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_354_);
    return v___x_354_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2___boxed(
    mut v___x_356_: *mut crate::leanh::LeanObject,
    mut v_x_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_356_, v_x_357_);
    crate::leanh::lean_dec(v_x_357_);
    crate::leanh::lean_dec(v___x_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg(
    mut v_inst_360_: *mut crate::leanh::LeanObject,
    mut v_inst_361_: *mut crate::leanh::LeanObject,
    mut v_inst_362_: *mut crate::leanh::LeanObject,
    mut v_mutex_363_: *mut crate::leanh::LeanObject,
    mut v_k_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_365_ = crate::leanh::lean_ctor_get(v_inst_360_, 0);
    v_toFunctor_366_ = crate::leanh::lean_ctor_get(v_toApplicative_365_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_366_);
    v_toBind_367_ = crate::leanh::lean_ctor_get(v_inst_360_, 1);
    crate::leanh::lean_inc(v_toBind_367_);
    crate::leanh::lean_dec_ref(v_inst_360_);
    v_ref_368_ = crate::leanh::lean_ctor_get(v_mutex_363_, 0);
    crate::leanh::lean_inc(v_ref_368_);
    v_mutex_369_ = crate::leanh::lean_ctor_get(v_mutex_363_, 1);
    crate::leanh::lean_inc_n(v_mutex_369_, 2);
    crate::leanh::lean_dec_ref(v_mutex_363_);
    v_map_370_ = crate::leanh::lean_ctor_get(v_toFunctor_366_, 0);
    crate::leanh::lean_inc(v_map_370_);
    crate::leanh::lean_dec_ref(v_toFunctor_366_);
    v___x_371_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_write___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_371_, 0, v_mutex_369_);
    crate::leanh::lean_inc(v_inst_361_);
    v___x_372_ = crate::leanh::lean_apply_2(v_inst_361_, crate::leanh::lean_box(0), v___x_371_);
    v___f_373_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_373_, 0, v_k_364_);
    crate::leanh::lean_closure_set(v___f_373_, 1, v_ref_368_);
    v___f_374_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___x_375_ = crate::leanh::lean_apply_4(
        v_toBind_367_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_372_,
        v___f_373_,
    );
    v___x_376_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_376_, 0, v_mutex_369_);
    v___x_377_ = crate::leanh::lean_apply_2(v_inst_361_, crate::leanh::lean_box(0), v___x_376_);
    v___f_378_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_378_, 0, v___x_377_);
    v_y_379_ = crate::leanh::lean_apply_4(
        v_inst_362_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_375_,
        v___f_378_,
    );
    v___x_380_ = crate::leanh::lean_apply_4(
        v_map_370_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_374_,
        v_y_379_,
    );
    return v___x_380_;
}
pub unsafe fn l_Std_SharedMutex_atomically(
    mut v_m_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_383_: *mut crate::leanh::LeanObject,
    mut v_inst_384_: *mut crate::leanh::LeanObject,
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_mutex_387_: *mut crate::leanh::LeanObject,
    mut v_k_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Std_SharedMutex_atomically___redArg(
        v_inst_384_,
        v_inst_385_,
        v_inst_386_,
        v_mutex_387_,
        v_k_388_,
    );
    return v___x_389_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__0(
    mut v_x_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_391_ = crate::leanh::lean_ctor_get(v_x_390_, 0);
    crate::leanh::lean_inc(v_fst_391_);
    return v_fst_391_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_392_);
    crate::leanh::lean_dec_ref(v_x_392_);
    return v_res_393_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__1(
    mut v_val_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_395_, 0, v_val_394_);
    return v___x_395_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2(
    mut v___x_396_: *mut crate::leanh::LeanObject,
    mut v_x_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_396_);
    return v___x_396_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_398_: *mut crate::leanh::LeanObject,
    mut v_x_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_398_, v_x_399_);
    crate::leanh::lean_dec(v_x_399_);
    crate::leanh::lean_dec(v___x_398_);
    return v_res_400_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_401_: *mut crate::leanh::LeanObject,
    mut v_k_402_: *mut crate::leanh::LeanObject,
    mut v_ref_403_: *mut crate::leanh::LeanObject,
    mut v___f_404_: *mut crate::leanh::LeanObject,
    mut v_mutex_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v___f_408_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_409_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_409_ == 0 {
        let mut v_toPure_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_408_);
        crate::leanh::lean_dec(v_inst_407_);
        crate::leanh::lean_dec(v_inst_406_);
        crate::leanh::lean_dec(v_mutex_405_);
        crate::leanh::lean_dec_ref(v___f_404_);
        crate::leanh::lean_dec(v_ref_403_);
        crate::leanh::lean_dec(v_k_402_);
        v_toPure_410_ = crate::leanh::lean_ctor_get(v_toApplicative_401_, 1);
        crate::leanh::lean_inc(v_toPure_410_);
        crate::leanh::lean_dec_ref(v_toApplicative_401_);
        v___x_411_ = crate::leanh::lean_box(0);
        v___x_412_ =
            crate::leanh::lean_apply_2(v_toPure_410_, crate::leanh::lean_box(0), v___x_411_);
        return v___x_412_;
    } else {
        let mut v_toFunctor_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_413_ = crate::leanh::lean_ctor_get(v_toApplicative_401_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_413_);
        crate::leanh::lean_dec_ref(v_toApplicative_401_);
        v_map_414_ = crate::leanh::lean_ctor_get(v_toFunctor_413_, 0);
        crate::leanh::lean_inc_n(v_map_414_, 2);
        crate::leanh::lean_dec_ref(v_toFunctor_413_);
        v___x_415_ = crate::leanh::lean_apply_1(v_k_402_, v_ref_403_);
        v___x_416_ = crate::leanh::lean_apply_4(
            v_map_414_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_404_,
            v___x_415_,
        );
        v___x_417_ = crate::leanh::lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_417_, 0, v_mutex_405_);
        v___x_418_ = crate::leanh::lean_apply_2(v_inst_406_, crate::leanh::lean_box(0), v___x_417_);
        v___f_419_ = crate::leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_419_, 0, v___x_418_);
        v_y_420_ = crate::leanh::lean_apply_4(
            v_inst_407_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_416_,
            v___f_419_,
        );
        v___x_421_ = crate::leanh::lean_apply_4(
            v_map_414_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_408_,
            v_y_420_,
        );
        return v___x_421_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_422_: *mut crate::leanh::LeanObject,
    mut v_k_423_: *mut crate::leanh::LeanObject,
    mut v_ref_424_: *mut crate::leanh::LeanObject,
    mut v___f_425_: *mut crate::leanh::LeanObject,
    mut v_mutex_426_: *mut crate::leanh::LeanObject,
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v___f_429_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_140__boxed_431_: u8 = 0;
    let mut v_res_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_431_ = (crate::leanh::lean_unbox(v_____do__lift_430_) as u8);
    v_res_432_ = l_Std_SharedMutex_tryAtomically___redArg___lam__3(
        v_toApplicative_422_,
        v_k_423_,
        v_ref_424_,
        v___f_425_,
        v_mutex_426_,
        v_inst_427_,
        v_inst_428_,
        v___f_429_,
        v_____do__lift_140__boxed_431_,
    );
    return v_res_432_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg(
    mut v_inst_435_: *mut crate::leanh::LeanObject,
    mut v_inst_436_: *mut crate::leanh::LeanObject,
    mut v_inst_437_: *mut crate::leanh::LeanObject,
    mut v_mutex_438_: *mut crate::leanh::LeanObject,
    mut v_k_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_440_ = crate::leanh::lean_ctor_get(v_inst_435_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_440_);
    v_toBind_441_ = crate::leanh::lean_ctor_get(v_inst_435_, 1);
    crate::leanh::lean_inc(v_toBind_441_);
    crate::leanh::lean_dec_ref(v_inst_435_);
    v_ref_442_ = crate::leanh::lean_ctor_get(v_mutex_438_, 0);
    crate::leanh::lean_inc(v_ref_442_);
    v_mutex_443_ = crate::leanh::lean_ctor_get(v_mutex_438_, 1);
    crate::leanh::lean_inc_n(v_mutex_443_, 2);
    crate::leanh::lean_dec_ref(v_mutex_438_);
    v___f_444_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_445_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    crate::leanh::lean_inc(v_inst_436_);
    v___f_446_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_446_, 0, v_toApplicative_440_);
    crate::leanh::lean_closure_set(v___f_446_, 1, v_k_439_);
    crate::leanh::lean_closure_set(v___f_446_, 2, v_ref_442_);
    crate::leanh::lean_closure_set(v___f_446_, 3, v___f_445_);
    crate::leanh::lean_closure_set(v___f_446_, 4, v_mutex_443_);
    crate::leanh::lean_closure_set(v___f_446_, 5, v_inst_436_);
    crate::leanh::lean_closure_set(v___f_446_, 6, v_inst_437_);
    crate::leanh::lean_closure_set(v___f_446_, 7, v___f_444_);
    v___x_447_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_tryWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_447_, 0, v_mutex_443_);
    v___x_448_ = crate::leanh::lean_apply_2(v_inst_436_, crate::leanh::lean_box(0), v___x_447_);
    v___x_449_ = crate::leanh::lean_apply_4(
        v_toBind_441_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_448_,
        v___f_446_,
    );
    return v___x_449_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically(
    mut v_m_450_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_451_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_452_: *mut crate::leanh::LeanObject,
    mut v_inst_453_: *mut crate::leanh::LeanObject,
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_inst_455_: *mut crate::leanh::LeanObject,
    mut v_mutex_456_: *mut crate::leanh::LeanObject,
    mut v_k_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Std_SharedMutex_tryAtomically___redArg(
        v_inst_453_,
        v_inst_454_,
        v_inst_455_,
        v_mutex_456_,
        v_k_457_,
    );
    return v___x_458_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__0(
    mut v_k_459_: *mut crate::leanh::LeanObject,
    mut v_state_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_461_ = crate::leanh::lean_apply_1(v_k_459_, v_state_460_);
    return v___x_461_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2(
    mut v_ref_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_st_ref_get(v_ref_462_);
    return v___x_464_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(
    mut v_ref_465_: *mut crate::leanh::LeanObject,
    mut v___y_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_465_);
    crate::leanh::lean_dec(v_ref_465_);
    return v_res_467_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__1(
    mut v_ref_468_: *mut crate::leanh::LeanObject,
    mut v_inst_469_: *mut crate::leanh::LeanObject,
    mut v_toBind_470_: *mut crate::leanh::LeanObject,
    mut v___f_471_: *mut crate::leanh::LeanObject,
    mut v_____r_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_473_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_473_, 0, v_ref_468_);
    v___x_474_ = crate::leanh::lean_apply_2(v_inst_469_, crate::leanh::lean_box(0), v___f_473_);
    v___x_475_ = crate::leanh::lean_apply_4(
        v_toBind_470_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_474_,
        v___f_471_,
    );
    return v___x_475_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg(
    mut v_inst_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
    mut v_inst_478_: *mut crate::leanh::LeanObject,
    mut v_mutex_479_: *mut crate::leanh::LeanObject,
    mut v_k_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_481_ = crate::leanh::lean_ctor_get(v_inst_476_, 0);
    v_toFunctor_482_ = crate::leanh::lean_ctor_get(v_toApplicative_481_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_482_);
    v_toBind_483_ = crate::leanh::lean_ctor_get(v_inst_476_, 1);
    crate::leanh::lean_inc_n(v_toBind_483_, 2);
    crate::leanh::lean_dec_ref(v_inst_476_);
    v_ref_484_ = crate::leanh::lean_ctor_get(v_mutex_479_, 0);
    crate::leanh::lean_inc(v_ref_484_);
    v_mutex_485_ = crate::leanh::lean_ctor_get(v_mutex_479_, 1);
    crate::leanh::lean_inc_n(v_mutex_485_, 2);
    crate::leanh::lean_dec_ref(v_mutex_479_);
    v_map_486_ = crate::leanh::lean_ctor_get(v_toFunctor_482_, 0);
    crate::leanh::lean_inc(v_map_486_);
    crate::leanh::lean_dec_ref(v_toFunctor_482_);
    v___x_487_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_read___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_487_, 0, v_mutex_485_);
    crate::leanh::lean_inc_n(v_inst_477_, 2);
    v___x_488_ = crate::leanh::lean_apply_2(v_inst_477_, crate::leanh::lean_box(0), v___x_487_);
    v___f_489_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_489_, 0, v_k_480_);
    v___f_490_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___f_491_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_491_, 0, v_ref_484_);
    crate::leanh::lean_closure_set(v___f_491_, 1, v_inst_477_);
    crate::leanh::lean_closure_set(v___f_491_, 2, v_toBind_483_);
    crate::leanh::lean_closure_set(v___f_491_, 3, v___f_489_);
    v___x_492_ = crate::leanh::lean_apply_4(
        v_toBind_483_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_488_,
        v___f_491_,
    );
    v___x_493_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_493_, 0, v_mutex_485_);
    v___x_494_ = crate::leanh::lean_apply_2(v_inst_477_, crate::leanh::lean_box(0), v___x_493_);
    v___f_495_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_495_, 0, v___x_494_);
    v_y_496_ = crate::leanh::lean_apply_4(
        v_inst_478_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_492_,
        v___f_495_,
    );
    v___x_497_ = crate::leanh::lean_apply_4(
        v_map_486_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_490_,
        v_y_496_,
    );
    return v___x_497_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead(
    mut v_m_498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_500_: *mut crate::leanh::LeanObject,
    mut v_inst_501_: *mut crate::leanh::LeanObject,
    mut v_inst_502_: *mut crate::leanh::LeanObject,
    mut v_inst_503_: *mut crate::leanh::LeanObject,
    mut v_mutex_504_: *mut crate::leanh::LeanObject,
    mut v_k_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Std_SharedMutex_atomicallyRead___redArg(
        v_inst_501_,
        v_inst_502_,
        v_inst_503_,
        v_mutex_504_,
        v_k_505_,
    );
    return v___x_506_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(
    mut v_k_507_: *mut crate::leanh::LeanObject,
    mut v_map_508_: *mut crate::leanh::LeanObject,
    mut v___f_509_: *mut crate::leanh::LeanObject,
    mut v_state_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = crate::leanh::lean_apply_1(v_k_507_, v_state_510_);
    v___x_512_ = crate::leanh::lean_apply_4(
        v_map_508_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_509_,
        v___x_511_,
    );
    return v___x_512_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(
    mut v_toApplicative_513_: *mut crate::leanh::LeanObject,
    mut v_inst_514_: *mut crate::leanh::LeanObject,
    mut v___f_515_: *mut crate::leanh::LeanObject,
    mut v_k_516_: *mut crate::leanh::LeanObject,
    mut v___f_517_: *mut crate::leanh::LeanObject,
    mut v_toBind_518_: *mut crate::leanh::LeanObject,
    mut v_mutex_519_: *mut crate::leanh::LeanObject,
    mut v_inst_520_: *mut crate::leanh::LeanObject,
    mut v___f_521_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_522_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_522_ == 0 {
        let mut v_toPure_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_521_);
        crate::leanh::lean_dec(v_inst_520_);
        crate::leanh::lean_dec(v_mutex_519_);
        crate::leanh::lean_dec(v_toBind_518_);
        crate::leanh::lean_dec_ref(v___f_517_);
        crate::leanh::lean_dec(v_k_516_);
        crate::leanh::lean_dec_ref(v___f_515_);
        crate::leanh::lean_dec(v_inst_514_);
        v_toPure_523_ = crate::leanh::lean_ctor_get(v_toApplicative_513_, 1);
        crate::leanh::lean_inc(v_toPure_523_);
        crate::leanh::lean_dec_ref(v_toApplicative_513_);
        v___x_524_ = crate::leanh::lean_box(0);
        v___x_525_ =
            crate::leanh::lean_apply_2(v_toPure_523_, crate::leanh::lean_box(0), v___x_524_);
        return v___x_525_;
    } else {
        let mut v_toFunctor_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_526_ = crate::leanh::lean_ctor_get(v_toApplicative_513_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_526_);
        crate::leanh::lean_dec_ref(v_toApplicative_513_);
        v_map_527_ = crate::leanh::lean_ctor_get(v_toFunctor_526_, 0);
        crate::leanh::lean_inc_n(v_map_527_, 2);
        crate::leanh::lean_dec_ref(v_toFunctor_526_);
        crate::leanh::lean_inc(v_inst_514_);
        v___x_528_ = crate::leanh::lean_apply_2(v_inst_514_, crate::leanh::lean_box(0), v___f_515_);
        v___f_529_ = crate::leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_529_, 0, v_k_516_);
        crate::leanh::lean_closure_set(v___f_529_, 1, v_map_527_);
        crate::leanh::lean_closure_set(v___f_529_, 2, v___f_517_);
        v___x_530_ = crate::leanh::lean_apply_4(
            v_toBind_518_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_528_,
            v___f_529_,
        );
        v___x_531_ = crate::leanh::lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_531_, 0, v_mutex_519_);
        v___x_532_ = crate::leanh::lean_apply_2(v_inst_514_, crate::leanh::lean_box(0), v___x_531_);
        v___f_533_ = crate::leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_533_, 0, v___x_532_);
        v_y_534_ = crate::leanh::lean_apply_4(
            v_inst_520_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_530_,
            v___f_533_,
        );
        v___x_535_ = crate::leanh::lean_apply_4(
            v_map_527_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_521_,
            v_y_534_,
        );
        return v___x_535_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(
    mut v_toApplicative_536_: *mut crate::leanh::LeanObject,
    mut v_inst_537_: *mut crate::leanh::LeanObject,
    mut v___f_538_: *mut crate::leanh::LeanObject,
    mut v_k_539_: *mut crate::leanh::LeanObject,
    mut v___f_540_: *mut crate::leanh::LeanObject,
    mut v_toBind_541_: *mut crate::leanh::LeanObject,
    mut v_mutex_542_: *mut crate::leanh::LeanObject,
    mut v_inst_543_: *mut crate::leanh::LeanObject,
    mut v___f_544_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_191__boxed_546_: u8 = 0;
    let mut v_res_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_546_ = (crate::leanh::lean_unbox(v_____do__lift_545_) as u8);
    v_res_547_ = l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(
        v_toApplicative_536_,
        v_inst_537_,
        v___f_538_,
        v_k_539_,
        v___f_540_,
        v_toBind_541_,
        v_mutex_542_,
        v_inst_543_,
        v___f_544_,
        v_____do__lift_191__boxed_546_,
    );
    return v_res_547_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg(
    mut v_inst_548_: *mut crate::leanh::LeanObject,
    mut v_inst_549_: *mut crate::leanh::LeanObject,
    mut v_inst_550_: *mut crate::leanh::LeanObject,
    mut v_mutex_551_: *mut crate::leanh::LeanObject,
    mut v_k_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_553_ = crate::leanh::lean_ctor_get(v_inst_548_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_553_);
    v_toBind_554_ = crate::leanh::lean_ctor_get(v_inst_548_, 1);
    crate::leanh::lean_inc_n(v_toBind_554_, 2);
    crate::leanh::lean_dec_ref(v_inst_548_);
    v_ref_555_ = crate::leanh::lean_ctor_get(v_mutex_551_, 0);
    crate::leanh::lean_inc(v_ref_555_);
    v_mutex_556_ = crate::leanh::lean_ctor_get(v_mutex_551_, 1);
    crate::leanh::lean_inc_n(v_mutex_556_, 2);
    crate::leanh::lean_dec_ref(v_mutex_551_);
    v___f_557_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    v___f_558_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_559_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_559_, 0, v_ref_555_);
    crate::leanh::lean_inc(v_inst_549_);
    v___f_560_ = crate::leanh::lean_alloc_closure(
        l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_560_, 0, v_toApplicative_553_);
    crate::leanh::lean_closure_set(v___f_560_, 1, v_inst_549_);
    crate::leanh::lean_closure_set(v___f_560_, 2, v___f_559_);
    crate::leanh::lean_closure_set(v___f_560_, 3, v_k_552_);
    crate::leanh::lean_closure_set(v___f_560_, 4, v___f_557_);
    crate::leanh::lean_closure_set(v___f_560_, 5, v_toBind_554_);
    crate::leanh::lean_closure_set(v___f_560_, 6, v_mutex_556_);
    crate::leanh::lean_closure_set(v___f_560_, 7, v_inst_550_);
    crate::leanh::lean_closure_set(v___f_560_, 8, v___f_558_);
    v___x_561_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_tryRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_561_, 0, v_mutex_556_);
    v___x_562_ = crate::leanh::lean_apply_2(v_inst_549_, crate::leanh::lean_box(0), v___x_561_);
    v___x_563_ = crate::leanh::lean_apply_4(
        v_toBind_554_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_562_,
        v___f_560_,
    );
    return v___x_563_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead(
    mut v_m_564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_565_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_inst_569_: *mut crate::leanh::LeanObject,
    mut v_mutex_570_: *mut crate::leanh::LeanObject,
    mut v_k_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Std_SharedMutex_tryAtomicallyRead___redArg(
        v_inst_567_,
        v_inst_568_,
        v_inst_569_,
        v_mutex_570_,
        v_k_571_,
    );
    return v___x_572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_SharedMutex(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl =
        _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Sync_SharedMutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_SharedMutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_SharedMutex(builtin);
}
