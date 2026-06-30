// Lean compiler output
// Module: Std.Sync.SharedMutex
// Imports: Std.Sync.Basic
use crate::ffi::{
    lean_io_basesharedmutex_new, lean_io_basesharedmutex_read, lean_io_basesharedmutex_try_read,
    lean_io_basesharedmutex_try_write, lean_io_basesharedmutex_unlock_read,
    lean_io_basesharedmutex_unlock_write, lean_io_basesharedmutex_write, lean_st_mk_ref,
    lean_st_ref_get,
};
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
pub static mut l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value:
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
    m_fun: l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_SharedMutex_atomically___redArg___closed__0_value:
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
    m_fun: l_Std_SharedMutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_atomically___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_atomically___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__0_value:
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
    m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__1_value:
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
    m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl()
-> *mut leanh::LeanObject {
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = leanh::lean_box(0);
    return v___x_287_;
}
pub unsafe fn l_Std_BaseSharedMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_290_ = lean_io_basesharedmutex_new();
    return v_res_290_;
}
pub unsafe fn l_Std_BaseSharedMutex_write___boxed(
    mut v_mutex_293_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = lean_io_basesharedmutex_write(v_mutex_293_);
    leanh::lean_dec(v_mutex_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryWrite___boxed(
    mut v_mutex_298_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_300_: u8 = 0;
    let mut v_r_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = lean_io_basesharedmutex_try_write(v_mutex_298_);
    leanh::lean_dec(v_mutex_298_);
    v_r_301_ = leanh::lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockWrite___boxed(
    mut v_mutex_304_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = lean_io_basesharedmutex_unlock_write(v_mutex_304_);
    leanh::lean_dec(v_mutex_304_);
    return v_res_306_;
}
pub unsafe fn l_Std_BaseSharedMutex_read___boxed(
    mut v_mutex_309_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = lean_io_basesharedmutex_read(v_mutex_309_);
    leanh::lean_dec(v_mutex_309_);
    return v_res_311_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryRead___boxed(
    mut v_mutex_314_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_316_: u8 = 0;
    let mut v_r_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = lean_io_basesharedmutex_try_read(v_mutex_314_);
    leanh::lean_dec(v_mutex_314_);
    v_r_317_ = leanh::lean_box((v_res_316_) as usize);
    return v_r_317_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockRead___boxed(
    mut v_mutex_320_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_io_basesharedmutex_unlock_read(v_mutex_320_);
    leanh::lean_dec(v_mutex_320_);
    return v_res_322_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(
    mut v_self_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mutex_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mutex_324_ = leanh::lean_ctor_get(v_self_323_, 1);
    leanh::lean_inc(v_mutex_324_);
    return v_mutex_324_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed(
    mut v_self_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(v_self_325_);
    leanh::lean_dec_ref(v_self_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex(
    mut v_00_u03b1_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_329_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0;
    return v___f_329_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg(
    mut v_a_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_st_mk_ref(v_a_330_);
    v___x_333_ = lean_io_basesharedmutex_new();
    v___x_334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_334_, 0, v___x_332_);
    leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg___boxed(
    mut v_a_335_: *mut leanh::LeanObject,
    mut v_a_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Std_SharedMutex_new___redArg(v_a_335_);
    return v_res_337_;
}
pub unsafe fn l_Std_SharedMutex_new(
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_a_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = l_Std_SharedMutex_new___redArg(v_a_339_);
    return v___x_341_;
}
pub unsafe fn l_Std_SharedMutex_new___boxed(
    mut v_00_u03b1_342_: *mut leanh::LeanObject,
    mut v_a_343_: *mut leanh::LeanObject,
    mut v_a_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Std_SharedMutex_new(v_00_u03b1_342_, v_a_343_);
    return v_res_345_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__0(
    mut v_k_346_: *mut leanh::LeanObject,
    mut v_ref_347_: *mut leanh::LeanObject,
    mut v_____r_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = leanh::lean_apply_1(v_k_346_, v_ref_347_);
    return v___x_349_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1(
    mut v_x_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_351_ = leanh::lean_ctor_get(v_x_350_, 0);
    leanh::lean_inc(v_fst_351_);
    return v_fst_351_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1___boxed(
    mut v_x_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_352_);
    leanh::lean_dec_ref(v_x_352_);
    return v_res_353_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2(
    mut v___x_354_: *mut leanh::LeanObject,
    mut v_x_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_354_);
    return v___x_354_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2___boxed(
    mut v___x_356_: *mut leanh::LeanObject,
    mut v_x_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_356_, v_x_357_);
    leanh::lean_dec(v_x_357_);
    leanh::lean_dec(v___x_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg(
    mut v_inst_360_: *mut leanh::LeanObject,
    mut v_inst_361_: *mut leanh::LeanObject,
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_mutex_363_: *mut leanh::LeanObject,
    mut v_k_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_365_ = leanh::lean_ctor_get(v_inst_360_, 0);
    v_toFunctor_366_ = leanh::lean_ctor_get(v_toApplicative_365_, 0);
    leanh::lean_inc_ref(v_toFunctor_366_);
    v_toBind_367_ = leanh::lean_ctor_get(v_inst_360_, 1);
    leanh::lean_inc(v_toBind_367_);
    leanh::lean_dec_ref(v_inst_360_);
    v_ref_368_ = leanh::lean_ctor_get(v_mutex_363_, 0);
    leanh::lean_inc(v_ref_368_);
    v_mutex_369_ = leanh::lean_ctor_get(v_mutex_363_, 1);
    leanh::lean_inc_n(v_mutex_369_, 2);
    leanh::lean_dec_ref(v_mutex_363_);
    v_map_370_ = leanh::lean_ctor_get(v_toFunctor_366_, 0);
    leanh::lean_inc(v_map_370_);
    leanh::lean_dec_ref(v_toFunctor_366_);
    v___x_371_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_write___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_371_, 0, v_mutex_369_);
    leanh::lean_inc(v_inst_361_);
    v___x_372_ = leanh::lean_apply_2(v_inst_361_, leanh::lean_box(0), v___x_371_);
    v___f_373_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_373_, 0, v_k_364_);
    leanh::lean_closure_set(v___f_373_, 1, v_ref_368_);
    v___f_374_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___x_375_ = leanh::lean_apply_4(
        v_toBind_367_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_372_,
        v___f_373_,
    );
    v___x_376_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_376_, 0, v_mutex_369_);
    v___x_377_ = leanh::lean_apply_2(v_inst_361_, leanh::lean_box(0), v___x_376_);
    v___f_378_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_378_, 0, v___x_377_);
    v_y_379_ = leanh::lean_apply_4(
        v_inst_362_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_375_,
        v___f_378_,
    );
    v___x_380_ = leanh::lean_apply_4(
        v_map_370_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_374_,
        v_y_379_,
    );
    return v___x_380_;
}
pub unsafe fn l_Std_SharedMutex_atomically(
    mut v_m_381_: *mut leanh::LeanObject,
    mut v_00_u03b1_382_: *mut leanh::LeanObject,
    mut v_00_u03b2_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_mutex_387_: *mut leanh::LeanObject,
    mut v_k_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_391_ = leanh::lean_ctor_get(v_x_390_, 0);
    leanh::lean_inc(v_fst_391_);
    return v_fst_391_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_392_);
    leanh::lean_dec_ref(v_x_392_);
    return v_res_393_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__1(
    mut v_val_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_395_, 0, v_val_394_);
    return v___x_395_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2(
    mut v___x_396_: *mut leanh::LeanObject,
    mut v_x_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_396_);
    return v___x_396_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_398_: *mut leanh::LeanObject,
    mut v_x_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_398_, v_x_399_);
    leanh::lean_dec(v_x_399_);
    leanh::lean_dec(v___x_398_);
    return v_res_400_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_401_: *mut leanh::LeanObject,
    mut v_k_402_: *mut leanh::LeanObject,
    mut v_ref_403_: *mut leanh::LeanObject,
    mut v___f_404_: *mut leanh::LeanObject,
    mut v_mutex_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v___f_408_: *mut leanh::LeanObject,
    mut v_____do__lift_409_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_409_ == 0 {
        let mut v_toPure_410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_408_);
        leanh::lean_dec(v_inst_407_);
        leanh::lean_dec(v_inst_406_);
        leanh::lean_dec(v_mutex_405_);
        leanh::lean_dec_ref(v___f_404_);
        leanh::lean_dec(v_ref_403_);
        leanh::lean_dec(v_k_402_);
        v_toPure_410_ = leanh::lean_ctor_get(v_toApplicative_401_, 1);
        leanh::lean_inc(v_toPure_410_);
        leanh::lean_dec_ref(v_toApplicative_401_);
        v___x_411_ = leanh::lean_box(0);
        v___x_412_ =
            leanh::lean_apply_2(v_toPure_410_, leanh::lean_box(0), v___x_411_);
        return v___x_412_;
    } else {
        let mut v_toFunctor_413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_413_ = leanh::lean_ctor_get(v_toApplicative_401_, 0);
        leanh::lean_inc_ref(v_toFunctor_413_);
        leanh::lean_dec_ref(v_toApplicative_401_);
        v_map_414_ = leanh::lean_ctor_get(v_toFunctor_413_, 0);
        leanh::lean_inc_n(v_map_414_, 2);
        leanh::lean_dec_ref(v_toFunctor_413_);
        v___x_415_ = leanh::lean_apply_1(v_k_402_, v_ref_403_);
        v___x_416_ = leanh::lean_apply_4(
            v_map_414_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_404_,
            v___x_415_,
        );
        v___x_417_ = leanh::lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___x_417_, 0, v_mutex_405_);
        v___x_418_ = leanh::lean_apply_2(v_inst_406_, leanh::lean_box(0), v___x_417_);
        v___f_419_ = leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_419_, 0, v___x_418_);
        v_y_420_ = leanh::lean_apply_4(
            v_inst_407_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_416_,
            v___f_419_,
        );
        v___x_421_ = leanh::lean_apply_4(
            v_map_414_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_408_,
            v_y_420_,
        );
        return v___x_421_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_422_: *mut leanh::LeanObject,
    mut v_k_423_: *mut leanh::LeanObject,
    mut v_ref_424_: *mut leanh::LeanObject,
    mut v___f_425_: *mut leanh::LeanObject,
    mut v_mutex_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_inst_428_: *mut leanh::LeanObject,
    mut v___f_429_: *mut leanh::LeanObject,
    mut v_____do__lift_430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_140__boxed_431_: u8 = 0;
    let mut v_res_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_431_ = (leanh::lean_unbox(v_____do__lift_430_) as u8);
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
    mut v_inst_435_: *mut leanh::LeanObject,
    mut v_inst_436_: *mut leanh::LeanObject,
    mut v_inst_437_: *mut leanh::LeanObject,
    mut v_mutex_438_: *mut leanh::LeanObject,
    mut v_k_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_440_ = leanh::lean_ctor_get(v_inst_435_, 0);
    leanh::lean_inc_ref(v_toApplicative_440_);
    v_toBind_441_ = leanh::lean_ctor_get(v_inst_435_, 1);
    leanh::lean_inc(v_toBind_441_);
    leanh::lean_dec_ref(v_inst_435_);
    v_ref_442_ = leanh::lean_ctor_get(v_mutex_438_, 0);
    leanh::lean_inc(v_ref_442_);
    v_mutex_443_ = leanh::lean_ctor_get(v_mutex_438_, 1);
    leanh::lean_inc_n(v_mutex_443_, 2);
    leanh::lean_dec_ref(v_mutex_438_);
    v___f_444_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_445_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    leanh::lean_inc(v_inst_436_);
    v___f_446_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_446_, 0, v_toApplicative_440_);
    leanh::lean_closure_set(v___f_446_, 1, v_k_439_);
    leanh::lean_closure_set(v___f_446_, 2, v_ref_442_);
    leanh::lean_closure_set(v___f_446_, 3, v___f_445_);
    leanh::lean_closure_set(v___f_446_, 4, v_mutex_443_);
    leanh::lean_closure_set(v___f_446_, 5, v_inst_436_);
    leanh::lean_closure_set(v___f_446_, 6, v_inst_437_);
    leanh::lean_closure_set(v___f_446_, 7, v___f_444_);
    v___x_447_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_tryWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_447_, 0, v_mutex_443_);
    v___x_448_ = leanh::lean_apply_2(v_inst_436_, leanh::lean_box(0), v___x_447_);
    v___x_449_ = leanh::lean_apply_4(
        v_toBind_441_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_448_,
        v___f_446_,
    );
    return v___x_449_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically(
    mut v_m_450_: *mut leanh::LeanObject,
    mut v_00_u03b1_451_: *mut leanh::LeanObject,
    mut v_00_u03b2_452_: *mut leanh::LeanObject,
    mut v_inst_453_: *mut leanh::LeanObject,
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_inst_455_: *mut leanh::LeanObject,
    mut v_mutex_456_: *mut leanh::LeanObject,
    mut v_k_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_k_459_: *mut leanh::LeanObject,
    mut v_state_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_461_ = leanh::lean_apply_1(v_k_459_, v_state_460_);
    return v___x_461_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2(
    mut v_ref_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_st_ref_get(v_ref_462_);
    return v___x_464_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(
    mut v_ref_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_465_);
    leanh::lean_dec(v_ref_465_);
    return v_res_467_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__1(
    mut v_ref_468_: *mut leanh::LeanObject,
    mut v_inst_469_: *mut leanh::LeanObject,
    mut v_toBind_470_: *mut leanh::LeanObject,
    mut v___f_471_: *mut leanh::LeanObject,
    mut v_____r_472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_473_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_473_, 0, v_ref_468_);
    v___x_474_ = leanh::lean_apply_2(v_inst_469_, leanh::lean_box(0), v___f_473_);
    v___x_475_ = leanh::lean_apply_4(
        v_toBind_470_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_474_,
        v___f_471_,
    );
    return v___x_475_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg(
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_mutex_479_: *mut leanh::LeanObject,
    mut v_k_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_481_ = leanh::lean_ctor_get(v_inst_476_, 0);
    v_toFunctor_482_ = leanh::lean_ctor_get(v_toApplicative_481_, 0);
    leanh::lean_inc_ref(v_toFunctor_482_);
    v_toBind_483_ = leanh::lean_ctor_get(v_inst_476_, 1);
    leanh::lean_inc_n(v_toBind_483_, 2);
    leanh::lean_dec_ref(v_inst_476_);
    v_ref_484_ = leanh::lean_ctor_get(v_mutex_479_, 0);
    leanh::lean_inc(v_ref_484_);
    v_mutex_485_ = leanh::lean_ctor_get(v_mutex_479_, 1);
    leanh::lean_inc_n(v_mutex_485_, 2);
    leanh::lean_dec_ref(v_mutex_479_);
    v_map_486_ = leanh::lean_ctor_get(v_toFunctor_482_, 0);
    leanh::lean_inc(v_map_486_);
    leanh::lean_dec_ref(v_toFunctor_482_);
    v___x_487_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_read___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_487_, 0, v_mutex_485_);
    leanh::lean_inc_n(v_inst_477_, 2);
    v___x_488_ = leanh::lean_apply_2(v_inst_477_, leanh::lean_box(0), v___x_487_);
    v___f_489_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_489_, 0, v_k_480_);
    v___f_490_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___f_491_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_491_, 0, v_ref_484_);
    leanh::lean_closure_set(v___f_491_, 1, v_inst_477_);
    leanh::lean_closure_set(v___f_491_, 2, v_toBind_483_);
    leanh::lean_closure_set(v___f_491_, 3, v___f_489_);
    v___x_492_ = leanh::lean_apply_4(
        v_toBind_483_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_488_,
        v___f_491_,
    );
    v___x_493_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_493_, 0, v_mutex_485_);
    v___x_494_ = leanh::lean_apply_2(v_inst_477_, leanh::lean_box(0), v___x_493_);
    v___f_495_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_495_, 0, v___x_494_);
    v_y_496_ = leanh::lean_apply_4(
        v_inst_478_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_492_,
        v___f_495_,
    );
    v___x_497_ = leanh::lean_apply_4(
        v_map_486_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_490_,
        v_y_496_,
    );
    return v___x_497_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead(
    mut v_m_498_: *mut leanh::LeanObject,
    mut v_00_u03b1_499_: *mut leanh::LeanObject,
    mut v_00_u03b2_500_: *mut leanh::LeanObject,
    mut v_inst_501_: *mut leanh::LeanObject,
    mut v_inst_502_: *mut leanh::LeanObject,
    mut v_inst_503_: *mut leanh::LeanObject,
    mut v_mutex_504_: *mut leanh::LeanObject,
    mut v_k_505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_k_507_: *mut leanh::LeanObject,
    mut v_map_508_: *mut leanh::LeanObject,
    mut v___f_509_: *mut leanh::LeanObject,
    mut v_state_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = leanh::lean_apply_1(v_k_507_, v_state_510_);
    v___x_512_ = leanh::lean_apply_4(
        v_map_508_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_509_,
        v___x_511_,
    );
    return v___x_512_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(
    mut v_toApplicative_513_: *mut leanh::LeanObject,
    mut v_inst_514_: *mut leanh::LeanObject,
    mut v___f_515_: *mut leanh::LeanObject,
    mut v_k_516_: *mut leanh::LeanObject,
    mut v___f_517_: *mut leanh::LeanObject,
    mut v_toBind_518_: *mut leanh::LeanObject,
    mut v_mutex_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v___f_521_: *mut leanh::LeanObject,
    mut v_____do__lift_522_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_522_ == 0 {
        let mut v_toPure_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_521_);
        leanh::lean_dec(v_inst_520_);
        leanh::lean_dec(v_mutex_519_);
        leanh::lean_dec(v_toBind_518_);
        leanh::lean_dec_ref(v___f_517_);
        leanh::lean_dec(v_k_516_);
        leanh::lean_dec_ref(v___f_515_);
        leanh::lean_dec(v_inst_514_);
        v_toPure_523_ = leanh::lean_ctor_get(v_toApplicative_513_, 1);
        leanh::lean_inc(v_toPure_523_);
        leanh::lean_dec_ref(v_toApplicative_513_);
        v___x_524_ = leanh::lean_box(0);
        v___x_525_ =
            leanh::lean_apply_2(v_toPure_523_, leanh::lean_box(0), v___x_524_);
        return v___x_525_;
    } else {
        let mut v_toFunctor_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_526_ = leanh::lean_ctor_get(v_toApplicative_513_, 0);
        leanh::lean_inc_ref(v_toFunctor_526_);
        leanh::lean_dec_ref(v_toApplicative_513_);
        v_map_527_ = leanh::lean_ctor_get(v_toFunctor_526_, 0);
        leanh::lean_inc_n(v_map_527_, 2);
        leanh::lean_dec_ref(v_toFunctor_526_);
        leanh::lean_inc(v_inst_514_);
        v___x_528_ = leanh::lean_apply_2(v_inst_514_, leanh::lean_box(0), v___f_515_);
        v___f_529_ = leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_529_, 0, v_k_516_);
        leanh::lean_closure_set(v___f_529_, 1, v_map_527_);
        leanh::lean_closure_set(v___f_529_, 2, v___f_517_);
        v___x_530_ = leanh::lean_apply_4(
            v_toBind_518_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_528_,
            v___f_529_,
        );
        v___x_531_ = leanh::lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___x_531_, 0, v_mutex_519_);
        v___x_532_ = leanh::lean_apply_2(v_inst_514_, leanh::lean_box(0), v___x_531_);
        v___f_533_ = leanh::lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_533_, 0, v___x_532_);
        v_y_534_ = leanh::lean_apply_4(
            v_inst_520_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_530_,
            v___f_533_,
        );
        v___x_535_ = leanh::lean_apply_4(
            v_map_527_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_521_,
            v_y_534_,
        );
        return v___x_535_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(
    mut v_toApplicative_536_: *mut leanh::LeanObject,
    mut v_inst_537_: *mut leanh::LeanObject,
    mut v___f_538_: *mut leanh::LeanObject,
    mut v_k_539_: *mut leanh::LeanObject,
    mut v___f_540_: *mut leanh::LeanObject,
    mut v_toBind_541_: *mut leanh::LeanObject,
    mut v_mutex_542_: *mut leanh::LeanObject,
    mut v_inst_543_: *mut leanh::LeanObject,
    mut v___f_544_: *mut leanh::LeanObject,
    mut v_____do__lift_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_191__boxed_546_: u8 = 0;
    let mut v_res_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_546_ = (leanh::lean_unbox(v_____do__lift_545_) as u8);
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
    mut v_inst_548_: *mut leanh::LeanObject,
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_inst_550_: *mut leanh::LeanObject,
    mut v_mutex_551_: *mut leanh::LeanObject,
    mut v_k_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_553_ = leanh::lean_ctor_get(v_inst_548_, 0);
    leanh::lean_inc_ref(v_toApplicative_553_);
    v_toBind_554_ = leanh::lean_ctor_get(v_inst_548_, 1);
    leanh::lean_inc_n(v_toBind_554_, 2);
    leanh::lean_dec_ref(v_inst_548_);
    v_ref_555_ = leanh::lean_ctor_get(v_mutex_551_, 0);
    leanh::lean_inc(v_ref_555_);
    v_mutex_556_ = leanh::lean_ctor_get(v_mutex_551_, 1);
    leanh::lean_inc_n(v_mutex_556_, 2);
    leanh::lean_dec_ref(v_mutex_551_);
    v___f_557_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    v___f_558_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_559_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_559_, 0, v_ref_555_);
    leanh::lean_inc(v_inst_549_);
    v___f_560_ = leanh::lean_alloc_closure(
        l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_560_, 0, v_toApplicative_553_);
    leanh::lean_closure_set(v___f_560_, 1, v_inst_549_);
    leanh::lean_closure_set(v___f_560_, 2, v___f_559_);
    leanh::lean_closure_set(v___f_560_, 3, v_k_552_);
    leanh::lean_closure_set(v___f_560_, 4, v___f_557_);
    leanh::lean_closure_set(v___f_560_, 5, v_toBind_554_);
    leanh::lean_closure_set(v___f_560_, 6, v_mutex_556_);
    leanh::lean_closure_set(v___f_560_, 7, v_inst_550_);
    leanh::lean_closure_set(v___f_560_, 8, v___f_558_);
    v___x_561_ = leanh::lean_alloc_closure(
        l_Std_BaseSharedMutex_tryRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_561_, 0, v_mutex_556_);
    v___x_562_ = leanh::lean_apply_2(v_inst_549_, leanh::lean_box(0), v___x_561_);
    v___x_563_ = leanh::lean_apply_4(
        v_toBind_554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_562_,
        v___f_560_,
    );
    return v___x_563_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead(
    mut v_m_564_: *mut leanh::LeanObject,
    mut v_00_u03b1_565_: *mut leanh::LeanObject,
    mut v_00_u03b2_566_: *mut leanh::LeanObject,
    mut v_inst_567_: *mut leanh::LeanObject,
    mut v_inst_568_: *mut leanh::LeanObject,
    mut v_inst_569_: *mut leanh::LeanObject,
    mut v_mutex_570_: *mut leanh::LeanObject,
    mut v_k_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl =
        _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_SharedMutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_SharedMutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sync_SharedMutex(builtin);
}