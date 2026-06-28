// Lean compiler output
// Module: Std.Sync.SharedMutex
// Imports: Std.Sync.Basic
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unbox,
};
pub static mut l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value)
        as *mut LeanObject;
pub static l_Std_SharedMutex_atomically___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_SharedMutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_SharedMutex_atomically___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_atomically___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_SharedMutex_tryAtomically___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_SharedMutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_SharedMutex_tryAtomically___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_SharedMutex_tryAtomically___redArg___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl() -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    v___x_287_ = lean_box(0);
    return v___x_287_;
}
pub unsafe fn l_Std_BaseSharedMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_290_: *mut LeanObject = core::ptr::null_mut();
    v_res_290_ = lean_io_basesharedmutex_new();
    return v_res_290_;
}
pub unsafe fn l_Std_BaseSharedMutex_write___boxed(
    mut v_mutex_293_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_295_ = lean_io_basesharedmutex_write(v_mutex_293_);
    lean_dec(v_mutex_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryWrite___boxed(
    mut v_mutex_298_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: u8 = 0;
    let mut v_r_301_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = lean_io_basesharedmutex_try_write(v_mutex_298_);
    lean_dec(v_mutex_298_);
    v_r_301_ = lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockWrite___boxed(
    mut v_mutex_304_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = lean_io_basesharedmutex_unlock_write(v_mutex_304_);
    lean_dec(v_mutex_304_);
    return v_res_306_;
}
pub unsafe fn l_Std_BaseSharedMutex_read___boxed(
    mut v_mutex_309_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_311_: *mut LeanObject = core::ptr::null_mut();
    v_res_311_ = lean_io_basesharedmutex_read(v_mutex_309_);
    lean_dec(v_mutex_309_);
    return v_res_311_;
}
pub unsafe fn l_Std_BaseSharedMutex_tryRead___boxed(
    mut v_mutex_314_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: u8 = 0;
    let mut v_r_317_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = lean_io_basesharedmutex_try_read(v_mutex_314_);
    lean_dec(v_mutex_314_);
    v_r_317_ = lean_box((v_res_316_) as usize);
    return v_r_317_;
}
pub unsafe fn l_Std_BaseSharedMutex_unlockRead___boxed(
    mut v_mutex_320_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_322_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_io_basesharedmutex_unlock_read(v_mutex_320_);
    lean_dec(v_mutex_320_);
    return v_res_322_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(
    mut v_self_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mutex_324_: *mut LeanObject = core::ptr::null_mut();
    v_mutex_324_ = lean_ctor_get(v_self_323_, 1);
    lean_inc(v_mutex_324_);
    return v_mutex_324_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed(
    mut v_self_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(v_self_325_);
    lean_dec_ref(v_self_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_instCoeOutSharedMutexBaseSharedMutex(
    mut v_00_u03b1_328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_329_: *mut LeanObject = core::ptr::null_mut();
    v___f_329_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0;
    return v___f_329_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg(mut v_a_330_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_st_mk_ref(v_a_330_);
    v___x_333_ = lean_io_basesharedmutex_new();
    v___x_334_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_334_, 0, v___x_332_);
    lean_ctor_set(v___x_334_, 1, v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Std_SharedMutex_new___redArg___boxed(
    mut v_a_335_: *mut LeanObject,
    mut v_a_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Std_SharedMutex_new___redArg(v_a_335_);
    return v_res_337_;
}
pub unsafe fn l_Std_SharedMutex_new(
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_a_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_341_ = l_Std_SharedMutex_new___redArg(v_a_339_);
    return v___x_341_;
}
pub unsafe fn l_Std_SharedMutex_new___boxed(
    mut v_00_u03b1_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_345_: *mut LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Std_SharedMutex_new(v_00_u03b1_342_, v_a_343_);
    return v_res_345_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__0(
    mut v_k_346_: *mut LeanObject,
    mut v_ref_347_: *mut LeanObject,
    mut v_____r_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_349_ = lean_apply_1(v_k_346_, v_ref_347_);
    return v___x_349_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1(
    mut v_x_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_351_: *mut LeanObject = core::ptr::null_mut();
    v_fst_351_ = lean_ctor_get(v_x_350_, 0);
    lean_inc(v_fst_351_);
    return v_fst_351_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__1___boxed(
    mut v_x_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_353_: *mut LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_352_);
    lean_dec_ref(v_x_352_);
    return v_res_353_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2(
    mut v___x_354_: *mut LeanObject,
    mut v_x_355_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_354_);
    return v___x_354_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg___lam__2___boxed(
    mut v___x_356_: *mut LeanObject,
    mut v_x_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_356_, v_x_357_);
    lean_dec(v_x_357_);
    lean_dec(v___x_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_SharedMutex_atomically___redArg(
    mut v_inst_360_: *mut LeanObject,
    mut v_inst_361_: *mut LeanObject,
    mut v_inst_362_: *mut LeanObject,
    mut v_mutex_363_: *mut LeanObject,
    mut v_k_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_365_ = lean_ctor_get(v_inst_360_, 0);
    v_toFunctor_366_ = lean_ctor_get(v_toApplicative_365_, 0);
    lean_inc_ref(v_toFunctor_366_);
    v_toBind_367_ = lean_ctor_get(v_inst_360_, 1);
    lean_inc(v_toBind_367_);
    lean_dec_ref(v_inst_360_);
    v_ref_368_ = lean_ctor_get(v_mutex_363_, 0);
    lean_inc(v_ref_368_);
    v_mutex_369_ = lean_ctor_get(v_mutex_363_, 1);
    lean_inc_n(v_mutex_369_, 2);
    lean_dec_ref(v_mutex_363_);
    v_map_370_ = lean_ctor_get(v_toFunctor_366_, 0);
    lean_inc(v_map_370_);
    lean_dec_ref(v_toFunctor_366_);
    v___x_371_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_write___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_371_, 0, v_mutex_369_);
    lean_inc(v_inst_361_);
    v___x_372_ = lean_apply_2(v_inst_361_, lean_box(0), v___x_371_);
    v___f_373_ = lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_373_, 0, v_k_364_);
    lean_closure_set(v___f_373_, 1, v_ref_368_);
    v___f_374_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___x_375_ = lean_apply_4(
        v_toBind_367_,
        lean_box(0),
        lean_box(0),
        v___x_372_,
        v___f_373_,
    );
    v___x_376_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_376_, 0, v_mutex_369_);
    v___x_377_ = lean_apply_2(v_inst_361_, lean_box(0), v___x_376_);
    v___f_378_ = lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_378_, 0, v___x_377_);
    v_y_379_ = lean_apply_4(
        v_inst_362_,
        lean_box(0),
        lean_box(0),
        v___x_375_,
        v___f_378_,
    );
    v___x_380_ = lean_apply_4(v_map_370_, lean_box(0), lean_box(0), v___f_374_, v_y_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_SharedMutex_atomically(
    mut v_m_381_: *mut LeanObject,
    mut v_00_u03b1_382_: *mut LeanObject,
    mut v_00_u03b2_383_: *mut LeanObject,
    mut v_inst_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_mutex_387_: *mut LeanObject,
    mut v_k_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_391_: *mut LeanObject = core::ptr::null_mut();
    v_fst_391_ = lean_ctor_get(v_x_390_, 0);
    lean_inc(v_fst_391_);
    return v_fst_391_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_393_: *mut LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_392_);
    lean_dec_ref(v_x_392_);
    return v_res_393_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__1(
    mut v_val_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_395_, 0, v_val_394_);
    return v___x_395_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2(
    mut v___x_396_: *mut LeanObject,
    mut v_x_397_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_396_);
    return v___x_396_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_398_: *mut LeanObject,
    mut v_x_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_400_: *mut LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_398_, v_x_399_);
    lean_dec(v_x_399_);
    lean_dec(v___x_398_);
    return v_res_400_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_401_: *mut LeanObject,
    mut v_k_402_: *mut LeanObject,
    mut v_ref_403_: *mut LeanObject,
    mut v___f_404_: *mut LeanObject,
    mut v_mutex_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v_inst_407_: *mut LeanObject,
    mut v___f_408_: *mut LeanObject,
    mut v_____do__lift_409_: u8,
) -> *mut LeanObject {
    if v_____do__lift_409_ == 0 {
        let mut v_toPure_410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_408_);
        lean_dec(v_inst_407_);
        lean_dec(v_inst_406_);
        lean_dec(v_mutex_405_);
        lean_dec_ref(v___f_404_);
        lean_dec(v_ref_403_);
        lean_dec(v_k_402_);
        v_toPure_410_ = lean_ctor_get(v_toApplicative_401_, 1);
        lean_inc(v_toPure_410_);
        lean_dec_ref(v_toApplicative_401_);
        v___x_411_ = lean_box(0);
        v___x_412_ = lean_apply_2(v_toPure_410_, lean_box(0), v___x_411_);
        return v___x_412_;
    } else {
        let mut v_toFunctor_413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_419_: *mut LeanObject = core::ptr::null_mut();
        let mut v_y_420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_413_ = lean_ctor_get(v_toApplicative_401_, 0);
        lean_inc_ref(v_toFunctor_413_);
        lean_dec_ref(v_toApplicative_401_);
        v_map_414_ = lean_ctor_get(v_toFunctor_413_, 0);
        lean_inc_n(v_map_414_, 2);
        lean_dec_ref(v_toFunctor_413_);
        v___x_415_ = lean_apply_1(v_k_402_, v_ref_403_);
        v___x_416_ = lean_apply_4(v_map_414_, lean_box(0), lean_box(0), v___f_404_, v___x_415_);
        v___x_417_ = lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockWrite___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___x_417_, 0, v_mutex_405_);
        v___x_418_ = lean_apply_2(v_inst_406_, lean_box(0), v___x_417_);
        v___f_419_ = lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_419_, 0, v___x_418_);
        v_y_420_ = lean_apply_4(
            v_inst_407_,
            lean_box(0),
            lean_box(0),
            v___x_416_,
            v___f_419_,
        );
        v___x_421_ = lean_apply_4(v_map_414_, lean_box(0), lean_box(0), v___f_408_, v_y_420_);
        return v___x_421_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_422_: *mut LeanObject,
    mut v_k_423_: *mut LeanObject,
    mut v_ref_424_: *mut LeanObject,
    mut v___f_425_: *mut LeanObject,
    mut v_mutex_426_: *mut LeanObject,
    mut v_inst_427_: *mut LeanObject,
    mut v_inst_428_: *mut LeanObject,
    mut v___f_429_: *mut LeanObject,
    mut v_____do__lift_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_140__boxed_431_: u8 = 0;
    let mut v_res_432_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_431_ = (lean_unbox(v_____do__lift_430_) as u8);
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
    mut v_inst_435_: *mut LeanObject,
    mut v_inst_436_: *mut LeanObject,
    mut v_inst_437_: *mut LeanObject,
    mut v_mutex_438_: *mut LeanObject,
    mut v_k_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_440_ = lean_ctor_get(v_inst_435_, 0);
    lean_inc_ref(v_toApplicative_440_);
    v_toBind_441_ = lean_ctor_get(v_inst_435_, 1);
    lean_inc(v_toBind_441_);
    lean_dec_ref(v_inst_435_);
    v_ref_442_ = lean_ctor_get(v_mutex_438_, 0);
    lean_inc(v_ref_442_);
    v_mutex_443_ = lean_ctor_get(v_mutex_438_, 1);
    lean_inc_n(v_mutex_443_, 2);
    lean_dec_ref(v_mutex_438_);
    v___f_444_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_445_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    lean_inc(v_inst_436_);
    v___f_446_ = lean_alloc_closure(
        l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_446_, 0, v_toApplicative_440_);
    lean_closure_set(v___f_446_, 1, v_k_439_);
    lean_closure_set(v___f_446_, 2, v_ref_442_);
    lean_closure_set(v___f_446_, 3, v___f_445_);
    lean_closure_set(v___f_446_, 4, v_mutex_443_);
    lean_closure_set(v___f_446_, 5, v_inst_436_);
    lean_closure_set(v___f_446_, 6, v_inst_437_);
    lean_closure_set(v___f_446_, 7, v___f_444_);
    v___x_447_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_tryWrite___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_447_, 0, v_mutex_443_);
    v___x_448_ = lean_apply_2(v_inst_436_, lean_box(0), v___x_447_);
    v___x_449_ = lean_apply_4(
        v_toBind_441_,
        lean_box(0),
        lean_box(0),
        v___x_448_,
        v___f_446_,
    );
    return v___x_449_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomically(
    mut v_m_450_: *mut LeanObject,
    mut v_00_u03b1_451_: *mut LeanObject,
    mut v_00_u03b2_452_: *mut LeanObject,
    mut v_inst_453_: *mut LeanObject,
    mut v_inst_454_: *mut LeanObject,
    mut v_inst_455_: *mut LeanObject,
    mut v_mutex_456_: *mut LeanObject,
    mut v_k_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_k_459_: *mut LeanObject,
    mut v_state_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_apply_1(v_k_459_, v_state_460_);
    return v___x_461_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2(
    mut v_ref_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_st_ref_get(v_ref_462_);
    return v___x_464_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(
    mut v_ref_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_465_);
    lean_dec(v_ref_465_);
    return v_res_467_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg___lam__1(
    mut v_ref_468_: *mut LeanObject,
    mut v_inst_469_: *mut LeanObject,
    mut v_toBind_470_: *mut LeanObject,
    mut v___f_471_: *mut LeanObject,
    mut v_____r_472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___f_473_ = lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_473_, 0, v_ref_468_);
    v___x_474_ = lean_apply_2(v_inst_469_, lean_box(0), v___f_473_);
    v___x_475_ = lean_apply_4(
        v_toBind_470_,
        lean_box(0),
        lean_box(0),
        v___x_474_,
        v___f_471_,
    );
    return v___x_475_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead___redArg(
    mut v_inst_476_: *mut LeanObject,
    mut v_inst_477_: *mut LeanObject,
    mut v_inst_478_: *mut LeanObject,
    mut v_mutex_479_: *mut LeanObject,
    mut v_k_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_481_ = lean_ctor_get(v_inst_476_, 0);
    v_toFunctor_482_ = lean_ctor_get(v_toApplicative_481_, 0);
    lean_inc_ref(v_toFunctor_482_);
    v_toBind_483_ = lean_ctor_get(v_inst_476_, 1);
    lean_inc_n(v_toBind_483_, 2);
    lean_dec_ref(v_inst_476_);
    v_ref_484_ = lean_ctor_get(v_mutex_479_, 0);
    lean_inc(v_ref_484_);
    v_mutex_485_ = lean_ctor_get(v_mutex_479_, 1);
    lean_inc_n(v_mutex_485_, 2);
    lean_dec_ref(v_mutex_479_);
    v_map_486_ = lean_ctor_get(v_toFunctor_482_, 0);
    lean_inc(v_map_486_);
    lean_dec_ref(v_toFunctor_482_);
    v___x_487_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_read___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_487_, 0, v_mutex_485_);
    lean_inc_n(v_inst_477_, 2);
    v___x_488_ = lean_apply_2(v_inst_477_, lean_box(0), v___x_487_);
    v___f_489_ = lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_489_, 0, v_k_480_);
    v___f_490_ = l_Std_SharedMutex_atomically___redArg___closed__0;
    v___f_491_ = lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_491_, 0, v_ref_484_);
    lean_closure_set(v___f_491_, 1, v_inst_477_);
    lean_closure_set(v___f_491_, 2, v_toBind_483_);
    lean_closure_set(v___f_491_, 3, v___f_489_);
    v___x_492_ = lean_apply_4(
        v_toBind_483_,
        lean_box(0),
        lean_box(0),
        v___x_488_,
        v___f_491_,
    );
    v___x_493_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_493_, 0, v_mutex_485_);
    v___x_494_ = lean_apply_2(v_inst_477_, lean_box(0), v___x_493_);
    v___f_495_ = lean_alloc_closure(
        l_Std_SharedMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_495_, 0, v___x_494_);
    v_y_496_ = lean_apply_4(
        v_inst_478_,
        lean_box(0),
        lean_box(0),
        v___x_492_,
        v___f_495_,
    );
    v___x_497_ = lean_apply_4(v_map_486_, lean_box(0), lean_box(0), v___f_490_, v_y_496_);
    return v___x_497_;
}
pub unsafe fn l_Std_SharedMutex_atomicallyRead(
    mut v_m_498_: *mut LeanObject,
    mut v_00_u03b1_499_: *mut LeanObject,
    mut v_00_u03b2_500_: *mut LeanObject,
    mut v_inst_501_: *mut LeanObject,
    mut v_inst_502_: *mut LeanObject,
    mut v_inst_503_: *mut LeanObject,
    mut v_mutex_504_: *mut LeanObject,
    mut v_k_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_k_507_: *mut LeanObject,
    mut v_map_508_: *mut LeanObject,
    mut v___f_509_: *mut LeanObject,
    mut v_state_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_apply_1(v_k_507_, v_state_510_);
    v___x_512_ = lean_apply_4(v_map_508_, lean_box(0), lean_box(0), v___f_509_, v___x_511_);
    return v___x_512_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(
    mut v_toApplicative_513_: *mut LeanObject,
    mut v_inst_514_: *mut LeanObject,
    mut v___f_515_: *mut LeanObject,
    mut v_k_516_: *mut LeanObject,
    mut v___f_517_: *mut LeanObject,
    mut v_toBind_518_: *mut LeanObject,
    mut v_mutex_519_: *mut LeanObject,
    mut v_inst_520_: *mut LeanObject,
    mut v___f_521_: *mut LeanObject,
    mut v_____do__lift_522_: u8,
) -> *mut LeanObject {
    if v_____do__lift_522_ == 0 {
        let mut v_toPure_523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_521_);
        lean_dec(v_inst_520_);
        lean_dec(v_mutex_519_);
        lean_dec(v_toBind_518_);
        lean_dec_ref(v___f_517_);
        lean_dec(v_k_516_);
        lean_dec_ref(v___f_515_);
        lean_dec(v_inst_514_);
        v_toPure_523_ = lean_ctor_get(v_toApplicative_513_, 1);
        lean_inc(v_toPure_523_);
        lean_dec_ref(v_toApplicative_513_);
        v___x_524_ = lean_box(0);
        v___x_525_ = lean_apply_2(v_toPure_523_, lean_box(0), v___x_524_);
        return v___x_525_;
    } else {
        let mut v_toFunctor_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_533_: *mut LeanObject = core::ptr::null_mut();
        let mut v_y_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_526_ = lean_ctor_get(v_toApplicative_513_, 0);
        lean_inc_ref(v_toFunctor_526_);
        lean_dec_ref(v_toApplicative_513_);
        v_map_527_ = lean_ctor_get(v_toFunctor_526_, 0);
        lean_inc_n(v_map_527_, 2);
        lean_dec_ref(v_toFunctor_526_);
        lean_inc(v_inst_514_);
        v___x_528_ = lean_apply_2(v_inst_514_, lean_box(0), v___f_515_);
        v___f_529_ = lean_alloc_closure(
            l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_529_, 0, v_k_516_);
        lean_closure_set(v___f_529_, 1, v_map_527_);
        lean_closure_set(v___f_529_, 2, v___f_517_);
        v___x_530_ = lean_apply_4(
            v_toBind_518_,
            lean_box(0),
            lean_box(0),
            v___x_528_,
            v___f_529_,
        );
        v___x_531_ = lean_alloc_closure(
            l_Std_BaseSharedMutex_unlockRead___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___x_531_, 0, v_mutex_519_);
        v___x_532_ = lean_apply_2(v_inst_514_, lean_box(0), v___x_531_);
        v___f_533_ = lean_alloc_closure(
            l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_533_, 0, v___x_532_);
        v_y_534_ = lean_apply_4(
            v_inst_520_,
            lean_box(0),
            lean_box(0),
            v___x_530_,
            v___f_533_,
        );
        v___x_535_ = lean_apply_4(v_map_527_, lean_box(0), lean_box(0), v___f_521_, v_y_534_);
        return v___x_535_;
    }
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(
    mut v_toApplicative_536_: *mut LeanObject,
    mut v_inst_537_: *mut LeanObject,
    mut v___f_538_: *mut LeanObject,
    mut v_k_539_: *mut LeanObject,
    mut v___f_540_: *mut LeanObject,
    mut v_toBind_541_: *mut LeanObject,
    mut v_mutex_542_: *mut LeanObject,
    mut v_inst_543_: *mut LeanObject,
    mut v___f_544_: *mut LeanObject,
    mut v_____do__lift_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_191__boxed_546_: u8 = 0;
    let mut v_res_547_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_546_ = (lean_unbox(v_____do__lift_545_) as u8);
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
    mut v_inst_548_: *mut LeanObject,
    mut v_inst_549_: *mut LeanObject,
    mut v_inst_550_: *mut LeanObject,
    mut v_mutex_551_: *mut LeanObject,
    mut v_k_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_553_ = lean_ctor_get(v_inst_548_, 0);
    lean_inc_ref(v_toApplicative_553_);
    v_toBind_554_ = lean_ctor_get(v_inst_548_, 1);
    lean_inc_n(v_toBind_554_, 2);
    lean_dec_ref(v_inst_548_);
    v_ref_555_ = lean_ctor_get(v_mutex_551_, 0);
    lean_inc(v_ref_555_);
    v_mutex_556_ = lean_ctor_get(v_mutex_551_, 1);
    lean_inc_n(v_mutex_556_, 2);
    lean_dec_ref(v_mutex_551_);
    v___f_557_ = l_Std_SharedMutex_tryAtomically___redArg___closed__1;
    v___f_558_ = l_Std_SharedMutex_tryAtomically___redArg___closed__0;
    v___f_559_ = lean_alloc_closure(
        l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_559_, 0, v_ref_555_);
    lean_inc(v_inst_549_);
    v___f_560_ = lean_alloc_closure(
        l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_560_, 0, v_toApplicative_553_);
    lean_closure_set(v___f_560_, 1, v_inst_549_);
    lean_closure_set(v___f_560_, 2, v___f_559_);
    lean_closure_set(v___f_560_, 3, v_k_552_);
    lean_closure_set(v___f_560_, 4, v___f_557_);
    lean_closure_set(v___f_560_, 5, v_toBind_554_);
    lean_closure_set(v___f_560_, 6, v_mutex_556_);
    lean_closure_set(v___f_560_, 7, v_inst_550_);
    lean_closure_set(v___f_560_, 8, v___f_558_);
    v___x_561_ = lean_alloc_closure(
        l_Std_BaseSharedMutex_tryRead___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_561_, 0, v_mutex_556_);
    v___x_562_ = lean_apply_2(v_inst_549_, lean_box(0), v___x_561_);
    v___x_563_ = lean_apply_4(
        v_toBind_554_,
        lean_box(0),
        lean_box(0),
        v___x_562_,
        v___f_560_,
    );
    return v___x_563_;
}
pub unsafe fn l_Std_SharedMutex_tryAtomicallyRead(
    mut v_m_564_: *mut LeanObject,
    mut v_00_u03b1_565_: *mut LeanObject,
    mut v_00_u03b2_566_: *mut LeanObject,
    mut v_inst_567_: *mut LeanObject,
    mut v_inst_568_: *mut LeanObject,
    mut v_inst_569_: *mut LeanObject,
    mut v_mutex_570_: *mut LeanObject,
    mut v_k_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut LeanObject {
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
    l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl =
        _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_SharedMutex(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Sync_SharedMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_SharedMutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_SharedMutex(builtin);
}
