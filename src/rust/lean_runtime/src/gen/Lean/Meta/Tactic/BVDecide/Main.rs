// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Main
// Imports: Lean.Meta.Tactic.BVDecide.Prover.Bitblast Lean.Meta.Tactic.BVDecide.Normalize
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Counterexample::l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize,
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Prover::Basic::l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Prover::Bitblast::{
    initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast,
    l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::l_Lean_Meta_Tactic_BVDecide_M_run___redArg;
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0(
    mut v_g_292_: *mut LeanObject,
    mut v___x_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
    mut v___y_295_: *mut LeanObject,
    mut v___y_296_: *mut LeanObject,
    mut v___y_297_: *mut LeanObject,
    mut v___y_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
        v_g_292_, v___x_293_, v___y_295_, v___y_296_, v___y_297_, v___y_298_,
    );
    return v___x_300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0___boxed(
    mut v_g_301_: *mut LeanObject,
    mut v___x_302_: *mut LeanObject,
    mut v___y_303_: *mut LeanObject,
    mut v___y_304_: *mut LeanObject,
    mut v___y_305_: *mut LeanObject,
    mut v___y_306_: *mut LeanObject,
    mut v___y_307_: *mut LeanObject,
    mut v___y_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_309_: *mut LeanObject = core::ptr::null_mut();
    v_res_309_ =
        l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0(
            v_g_301_, v___x_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_,
        );
    lean_dec(v___y_307_);
    lean_dec_ref(v___y_306_);
    lean_dec(v___y_305_);
    lean_dec_ref(v___y_304_);
    lean_dec(v___y_303_);
    return v_res_309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(
    mut v_g_310_: *mut LeanObject,
    mut v_ctx_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
    mut v_a_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed as *mut core::ffi::c_void,
        9,
        1,
    );
    lean_closure_set(v___x_317_, 0, v_ctx_311_);
    v___f_318_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
    lean_closure_set(v___f_318_, 0, v_g_310_);
    lean_closure_set(v___f_318_, 1, v___x_317_);
    v___x_319_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
        v___f_318_, v_a_312_, v_a_313_, v_a_314_, v_a_315_,
    );
    return v___x_319_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(
    mut v_g_320_: *mut LeanObject,
    mut v_ctx_321_: *mut LeanObject,
    mut v_a_322_: *mut LeanObject,
    mut v_a_323_: *mut LeanObject,
    mut v_a_324_: *mut LeanObject,
    mut v_a_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(
        v_g_320_, v_ctx_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_,
    );
    lean_dec(v_a_325_);
    lean_dec_ref(v_a_324_);
    lean_dec(v_a_323_);
    lean_dec_ref(v_a_322_);
    return v_res_327_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
    mut v_g_330_: *mut LeanObject,
    mut v_ctx_331_: *mut LeanObject,
    mut v_a_332_: *mut LeanObject,
    mut v_a_333_: *mut LeanObject,
    mut v_a_334_: *mut LeanObject,
    mut v_a_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v_val_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_351_: u8 = 0;
    let mut v_a_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_355_: u8 = 0;
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_a_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_385_: u8 = 0;
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_391_: u8 = 0;
    let mut v_a_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_337_ = lean_ctor_get(v_ctx_331_, 5);
                v___x_338_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
                    v_g_330_,
                    v_config_337_,
                    v_a_332_,
                    v_a_333_,
                    v_a_334_,
                    v_a_335_,
                );
                if lean_obj_tag(v___x_338_) == 0 {
                    v_a_339_ = lean_ctor_get(v___x_338_, 0);
                    v_isSharedCheck_391_ = (!lean_is_exclusive(v___x_338_)) as u8;
                    if v_isSharedCheck_391_ == 0 {
                        v___x_341_ = v___x_338_;
                        v_isShared_342_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_339_);
                        lean_dec(v___x_338_);
                        v___x_341_ = lean_box(0);
                        v_isShared_342_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_ctx_331_);
                    v_a_392_ = lean_ctor_get(v___x_338_, 0);
                    v_isSharedCheck_399_ = (!lean_is_exclusive(v___x_338_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v___x_394_ = v___x_338_;
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_392_);
                        lean_dec(v___x_338_);
                        v___x_394_ = lean_box(0);
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_339_) == 1 {
                    lean_del_object(v___x_341_);
                    v_val_343_ = lean_ctor_get(v_a_339_, 0);
                    v_isSharedCheck_386_ = (!lean_is_exclusive(v_a_339_)) as u8;
                    if v_isSharedCheck_386_ == 0 {
                        v___x_345_ = v_a_339_;
                        v_isShared_346_ = v_isSharedCheck_386_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_343_);
                        lean_dec(v_a_339_);
                        v___x_345_ = lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_386_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_339_);
                    lean_dec_ref(v_ctx_331_);
                    v___x_387_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0;
                    if v_isShared_342_ == 0 {
                        lean_ctor_set(v___x_341_, 0, v___x_387_);
                        v___x_389_ = v___x_341_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
                        v___x_389_ = v_reuseFailAlloc_390_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_347_ =
                    l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(
                        v_val_343_, v_ctx_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_,
                    );
                if lean_obj_tag(v___x_347_) == 0 {
                    v_a_348_ = lean_ctor_get(v___x_347_, 0);
                    v_isSharedCheck_377_ = (!lean_is_exclusive(v___x_347_)) as u8;
                    if v_isSharedCheck_377_ == 0 {
                        v___x_350_ = v___x_347_;
                        v_isShared_351_ = v_isSharedCheck_377_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_348_);
                        lean_dec(v___x_347_);
                        v___x_350_ = lean_box(0);
                        v_isShared_351_ = v_isSharedCheck_377_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_345_);
                    v_a_378_ = lean_ctor_get(v___x_347_, 0);
                    v_isSharedCheck_385_ = (!lean_is_exclusive(v___x_347_)) as u8;
                    if v_isSharedCheck_385_ == 0 {
                        v___x_380_ = v___x_347_;
                        v_isShared_381_ = v_isSharedCheck_385_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_378_);
                        lean_dec(v___x_347_);
                        v___x_380_ = lean_box(0);
                        v_isShared_381_ = v_isSharedCheck_385_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_348_) == 0 {
                    lean_del_object(v___x_345_);
                    v_a_352_ = lean_ctor_get(v_a_348_, 0);
                    v_isSharedCheck_362_ = (!lean_is_exclusive(v_a_348_)) as u8;
                    if v_isSharedCheck_362_ == 0 {
                        v___x_354_ = v_a_348_;
                        v_isShared_355_ = v_isSharedCheck_362_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_352_);
                        lean_dec(v_a_348_);
                        v___x_354_ = lean_box(0);
                        v_isShared_355_ = v_isSharedCheck_362_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_363_ = lean_ctor_get(v_a_348_, 0);
                    v_isSharedCheck_376_ = (!lean_is_exclusive(v_a_348_)) as u8;
                    if v_isSharedCheck_376_ == 0 {
                        v___x_365_ = v_a_348_;
                        v_isShared_366_ = v_isSharedCheck_376_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_363_);
                        lean_dec(v_a_348_);
                        v___x_365_ = lean_box(0);
                        v_isShared_366_ = v_isSharedCheck_376_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_355_ == 0 {
                    v___x_357_ = v___x_354_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_352_);
                    v___x_357_ = v_reuseFailAlloc_361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_351_ == 0 {
                    lean_ctor_set(v___x_350_, 0, v___x_357_);
                    v___x_359_ = v___x_350_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
                    v___x_359_ = v_reuseFailAlloc_360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_359_;
            }
            7 => {
                if v_isShared_346_ == 0 {
                    lean_ctor_set(v___x_345_, 0, v_a_363_);
                    v___x_368_ = v___x_345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_363_);
                    v___x_368_ = v_reuseFailAlloc_375_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_366_ == 0 {
                    lean_ctor_set(v___x_365_, 0, v___x_368_);
                    v___x_370_ = v___x_365_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
                    v___x_370_ = v_reuseFailAlloc_374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_351_ == 0 {
                    lean_ctor_set(v___x_350_, 0, v___x_370_);
                    v___x_372_ = v___x_350_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
                    v___x_372_ = v_reuseFailAlloc_373_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_372_;
            }
            11 => {
                if v_isShared_381_ == 0 {
                    v___x_383_ = v___x_380_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
                    v___x_383_ = v_reuseFailAlloc_384_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_383_;
            }
            13 => {
                return v___x_389_;
            }
            14 => {
                if v_isShared_395_ == 0 {
                    v___x_397_ = v___x_394_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
                    v___x_397_ = v_reuseFailAlloc_398_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___boxed(
    mut v_g_400_: *mut LeanObject,
    mut v_ctx_401_: *mut LeanObject,
    mut v_a_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
    mut v_a_405_: *mut LeanObject,
    mut v_a_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_407_: *mut LeanObject = core::ptr::null_mut();
    v_res_407_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
        v_g_400_, v_ctx_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_,
    );
    lean_dec(v_a_405_);
    lean_dec_ref(v_a_404_);
    lean_dec(v_a_403_);
    lean_dec_ref(v_a_402_);
    return v_res_407_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(
    mut v_msgData_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = lean_st_ref_get(v___y_412_);
    v_env_415_ = lean_ctor_get(v___x_414_, 0);
    lean_inc_ref(v_env_415_);
    lean_dec(v___x_414_);
    v___x_416_ = lean_st_ref_get(v___y_410_);
    v_mctx_417_ = lean_ctor_get(v___x_416_, 0);
    lean_inc_ref(v_mctx_417_);
    lean_dec(v___x_416_);
    v_lctx_418_ = lean_ctor_get(v___y_409_, 2);
    v_options_419_ = lean_ctor_get(v___y_411_, 2);
    lean_inc_ref(v_options_419_);
    lean_inc_ref(v_lctx_418_);
    v___x_420_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_420_, 0, v_env_415_);
    lean_ctor_set(v___x_420_, 1, v_mctx_417_);
    lean_ctor_set(v___x_420_, 2, v_lctx_418_);
    lean_ctor_set(v___x_420_, 3, v_options_419_);
    v___x_421_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_421_, 0, v___x_420_);
    lean_ctor_set(v___x_421_, 1, v_msgData_408_);
    v___x_422_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_422_, 0, v___x_421_);
    return v___x_422_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(
    mut v_msgData_423_: *mut LeanObject,
    mut v___y_424_: *mut LeanObject,
    mut v___y_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_429_: *mut LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(
        v_msgData_423_,
        v___y_424_,
        v___y_425_,
        v___y_426_,
        v___y_427_,
    );
    lean_dec(v___y_427_);
    lean_dec_ref(v___y_426_);
    lean_dec(v___y_425_);
    lean_dec_ref(v___y_424_);
    return v_res_429_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(
    mut v_mvarId_430_: *mut LeanObject,
    mut v_x_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
    mut v___y_433_: *mut LeanObject,
    mut v___y_434_: *mut LeanObject,
    mut v___y_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_441_: u8 = 0;
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_a_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_437_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_430_,
                    v_x_431_,
                    v___y_432_,
                    v___y_433_,
                    v___y_434_,
                    v___y_435_,
                );
                if lean_obj_tag(v___x_437_) == 0 {
                    v_a_438_ = lean_ctor_get(v___x_437_, 0);
                    v_isSharedCheck_445_ = (!lean_is_exclusive(v___x_437_)) as u8;
                    if v_isSharedCheck_445_ == 0 {
                        v___x_440_ = v___x_437_;
                        v_isShared_441_ = v_isSharedCheck_445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_438_);
                        lean_dec(v___x_437_);
                        v___x_440_ = lean_box(0);
                        v_isShared_441_ = v_isSharedCheck_445_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_446_ = lean_ctor_get(v___x_437_, 0);
                    v_isSharedCheck_453_ = (!lean_is_exclusive(v___x_437_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_448_ = v___x_437_;
                        v_isShared_449_ = v_isSharedCheck_453_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_446_);
                        lean_dec(v___x_437_);
                        v___x_448_ = lean_box(0);
                        v_isShared_449_ = v_isSharedCheck_453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_441_ == 0 {
                    v___x_443_ = v___x_440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
                    v___x_443_ = v_reuseFailAlloc_444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_443_;
            }
            3 => {
                if v_isShared_449_ == 0 {
                    v___x_451_ = v___x_448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
                    v___x_451_ = v_reuseFailAlloc_452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg___boxed(
    mut v_mvarId_454_: *mut LeanObject,
    mut v_x_455_: *mut LeanObject,
    mut v___y_456_: *mut LeanObject,
    mut v___y_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_461_: *mut LeanObject = core::ptr::null_mut();
    v_res_461_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(
            v_mvarId_454_,
            v_x_455_,
            v___y_456_,
            v___y_457_,
            v___y_458_,
            v___y_459_,
        );
    lean_dec(v___y_459_);
    lean_dec_ref(v___y_458_);
    lean_dec(v___y_457_);
    lean_dec_ref(v___y_456_);
    return v_res_461_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(
    mut v_00_u03b1_462_: *mut LeanObject,
    mut v_mvarId_463_: *mut LeanObject,
    mut v_x_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(
            v_mvarId_463_,
            v_x_464_,
            v___y_465_,
            v___y_466_,
            v___y_467_,
            v___y_468_,
        );
    return v___x_470_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___boxed(
    mut v_00_u03b1_471_: *mut LeanObject,
    mut v_mvarId_472_: *mut LeanObject,
    mut v_x_473_: *mut LeanObject,
    mut v___y_474_: *mut LeanObject,
    mut v___y_475_: *mut LeanObject,
    mut v___y_476_: *mut LeanObject,
    mut v___y_477_: *mut LeanObject,
    mut v___y_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_479_: *mut LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(
        v_00_u03b1_471_,
        v_mvarId_472_,
        v_x_473_,
        v___y_474_,
        v___y_475_,
        v___y_476_,
        v___y_477_,
    );
    lean_dec(v___y_477_);
    lean_dec_ref(v___y_476_);
    lean_dec(v___y_475_);
    lean_dec_ref(v___y_474_);
    return v_res_479_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
    mut v_msg_480_: *mut LeanObject,
    mut v___y_481_: *mut LeanObject,
    mut v___y_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_486_ = lean_ctor_get(v___y_483_, 5);
                v___x_487_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
                v_a_488_ = lean_ctor_get(v___x_487_, 0);
                v_isSharedCheck_496_ = (!lean_is_exclusive(v___x_487_)) as u8;
                if v_isSharedCheck_496_ == 0 {
                    v___x_490_ = v___x_487_;
                    v_isShared_491_ = v_isSharedCheck_496_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_488_);
                    lean_dec(v___x_487_);
                    v___x_490_ = lean_box(0);
                    v_isShared_491_ = v_isSharedCheck_496_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_486_);
                v___x_492_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_492_, 0, v_ref_486_);
                lean_ctor_set(v___x_492_, 1, v_a_488_);
                if v_isShared_491_ == 0 {
                    lean_ctor_set_tag(v___x_490_, 1);
                    lean_ctor_set(v___x_490_, 0, v___x_492_);
                    v___x_494_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
                    v___x_494_ = v_reuseFailAlloc_495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg___boxed(
    mut v_msg_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
    mut v___y_499_: *mut LeanObject,
    mut v___y_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
    mut v___y_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_503_: *mut LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
        v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_,
    );
    lean_dec(v___y_501_);
    lean_dec_ref(v___y_500_);
    lean_dec(v___y_499_);
    lean_dec_ref(v___y_498_);
    return v_res_503_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(
    mut v_a_504_: *mut LeanObject,
    mut v___y_505_: *mut LeanObject,
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
    mut v___y_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_510_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(
                    v_a_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_,
                );
                if lean_obj_tag(v___x_510_) == 0 {
                    v_a_511_ = lean_ctor_get(v___x_510_, 0);
                    lean_inc(v_a_511_);
                    lean_dec_ref_known(v___x_510_, 1);
                    v___x_512_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_a_511_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
                    v_a_513_ = lean_ctor_get(v___x_512_, 0);
                    lean_inc(v_a_513_);
                    lean_dec_ref(v___x_512_);
                    v___x_514_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_513_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
                    return v___x_514_;
                } else {
                    v_a_515_ = lean_ctor_get(v___x_510_, 0);
                    v_isSharedCheck_522_ = (!lean_is_exclusive(v___x_510_)) as u8;
                    if v_isSharedCheck_522_ == 0 {
                        v___x_517_ = v___x_510_;
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_515_);
                        lean_dec(v___x_510_);
                        v___x_517_ = lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_518_ == 0 {
                    v___x_520_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
                    v___x_520_ = v_reuseFailAlloc_521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed(
    mut v_a_523_: *mut LeanObject,
    mut v___y_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
    mut v___y_526_: *mut LeanObject,
    mut v___y_527_: *mut LeanObject,
    mut v___y_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_529_: *mut LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(
        v_a_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_,
    );
    lean_dec(v___y_527_);
    lean_dec_ref(v___y_526_);
    lean_dec(v___y_525_);
    lean_dec_ref(v___y_524_);
    return v_res_529_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide(
    mut v_g_530_: *mut LeanObject,
    mut v_ctx_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
    mut v_a_534_: *mut LeanObject,
    mut v_a_535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v_a_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goal_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v_a_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_537_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
                    v_g_530_, v_ctx_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_,
                );
                if lean_obj_tag(v___x_537_) == 0 {
                    v_a_538_ = lean_ctor_get(v___x_537_, 0);
                    v_isSharedCheck_550_ = (!lean_is_exclusive(v___x_537_)) as u8;
                    if v_isSharedCheck_550_ == 0 {
                        v___x_540_ = v___x_537_;
                        v_isShared_541_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_538_);
                        lean_dec(v___x_537_);
                        v___x_540_ = lean_box(0);
                        v_isShared_541_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_551_ = lean_ctor_get(v___x_537_, 0);
                    v_isSharedCheck_558_ = (!lean_is_exclusive(v___x_537_)) as u8;
                    if v_isSharedCheck_558_ == 0 {
                        v___x_553_ = v___x_537_;
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_551_);
                        lean_dec(v___x_537_);
                        v___x_553_ = lean_box(0);
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_538_) == 0 {
                    lean_del_object(v___x_540_);
                    v_a_542_ = lean_ctor_get(v_a_538_, 0);
                    lean_inc(v_a_542_);
                    lean_dec_ref_known(v_a_538_, 1);
                    v_goal_543_ = lean_ctor_get(v_a_542_, 0);
                    lean_inc(v_goal_543_);
                    v___f_544_ = lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___f_544_, 0, v_a_542_);
                    v___x_545_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_543_, v___f_544_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
                    return v___x_545_;
                } else {
                    v_a_546_ = lean_ctor_get(v_a_538_, 0);
                    lean_inc(v_a_546_);
                    lean_dec_ref_known(v_a_538_, 1);
                    if v_isShared_541_ == 0 {
                        lean_ctor_set(v___x_540_, 0, v_a_546_);
                        v___x_548_ = v___x_540_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_546_);
                        v___x_548_ = v_reuseFailAlloc_549_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_548_;
            }
            3 => {
                if v_isShared_554_ == 0 {
                    v___x_556_ = v___x_553_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
                    v___x_556_ = v_reuseFailAlloc_557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(
    mut v_g_559_: *mut LeanObject,
    mut v_ctx_560_: *mut LeanObject,
    mut v_a_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(
        v_g_559_, v_ctx_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_,
    );
    lean_dec(v_a_564_);
    lean_dec_ref(v_a_563_);
    lean_dec(v_a_562_);
    lean_dec_ref(v_a_561_);
    return v_res_566_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_msg_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
        v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_,
    );
    return v___x_574_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(
    mut v_00_u03b1_575_: *mut LeanObject,
    mut v_msg_576_: *mut LeanObject,
    mut v___y_577_: *mut LeanObject,
    mut v___y_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_582_: *mut LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(
        v_00_u03b1_575_,
        v_msg_576_,
        v___y_577_,
        v___y_578_,
        v___y_579_,
        v___y_580_,
    );
    lean_dec(v___y_580_);
    lean_dec_ref(v___y_579_);
    lean_dec(v___y_578_);
    lean_dec_ref(v___y_577_);
    return v_res_582_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
}
