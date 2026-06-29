// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Main
// Imports: Lean.Meta.Tactic.BVDecide.Prover.Bitblast Lean.Meta.Tactic.BVDecide.Normalize
use crate::ffi::lean_st_ref_get;
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
pub static l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0(
    mut v_g_292_: *mut crate::leanh::LeanObject,
    mut v___x_293_: *mut crate::leanh::LeanObject,
    mut v___y_294_: *mut crate::leanh::LeanObject,
    mut v___y_295_: *mut crate::leanh::LeanObject,
    mut v___y_296_: *mut crate::leanh::LeanObject,
    mut v___y_297_: *mut crate::leanh::LeanObject,
    mut v___y_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
        v_g_292_, v___x_293_, v___y_295_, v___y_296_, v___y_297_, v___y_298_,
    );
    return v___x_300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0___boxed(
    mut v_g_301_: *mut crate::leanh::LeanObject,
    mut v___x_302_: *mut crate::leanh::LeanObject,
    mut v___y_303_: *mut crate::leanh::LeanObject,
    mut v___y_304_: *mut crate::leanh::LeanObject,
    mut v___y_305_: *mut crate::leanh::LeanObject,
    mut v___y_306_: *mut crate::leanh::LeanObject,
    mut v___y_307_: *mut crate::leanh::LeanObject,
    mut v___y_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_309_ =
        l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0(
            v_g_301_, v___x_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_,
        );
    crate::leanh::lean_dec(v___y_307_);
    crate::leanh::lean_dec_ref(v___y_306_);
    crate::leanh::lean_dec(v___y_305_);
    crate::leanh::lean_dec_ref(v___y_304_);
    crate::leanh::lean_dec(v___y_303_);
    return v_res_309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(
    mut v_g_310_: *mut crate::leanh::LeanObject,
    mut v_ctx_311_: *mut crate::leanh::LeanObject,
    mut v_a_312_: *mut crate::leanh::LeanObject,
    mut v_a_313_: *mut crate::leanh::LeanObject,
    mut v_a_314_: *mut crate::leanh::LeanObject,
    mut v_a_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed as *mut core::ffi::c_void,
        9,
        1,
    );
    crate::leanh::lean_closure_set(v___x_317_, 0, v_ctx_311_);
    v___f_318_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
    crate::leanh::lean_closure_set(v___f_318_, 0, v_g_310_);
    crate::leanh::lean_closure_set(v___f_318_, 1, v___x_317_);
    v___x_319_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(
        v___f_318_, v_a_312_, v_a_313_, v_a_314_, v_a_315_,
    );
    return v___x_319_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat___boxed(
    mut v_g_320_: *mut crate::leanh::LeanObject,
    mut v_ctx_321_: *mut crate::leanh::LeanObject,
    mut v_a_322_: *mut crate::leanh::LeanObject,
    mut v_a_323_: *mut crate::leanh::LeanObject,
    mut v_a_324_: *mut crate::leanh::LeanObject,
    mut v_a_325_: *mut crate::leanh::LeanObject,
    mut v_a_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_327_ = l___private_Lean_Meta_Tactic_BVDecide_Main_0__Lean_Meta_Tactic_BVDecide_bvUnsat(
        v_g_320_, v_ctx_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_,
    );
    crate::leanh::lean_dec(v_a_325_);
    crate::leanh::lean_dec_ref(v_a_324_);
    crate::leanh::lean_dec(v_a_323_);
    crate::leanh::lean_dec_ref(v_a_322_);
    return v_res_327_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
    mut v_g_330_: *mut crate::leanh::LeanObject,
    mut v_ctx_331_: *mut crate::leanh::LeanObject,
    mut v_a_332_: *mut crate::leanh::LeanObject,
    mut v_a_333_: *mut crate::leanh::LeanObject,
    mut v_a_334_: *mut crate::leanh::LeanObject,
    mut v_a_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v_val_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_351_: u8 = 0;
    let mut v_a_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_355_: u8 = 0;
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut v_a_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_a_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_385_: u8 = 0;
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_391_: u8 = 0;
    let mut v_a_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_337_ = crate::leanh::lean_ctor_get(v_ctx_331_, 5);
                v___x_338_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
                    v_g_330_,
                    v_config_337_,
                    v_a_332_,
                    v_a_333_,
                    v_a_334_,
                    v_a_335_,
                );
                if crate::leanh::lean_obj_tag(v___x_338_) == 0 {
                    v_a_339_ = crate::leanh::lean_ctor_get(v___x_338_, 0);
                    v_isSharedCheck_391_ = (!crate::leanh::lean_is_exclusive(v___x_338_)) as u8;
                    if v_isSharedCheck_391_ == 0 {
                        v___x_341_ = v___x_338_;
                        v_isShared_342_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_339_);
                        crate::leanh::lean_dec(v___x_338_);
                        v___x_341_ = crate::leanh::lean_box(0);
                        v_isShared_342_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_331_);
                    v_a_392_ = crate::leanh::lean_ctor_get(v___x_338_, 0);
                    v_isSharedCheck_399_ = (!crate::leanh::lean_is_exclusive(v___x_338_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v___x_394_ = v___x_338_;
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_392_);
                        crate::leanh::lean_dec(v___x_338_);
                        v___x_394_ = crate::leanh::lean_box(0);
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_339_) == 1 {
                    crate::leanh::lean_del_object(v___x_341_);
                    v_val_343_ = crate::leanh::lean_ctor_get(v_a_339_, 0);
                    v_isSharedCheck_386_ = (!crate::leanh::lean_is_exclusive(v_a_339_)) as u8;
                    if v_isSharedCheck_386_ == 0 {
                        v___x_345_ = v_a_339_;
                        v_isShared_346_ = v_isSharedCheck_386_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_343_);
                        crate::leanh::lean_dec(v_a_339_);
                        v___x_345_ = crate::leanh::lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_386_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_339_);
                    crate::leanh::lean_dec_ref(v_ctx_331_);
                    v___x_387_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27___closed__0;
                    if v_isShared_342_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_387_);
                        v___x_389_ = v___x_341_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_390_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
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
                if crate::leanh::lean_obj_tag(v___x_347_) == 0 {
                    v_a_348_ = crate::leanh::lean_ctor_get(v___x_347_, 0);
                    v_isSharedCheck_377_ = (!crate::leanh::lean_is_exclusive(v___x_347_)) as u8;
                    if v_isSharedCheck_377_ == 0 {
                        v___x_350_ = v___x_347_;
                        v_isShared_351_ = v_isSharedCheck_377_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_348_);
                        crate::leanh::lean_dec(v___x_347_);
                        v___x_350_ = crate::leanh::lean_box(0);
                        v_isShared_351_ = v_isSharedCheck_377_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_345_);
                    v_a_378_ = crate::leanh::lean_ctor_get(v___x_347_, 0);
                    v_isSharedCheck_385_ = (!crate::leanh::lean_is_exclusive(v___x_347_)) as u8;
                    if v_isSharedCheck_385_ == 0 {
                        v___x_380_ = v___x_347_;
                        v_isShared_381_ = v_isSharedCheck_385_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_378_);
                        crate::leanh::lean_dec(v___x_347_);
                        v___x_380_ = crate::leanh::lean_box(0);
                        v_isShared_381_ = v_isSharedCheck_385_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_348_) == 0 {
                    crate::leanh::lean_del_object(v___x_345_);
                    v_a_352_ = crate::leanh::lean_ctor_get(v_a_348_, 0);
                    v_isSharedCheck_362_ = (!crate::leanh::lean_is_exclusive(v_a_348_)) as u8;
                    if v_isSharedCheck_362_ == 0 {
                        v___x_354_ = v_a_348_;
                        v_isShared_355_ = v_isSharedCheck_362_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_352_);
                        crate::leanh::lean_dec(v_a_348_);
                        v___x_354_ = crate::leanh::lean_box(0);
                        v_isShared_355_ = v_isSharedCheck_362_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_363_ = crate::leanh::lean_ctor_get(v_a_348_, 0);
                    v_isSharedCheck_376_ = (!crate::leanh::lean_is_exclusive(v_a_348_)) as u8;
                    if v_isSharedCheck_376_ == 0 {
                        v___x_365_ = v_a_348_;
                        v_isShared_366_ = v_isSharedCheck_376_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_363_);
                        crate::leanh::lean_dec(v_a_348_);
                        v___x_365_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_352_);
                    v___x_357_ = v_reuseFailAlloc_361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_350_, 0, v___x_357_);
                    v___x_359_ = v___x_350_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
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
                    crate::leanh::lean_ctor_set(v___x_345_, 0, v_a_363_);
                    v___x_368_ = v___x_345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_363_);
                    v___x_368_ = v_reuseFailAlloc_375_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_365_, 0, v___x_368_);
                    v___x_370_ = v___x_365_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
                    v___x_370_ = v_reuseFailAlloc_374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_350_, 0, v___x_370_);
                    v___x_372_ = v___x_350_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
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
                    v_reuseFailAlloc_384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
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
                    v_reuseFailAlloc_398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
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
    mut v_g_400_: *mut crate::leanh::LeanObject,
    mut v_ctx_401_: *mut crate::leanh::LeanObject,
    mut v_a_402_: *mut crate::leanh::LeanObject,
    mut v_a_403_: *mut crate::leanh::LeanObject,
    mut v_a_404_: *mut crate::leanh::LeanObject,
    mut v_a_405_: *mut crate::leanh::LeanObject,
    mut v_a_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_407_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
        v_g_400_, v_ctx_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_,
    );
    crate::leanh::lean_dec(v_a_405_);
    crate::leanh::lean_dec_ref(v_a_404_);
    crate::leanh::lean_dec(v_a_403_);
    crate::leanh::lean_dec_ref(v_a_402_);
    return v_res_407_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(
    mut v_msgData_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_414_ = lean_st_ref_get(v___y_412_);
    v_env_415_ = crate::leanh::lean_ctor_get(v___x_414_, 0);
    crate::leanh::lean_inc_ref(v_env_415_);
    crate::leanh::lean_dec(v___x_414_);
    v___x_416_ = lean_st_ref_get(v___y_410_);
    v_mctx_417_ = crate::leanh::lean_ctor_get(v___x_416_, 0);
    crate::leanh::lean_inc_ref(v_mctx_417_);
    crate::leanh::lean_dec(v___x_416_);
    v_lctx_418_ = crate::leanh::lean_ctor_get(v___y_409_, 2);
    v_options_419_ = crate::leanh::lean_ctor_get(v___y_411_, 2);
    crate::leanh::lean_inc_ref(v_options_419_);
    crate::leanh::lean_inc_ref(v_lctx_418_);
    v___x_420_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_420_, 0, v_env_415_);
    crate::leanh::lean_ctor_set(v___x_420_, 1, v_mctx_417_);
    crate::leanh::lean_ctor_set(v___x_420_, 2, v_lctx_418_);
    crate::leanh::lean_ctor_set(v___x_420_, 3, v_options_419_);
    v___x_421_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
    crate::leanh::lean_ctor_set(v___x_421_, 1, v_msgData_408_);
    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
    return v___x_422_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0___boxed(
    mut v_msgData_423_: *mut crate::leanh::LeanObject,
    mut v___y_424_: *mut crate::leanh::LeanObject,
    mut v___y_425_: *mut crate::leanh::LeanObject,
    mut v___y_426_: *mut crate::leanh::LeanObject,
    mut v___y_427_: *mut crate::leanh::LeanObject,
    mut v___y_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(
        v_msgData_423_,
        v___y_424_,
        v___y_425_,
        v___y_426_,
        v___y_427_,
    );
    crate::leanh::lean_dec(v___y_427_);
    crate::leanh::lean_dec_ref(v___y_426_);
    crate::leanh::lean_dec(v___y_425_);
    crate::leanh::lean_dec_ref(v___y_424_);
    return v_res_429_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(
    mut v_mvarId_430_: *mut crate::leanh::LeanObject,
    mut v_x_431_: *mut crate::leanh::LeanObject,
    mut v___y_432_: *mut crate::leanh::LeanObject,
    mut v___y_433_: *mut crate::leanh::LeanObject,
    mut v___y_434_: *mut crate::leanh::LeanObject,
    mut v___y_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_441_: u8 = 0;
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_a_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_437_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_430_,
                    v_x_431_,
                    v___y_432_,
                    v___y_433_,
                    v___y_434_,
                    v___y_435_,
                );
                if crate::leanh::lean_obj_tag(v___x_437_) == 0 {
                    v_a_438_ = crate::leanh::lean_ctor_get(v___x_437_, 0);
                    v_isSharedCheck_445_ = (!crate::leanh::lean_is_exclusive(v___x_437_)) as u8;
                    if v_isSharedCheck_445_ == 0 {
                        v___x_440_ = v___x_437_;
                        v_isShared_441_ = v_isSharedCheck_445_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_438_);
                        crate::leanh::lean_dec(v___x_437_);
                        v___x_440_ = crate::leanh::lean_box(0);
                        v_isShared_441_ = v_isSharedCheck_445_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_446_ = crate::leanh::lean_ctor_get(v___x_437_, 0);
                    v_isSharedCheck_453_ = (!crate::leanh::lean_is_exclusive(v___x_437_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_448_ = v___x_437_;
                        v_isShared_449_ = v_isSharedCheck_453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_446_);
                        crate::leanh::lean_dec(v___x_437_);
                        v___x_448_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
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
                    v_reuseFailAlloc_452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
    mut v_mvarId_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
    mut v___y_456_: *mut crate::leanh::LeanObject,
    mut v___y_457_: *mut crate::leanh::LeanObject,
    mut v___y_458_: *mut crate::leanh::LeanObject,
    mut v___y_459_: *mut crate::leanh::LeanObject,
    mut v___y_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(
            v_mvarId_454_,
            v_x_455_,
            v___y_456_,
            v___y_457_,
            v___y_458_,
            v___y_459_,
        );
    crate::leanh::lean_dec(v___y_459_);
    crate::leanh::lean_dec_ref(v___y_458_);
    crate::leanh::lean_dec(v___y_457_);
    crate::leanh::lean_dec_ref(v___y_456_);
    return v_res_461_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(
    mut v_00_u03b1_462_: *mut crate::leanh::LeanObject,
    mut v_mvarId_463_: *mut crate::leanh::LeanObject,
    mut v_x_464_: *mut crate::leanh::LeanObject,
    mut v___y_465_: *mut crate::leanh::LeanObject,
    mut v___y_466_: *mut crate::leanh::LeanObject,
    mut v___y_467_: *mut crate::leanh::LeanObject,
    mut v___y_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_471_: *mut crate::leanh::LeanObject,
    mut v_mvarId_472_: *mut crate::leanh::LeanObject,
    mut v_x_473_: *mut crate::leanh::LeanObject,
    mut v___y_474_: *mut crate::leanh::LeanObject,
    mut v___y_475_: *mut crate::leanh::LeanObject,
    mut v___y_476_: *mut crate::leanh::LeanObject,
    mut v___y_477_: *mut crate::leanh::LeanObject,
    mut v___y_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2(
        v_00_u03b1_471_,
        v_mvarId_472_,
        v_x_473_,
        v___y_474_,
        v___y_475_,
        v___y_476_,
        v___y_477_,
    );
    crate::leanh::lean_dec(v___y_477_);
    crate::leanh::lean_dec_ref(v___y_476_);
    crate::leanh::lean_dec(v___y_475_);
    crate::leanh::lean_dec_ref(v___y_474_);
    return v_res_479_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
    mut v_msg_480_: *mut crate::leanh::LeanObject,
    mut v___y_481_: *mut crate::leanh::LeanObject,
    mut v___y_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_486_ = crate::leanh::lean_ctor_get(v___y_483_, 5);
                v___x_487_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
                v_a_488_ = crate::leanh::lean_ctor_get(v___x_487_, 0);
                v_isSharedCheck_496_ = (!crate::leanh::lean_is_exclusive(v___x_487_)) as u8;
                if v_isSharedCheck_496_ == 0 {
                    v___x_490_ = v___x_487_;
                    v_isShared_491_ = v_isSharedCheck_496_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_488_);
                    crate::leanh::lean_dec(v___x_487_);
                    v___x_490_ = crate::leanh::lean_box(0);
                    v_isShared_491_ = v_isSharedCheck_496_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_486_);
                v___x_492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_492_, 0, v_ref_486_);
                crate::leanh::lean_ctor_set(v___x_492_, 1, v_a_488_);
                if v_isShared_491_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_490_, 1);
                    crate::leanh::lean_ctor_set(v___x_490_, 0, v___x_492_);
                    v___x_494_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
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
    mut v_msg_497_: *mut crate::leanh::LeanObject,
    mut v___y_498_: *mut crate::leanh::LeanObject,
    mut v___y_499_: *mut crate::leanh::LeanObject,
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
    mut v___y_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
        v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_,
    );
    crate::leanh::lean_dec(v___y_501_);
    crate::leanh::lean_dec_ref(v___y_500_);
    crate::leanh::lean_dec(v___y_499_);
    crate::leanh::lean_dec_ref(v___y_498_);
    return v_res_503_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(
    mut v_a_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
    mut v___y_507_: *mut crate::leanh::LeanObject,
    mut v___y_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_510_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(
                    v_a_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_,
                );
                if crate::leanh::lean_obj_tag(v___x_510_) == 0 {
                    v_a_511_ = crate::leanh::lean_ctor_get(v___x_510_, 0);
                    crate::leanh::lean_inc(v_a_511_);
                    crate::leanh::lean_dec_ref_known(v___x_510_, 1);
                    v___x_512_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__0(v_a_511_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
                    v_a_513_ = crate::leanh::lean_ctor_get(v___x_512_, 0);
                    crate::leanh::lean_inc(v_a_513_);
                    crate::leanh::lean_dec_ref(v___x_512_);
                    v___x_514_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(v_a_513_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
                    return v___x_514_;
                } else {
                    v_a_515_ = crate::leanh::lean_ctor_get(v___x_510_, 0);
                    v_isSharedCheck_522_ = (!crate::leanh::lean_is_exclusive(v___x_510_)) as u8;
                    if v_isSharedCheck_522_ == 0 {
                        v___x_517_ = v___x_510_;
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_515_);
                        crate::leanh::lean_dec(v___x_510_);
                        v___x_517_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
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
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
    mut v___y_527_: *mut crate::leanh::LeanObject,
    mut v___y_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0(
        v_a_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_,
    );
    crate::leanh::lean_dec(v___y_527_);
    crate::leanh::lean_dec_ref(v___y_526_);
    crate::leanh::lean_dec(v___y_525_);
    crate::leanh::lean_dec_ref(v___y_524_);
    return v_res_529_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_bvDecide(
    mut v_g_530_: *mut crate::leanh::LeanObject,
    mut v_ctx_531_: *mut crate::leanh::LeanObject,
    mut v_a_532_: *mut crate::leanh::LeanObject,
    mut v_a_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v_a_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v_a_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_537_ = l_Lean_Meta_Tactic_BVDecide_bvDecide_x27(
                    v_g_530_, v_ctx_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_,
                );
                if crate::leanh::lean_obj_tag(v___x_537_) == 0 {
                    v_a_538_ = crate::leanh::lean_ctor_get(v___x_537_, 0);
                    v_isSharedCheck_550_ = (!crate::leanh::lean_is_exclusive(v___x_537_)) as u8;
                    if v_isSharedCheck_550_ == 0 {
                        v___x_540_ = v___x_537_;
                        v_isShared_541_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_538_);
                        crate::leanh::lean_dec(v___x_537_);
                        v___x_540_ = crate::leanh::lean_box(0);
                        v_isShared_541_ = v_isSharedCheck_550_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_551_ = crate::leanh::lean_ctor_get(v___x_537_, 0);
                    v_isSharedCheck_558_ = (!crate::leanh::lean_is_exclusive(v___x_537_)) as u8;
                    if v_isSharedCheck_558_ == 0 {
                        v___x_553_ = v___x_537_;
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_551_);
                        crate::leanh::lean_dec(v___x_537_);
                        v___x_553_ = crate::leanh::lean_box(0);
                        v_isShared_554_ = v_isSharedCheck_558_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_538_) == 0 {
                    crate::leanh::lean_del_object(v___x_540_);
                    v_a_542_ = crate::leanh::lean_ctor_get(v_a_538_, 0);
                    crate::leanh::lean_inc(v_a_542_);
                    crate::leanh::lean_dec_ref_known(v_a_538_, 1);
                    v_goal_543_ = crate::leanh::lean_ctor_get(v_a_542_, 0);
                    crate::leanh::lean_inc(v_goal_543_);
                    v___f_544_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_bvDecide___lam__0___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_544_, 0, v_a_542_);
                    v___x_545_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__2___redArg(v_goal_543_, v___f_544_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
                    return v___x_545_;
                } else {
                    v_a_546_ = crate::leanh::lean_ctor_get(v_a_538_, 0);
                    crate::leanh::lean_inc(v_a_546_);
                    crate::leanh::lean_dec_ref_known(v_a_538_, 1);
                    if v_isShared_541_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_540_, 0, v_a_546_);
                        v___x_548_ = v___x_540_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_549_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_546_);
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
                    v_reuseFailAlloc_557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
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
    mut v_g_559_: *mut crate::leanh::LeanObject,
    mut v_ctx_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(
        v_g_559_, v_ctx_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_,
    );
    crate::leanh::lean_dec(v_a_564_);
    crate::leanh::lean_dec_ref(v_a_563_);
    crate::leanh::lean_dec(v_a_562_);
    crate::leanh::lean_dec_ref(v_a_561_);
    return v_res_566_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_msg_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___redArg(
        v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_,
    );
    return v___x_574_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1___boxed(
    mut v_00_u03b1_575_: *mut crate::leanh::LeanObject,
    mut v_msg_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_bvDecide_spec__1(
        v_00_u03b1_575_,
        v_msg_576_,
        v___y_577_,
        v___y_578_,
        v___y_579_,
        v___y_580_,
    );
    crate::leanh::lean_dec(v___y_580_);
    crate::leanh::lean_dec_ref(v___y_579_);
    crate::leanh::lean_dec(v___y_578_);
    crate::leanh::lean_dec_ref(v___y_577_);
    return v_res_582_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
}
