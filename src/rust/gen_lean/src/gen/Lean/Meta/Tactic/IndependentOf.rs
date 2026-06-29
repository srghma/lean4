// Lean compiler output
// Module: Lean.Meta.Tactic.IndependentOf
// Imports: Lean.Meta.CollectMVars Lean.Meta.Tactic.Util
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_infer_type, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isProp, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::CollectMVars::{
    initialize_Lean_Meta_CollectMVars, l_Lean_MVarId_getMVarDependencies,
    runtime_initialize_Lean_Meta_CollectMVars,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_getType, l_Lean_MVarId_isSubsingleton,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(
    mut v_e_276_: *mut crate::leanh::LeanObject,
    mut v___y_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_279_: u8 = 0;
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_293_: u8 = 0;
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut v_unused_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_279_ = l_Lean_Expr_hasMVar(v_e_276_);
                if v___x_279_ == 0 {
                    v___x_280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_280_, 0, v_e_276_);
                    return v___x_280_;
                } else {
                    v___x_281_ = lean_st_ref_get(v___y_277_);
                    v_mctx_282_ = crate::leanh::lean_ctor_get(v___x_281_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_282_);
                    crate::leanh::lean_dec(v___x_281_);
                    v___x_283_ = l_Lean_instantiateMVarsCore(v_mctx_282_, v_e_276_);
                    v_fst_284_ = crate::leanh::lean_ctor_get(v___x_283_, 0);
                    crate::leanh::lean_inc(v_fst_284_);
                    v_snd_285_ = crate::leanh::lean_ctor_get(v___x_283_, 1);
                    crate::leanh::lean_inc(v_snd_285_);
                    crate::leanh::lean_dec_ref(v___x_283_);
                    v___x_286_ = lean_st_ref_take(v___y_277_);
                    v_cache_287_ = crate::leanh::lean_ctor_get(v___x_286_, 1);
                    v_zetaDeltaFVarIds_288_ = crate::leanh::lean_ctor_get(v___x_286_, 2);
                    v_postponed_289_ = crate::leanh::lean_ctor_get(v___x_286_, 3);
                    v_diag_290_ = crate::leanh::lean_ctor_get(v___x_286_, 4);
                    v_isSharedCheck_299_ = (!crate::leanh::lean_is_exclusive(v___x_286_)) as u8;
                    if v_isSharedCheck_299_ == 0 {
                        v_unused_300_ = crate::leanh::lean_ctor_get(v___x_286_, 0);
                        crate::leanh::lean_dec(v_unused_300_);
                        v___x_292_ = v___x_286_;
                        v_isShared_293_ = v_isSharedCheck_299_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_290_);
                        crate::leanh::lean_inc(v_postponed_289_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_288_);
                        crate::leanh::lean_inc(v_cache_287_);
                        crate::leanh::lean_dec(v___x_286_);
                        v___x_292_ = crate::leanh::lean_box(0);
                        v_isShared_293_ = v_isSharedCheck_299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_292_, 0, v_snd_285_);
                    v___x_295_ = v___x_292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 0, v_snd_285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 1, v_cache_287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 2, v_zetaDeltaFVarIds_288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 3, v_postponed_289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 4, v_diag_290_);
                    v___x_295_ = v_reuseFailAlloc_298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_296_ = lean_st_ref_set(v___y_277_, v___x_295_);
                v___x_297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_297_, 0, v_fst_284_);
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(
    mut v_e_301_: *mut crate::leanh::LeanObject,
    mut v___y_302_: *mut crate::leanh::LeanObject,
    mut v___y_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(
        v_e_301_, v___y_302_,
    );
    crate::leanh::lean_dec(v___y_302_);
    return v_res_304_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(
    mut v_e_305_: *mut crate::leanh::LeanObject,
    mut v___y_306_: *mut crate::leanh::LeanObject,
    mut v___y_307_: *mut crate::leanh::LeanObject,
    mut v___y_308_: *mut crate::leanh::LeanObject,
    mut v___y_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(
        v_e_305_, v___y_307_,
    );
    return v___x_311_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(
    mut v_e_312_: *mut crate::leanh::LeanObject,
    mut v___y_313_: *mut crate::leanh::LeanObject,
    mut v___y_314_: *mut crate::leanh::LeanObject,
    mut v___y_315_: *mut crate::leanh::LeanObject,
    mut v___y_316_: *mut crate::leanh::LeanObject,
    mut v___y_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(
        v_e_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_,
    );
    crate::leanh::lean_dec(v___y_316_);
    crate::leanh::lean_dec_ref(v___y_315_);
    crate::leanh::lean_dec(v___y_314_);
    crate::leanh::lean_dec_ref(v___y_313_);
    return v_res_318_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
    mut v_mvarId_319_: *mut crate::leanh::LeanObject,
    mut v_x_320_: *mut crate::leanh::LeanObject,
    mut v___y_321_: *mut crate::leanh::LeanObject,
    mut v___y_322_: *mut crate::leanh::LeanObject,
    mut v___y_323_: *mut crate::leanh::LeanObject,
    mut v___y_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_330_: u8 = 0;
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_334_: u8 = 0;
    let mut v_a_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_319_,
                    v_x_320_,
                    v___y_321_,
                    v___y_322_,
                    v___y_323_,
                    v___y_324_,
                );
                if crate::leanh::lean_obj_tag(v___x_326_) == 0 {
                    v_a_327_ = crate::leanh::lean_ctor_get(v___x_326_, 0);
                    v_isSharedCheck_334_ = (!crate::leanh::lean_is_exclusive(v___x_326_)) as u8;
                    if v_isSharedCheck_334_ == 0 {
                        v___x_329_ = v___x_326_;
                        v_isShared_330_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_327_);
                        crate::leanh::lean_dec(v___x_326_);
                        v___x_329_ = crate::leanh::lean_box(0);
                        v_isShared_330_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_335_ = crate::leanh::lean_ctor_get(v___x_326_, 0);
                    v_isSharedCheck_342_ = (!crate::leanh::lean_is_exclusive(v___x_326_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_337_ = v___x_326_;
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_335_);
                        crate::leanh::lean_dec(v___x_326_);
                        v___x_337_ = crate::leanh::lean_box(0);
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_330_ == 0 {
                    v___x_332_ = v___x_329_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
                    v___x_332_ = v_reuseFailAlloc_333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_332_;
            }
            3 => {
                if v_isShared_338_ == 0 {
                    v___x_340_ = v___x_337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
                    v___x_340_ = v_reuseFailAlloc_341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg___boxed(
    mut v_mvarId_343_: *mut crate::leanh::LeanObject,
    mut v_x_344_: *mut crate::leanh::LeanObject,
    mut v___y_345_: *mut crate::leanh::LeanObject,
    mut v___y_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
    mut v___y_348_: *mut crate::leanh::LeanObject,
    mut v___y_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
        v_mvarId_343_,
        v_x_344_,
        v___y_345_,
        v___y_346_,
        v___y_347_,
        v___y_348_,
    );
    crate::leanh::lean_dec(v___y_348_);
    crate::leanh::lean_dec_ref(v___y_347_);
    crate::leanh::lean_dec(v___y_346_);
    crate::leanh::lean_dec_ref(v___y_345_);
    return v_res_350_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(
    mut v_00_u03b1_351_: *mut crate::leanh::LeanObject,
    mut v_mvarId_352_: *mut crate::leanh::LeanObject,
    mut v_x_353_: *mut crate::leanh::LeanObject,
    mut v___y_354_: *mut crate::leanh::LeanObject,
    mut v___y_355_: *mut crate::leanh::LeanObject,
    mut v___y_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
        v_mvarId_352_,
        v_x_353_,
        v___y_354_,
        v___y_355_,
        v___y_356_,
        v___y_357_,
    );
    return v___x_359_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___boxed(
    mut v_00_u03b1_360_: *mut crate::leanh::LeanObject,
    mut v_mvarId_361_: *mut crate::leanh::LeanObject,
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v___y_363_: *mut crate::leanh::LeanObject,
    mut v___y_364_: *mut crate::leanh::LeanObject,
    mut v___y_365_: *mut crate::leanh::LeanObject,
    mut v___y_366_: *mut crate::leanh::LeanObject,
    mut v___y_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(
        v_00_u03b1_360_,
        v_mvarId_361_,
        v_x_362_,
        v___y_363_,
        v___y_364_,
        v___y_365_,
        v___y_366_,
    );
    crate::leanh::lean_dec(v___y_366_);
    crate::leanh::lean_dec_ref(v___y_365_);
    crate::leanh::lean_dec(v___y_364_);
    crate::leanh::lean_dec_ref(v___y_363_);
    return v_res_368_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(
    mut v_a_369_: *mut crate::leanh::LeanObject,
    mut v_x_370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_371_: u8 = 0;
    let mut v_key_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_370_) == 0 {
                    v___x_371_ = 0;
                    return v___x_371_;
                } else {
                    v_key_372_ = crate::leanh::lean_ctor_get(v_x_370_, 0);
                    v_tail_373_ = crate::leanh::lean_ctor_get(v_x_370_, 2);
                    v___x_374_ = l_Lean_instBEqMVarId_beq(v_key_372_, v_a_369_);
                    if v___x_374_ == 0 {
                        v_x_370_ = v_tail_373_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_374_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg___boxed(
    mut v_a_376_: *mut crate::leanh::LeanObject,
    mut v_x_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_378_: u8 = 0;
    let mut v_r_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_376_, v_x_377_);
    crate::leanh::lean_dec(v_x_377_);
    crate::leanh::lean_dec(v_a_376_);
    v_r_379_ = crate::leanh::lean_box((v_res_378_) as usize);
    return v_r_379_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(
    mut v_m_380_: *mut crate::leanh::LeanObject,
    mut v_a_381_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: u64 = 0;
    let mut v___x_385_: u64 = 0;
    let mut v___x_386_: u64 = 0;
    let mut v_fold_387_: u64 = 0;
    let mut v___x_388_: u64 = 0;
    let mut v___x_389_: u64 = 0;
    let mut v___x_390_: u64 = 0;
    let mut v___x_391_: usize = 0;
    let mut v___x_392_: usize = 0;
    let mut v___x_393_: usize = 0;
    let mut v___x_394_: usize = 0;
    let mut v___x_395_: usize = 0;
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: u8 = 0;
    v_buckets_382_ = crate::leanh::lean_ctor_get(v_m_380_, 1);
    v___x_383_ = lean_array_get_size(v_buckets_382_);
    v___x_384_ = l_Lean_instHashableMVarId_hash(v_a_381_);
    v___x_385_ = 32u64;
    v___x_386_ = lean_uint64_shift_right(v___x_384_, v___x_385_);
    v_fold_387_ = lean_uint64_xor(v___x_384_, v___x_386_);
    v___x_388_ = 16u64;
    v___x_389_ = lean_uint64_shift_right(v_fold_387_, v___x_388_);
    v___x_390_ = lean_uint64_xor(v_fold_387_, v___x_389_);
    v___x_391_ = lean_uint64_to_usize(v___x_390_);
    v___x_392_ = lean_usize_of_nat(v___x_383_);
    v___x_393_ = 1usize;
    v___x_394_ = lean_usize_sub(v___x_392_, v___x_393_);
    v___x_395_ = lean_usize_land(v___x_391_, v___x_394_);
    v___x_396_ = lean_array_uget_borrowed(v_buckets_382_, v___x_395_);
    v___x_397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_381_, v___x_396_);
    return v___x_397_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg___boxed(
    mut v_m_398_: *mut crate::leanh::LeanObject,
    mut v_a_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: u8 = 0;
    let mut v_r_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_398_, v_a_399_);
    crate::leanh::lean_dec(v_a_399_);
    crate::leanh::lean_dec_ref(v_m_398_);
    v_r_401_ = crate::leanh::lean_box((v_res_400_) as usize);
    return v_r_401_;
}
pub unsafe fn l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
    mut v_a_402_: u8,
    mut v_g_403_: *mut crate::leanh::LeanObject,
    mut v_x_404_: *mut crate::leanh::LeanObject,
    mut v___y_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_410_: u8 = 0;
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_419_: u8 = 0;
    let mut v___x_420_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_a_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_404_) == 0 {
                    v___x_410_ = 1;
                    v___x_411_ = crate::leanh::lean_box((v___x_410_) as usize);
                    v___x_412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_412_, 0, v___x_411_);
                    return v___x_412_;
                } else {
                    v_head_413_ = crate::leanh::lean_ctor_get(v_x_404_, 0);
                    crate::leanh::lean_inc(v_head_413_);
                    v_tail_414_ = crate::leanh::lean_ctor_get(v_x_404_, 1);
                    crate::leanh::lean_inc(v_tail_414_);
                    crate::leanh::lean_dec_ref_known(v_x_404_, 2);
                    v___x_415_ = l_Lean_MVarId_getMVarDependencies(
                        v_head_413_,
                        v_a_402_,
                        v___y_405_,
                        v___y_406_,
                        v___y_407_,
                        v___y_408_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_415_) == 0 {
                        v_a_416_ = crate::leanh::lean_ctor_get(v___x_415_, 0);
                        v_isSharedCheck_427_ = (!crate::leanh::lean_is_exclusive(v___x_415_)) as u8;
                        if v_isSharedCheck_427_ == 0 {
                            v___x_418_ = v___x_415_;
                            v_isShared_419_ = v_isSharedCheck_427_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_416_);
                            crate::leanh::lean_dec(v___x_415_);
                            v___x_418_ = crate::leanh::lean_box(0);
                            v_isShared_419_ = v_isSharedCheck_427_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_414_);
                        v_a_428_ = crate::leanh::lean_ctor_get(v___x_415_, 0);
                        v_isSharedCheck_435_ = (!crate::leanh::lean_is_exclusive(v___x_415_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v___x_430_ = v___x_415_;
                            v_isShared_431_ = v_isSharedCheck_435_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_428_);
                            crate::leanh::lean_dec(v___x_415_);
                            v___x_430_ = crate::leanh::lean_box(0);
                            v_isShared_431_ = v_isSharedCheck_435_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_a_416_, v_g_403_);
                crate::leanh::lean_dec(v_a_416_);
                if v___x_420_ == 0 {
                    crate::leanh::lean_del_object(v___x_418_);
                    v_x_404_ = v_tail_414_;
                    state = 0;
                    continue;
                } else {
                    if v_a_402_ == 0 {
                        crate::leanh::lean_dec(v_tail_414_);
                        v___x_422_ = crate::leanh::lean_box((v_a_402_) as usize);
                        if v_isShared_419_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_418_, 0, v___x_422_);
                            v___x_424_ = v___x_418_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
                            v___x_424_ = v_reuseFailAlloc_425_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_418_);
                        v_x_404_ = v_tail_414_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_424_;
            }
            3 => {
                if v_isShared_431_ == 0 {
                    v___x_433_ = v___x_430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
                    v___x_433_ = v_reuseFailAlloc_434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2___boxed(
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_g_437_: *mut crate::leanh::LeanObject,
    mut v_x_438_: *mut crate::leanh::LeanObject,
    mut v___y_439_: *mut crate::leanh::LeanObject,
    mut v___y_440_: *mut crate::leanh::LeanObject,
    mut v___y_441_: *mut crate::leanh::LeanObject,
    mut v___y_442_: *mut crate::leanh::LeanObject,
    mut v___y_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2521__boxed_444_: u8 = 0;
    let mut v_res_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_2521__boxed_444_ = (crate::leanh::lean_unbox(v_a_436_) as u8);
    v_res_445_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
        v_a_2521__boxed_444_,
        v_g_437_,
        v_x_438_,
        v___y_439_,
        v___y_440_,
        v___y_441_,
        v___y_442_,
    );
    crate::leanh::lean_dec(v___y_442_);
    crate::leanh::lean_dec_ref(v___y_441_);
    crate::leanh::lean_dec(v___y_440_);
    crate::leanh::lean_dec_ref(v___y_439_);
    crate::leanh::lean_dec(v_g_437_);
    return v_res_445_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf___lam__0(
    mut v_g_446_: *mut crate::leanh::LeanObject,
    mut v_L_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v___y_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
    mut v___y_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: u8 = 0;
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_465_: u8 = 0;
    let mut v___x_466_: u8 = 0;
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: u8 = 0;
    let mut v___x_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_a_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_489_: u8 = 0;
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_493_: u8 = 0;
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_a_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_g_446_);
                v___x_453_ =
                    l_Lean_MVarId_getType(v_g_446_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
                if crate::leanh::lean_obj_tag(v___x_453_) == 0 {
                    v_a_454_ = crate::leanh::lean_ctor_get(v___x_453_, 0);
                    crate::leanh::lean_inc(v_a_454_);
                    crate::leanh::lean_dec_ref_known(v___x_453_, 1);
                    v___x_455_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_a_454_, v___y_449_);
                    v_a_456_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
                    v_isSharedCheck_499_ = (!crate::leanh::lean_is_exclusive(v___x_455_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_458_ = v___x_455_;
                        v_isShared_459_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_456_);
                        crate::leanh::lean_dec(v___x_455_);
                        v___x_458_ = crate::leanh::lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_451_);
                    crate::leanh::lean_dec_ref(v___y_450_);
                    crate::leanh::lean_dec(v___y_449_);
                    crate::leanh::lean_dec_ref(v___y_448_);
                    crate::leanh::lean_dec(v_L_447_);
                    crate::leanh::lean_dec(v_g_446_);
                    v_a_500_ = crate::leanh::lean_ctor_get(v___x_453_, 0);
                    v_isSharedCheck_507_ = (!crate::leanh::lean_is_exclusive(v___x_453_)) as u8;
                    if v_isSharedCheck_507_ == 0 {
                        v___x_502_ = v___x_453_;
                        v_isShared_503_ = v_isSharedCheck_507_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_500_);
                        crate::leanh::lean_dec(v___x_453_);
                        v___x_502_ = crate::leanh::lean_box(0);
                        v_isShared_503_ = v_isSharedCheck_507_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_460_ = l_Lean_Expr_hasExprMVar(v_a_456_);
                if v___x_460_ == 0 {
                    crate::leanh::lean_del_object(v___x_458_);
                    crate::leanh::lean_inc(v___y_451_);
                    crate::leanh::lean_inc_ref(v___y_450_);
                    crate::leanh::lean_inc(v___y_449_);
                    crate::leanh::lean_inc_ref(v___y_448_);
                    v___x_461_ =
                        lean_infer_type(v_a_456_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
                    if crate::leanh::lean_obj_tag(v___x_461_) == 0 {
                        v_a_462_ = crate::leanh::lean_ctor_get(v___x_461_, 0);
                        v_isSharedCheck_485_ = (!crate::leanh::lean_is_exclusive(v___x_461_)) as u8;
                        if v_isSharedCheck_485_ == 0 {
                            v___x_464_ = v___x_461_;
                            v_isShared_465_ = v_isSharedCheck_485_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_462_);
                            crate::leanh::lean_dec(v___x_461_);
                            v___x_464_ = crate::leanh::lean_box(0);
                            v_isShared_465_ = v_isSharedCheck_485_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_451_);
                        crate::leanh::lean_dec_ref(v___y_450_);
                        crate::leanh::lean_dec(v___y_449_);
                        crate::leanh::lean_dec_ref(v___y_448_);
                        crate::leanh::lean_dec(v_L_447_);
                        crate::leanh::lean_dec(v_g_446_);
                        v_a_486_ = crate::leanh::lean_ctor_get(v___x_461_, 0);
                        v_isSharedCheck_493_ = (!crate::leanh::lean_is_exclusive(v___x_461_)) as u8;
                        if v_isSharedCheck_493_ == 0 {
                            v___x_488_ = v___x_461_;
                            v_isShared_489_ = v_isSharedCheck_493_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_486_);
                            crate::leanh::lean_dec(v___x_461_);
                            v___x_488_ = crate::leanh::lean_box(0);
                            v_isShared_489_ = v_isSharedCheck_493_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_456_);
                    crate::leanh::lean_dec(v___y_451_);
                    crate::leanh::lean_dec_ref(v___y_450_);
                    crate::leanh::lean_dec(v___y_449_);
                    crate::leanh::lean_dec_ref(v___y_448_);
                    crate::leanh::lean_dec(v_L_447_);
                    crate::leanh::lean_dec(v_g_446_);
                    v___x_494_ = 0;
                    v___x_495_ = crate::leanh::lean_box((v___x_494_) as usize);
                    if v_isShared_459_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_495_);
                        v___x_497_ = v___x_458_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
                        v___x_497_ = v_reuseFailAlloc_498_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_466_ = 1;
                v___x_467_ = l_Lean_Expr_isProp(v_a_462_);
                crate::leanh::lean_dec(v_a_462_);
                if v___x_467_ == 0 {
                    crate::leanh::lean_del_object(v___x_464_);
                    crate::leanh::lean_inc(v_g_446_);
                    v___x_468_ = l_Lean_MVarId_isSubsingleton(
                        v_g_446_, v___y_448_, v___y_449_, v___y_450_, v___y_451_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_468_) == 0 {
                        v_a_469_ = crate::leanh::lean_ctor_get(v___x_468_, 0);
                        v_isSharedCheck_480_ = (!crate::leanh::lean_is_exclusive(v___x_468_)) as u8;
                        if v_isSharedCheck_480_ == 0 {
                            v___x_471_ = v___x_468_;
                            v_isShared_472_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_469_);
                            crate::leanh::lean_dec(v___x_468_);
                            v___x_471_ = crate::leanh::lean_box(0);
                            v_isShared_472_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_451_);
                        crate::leanh::lean_dec_ref(v___y_450_);
                        crate::leanh::lean_dec(v___y_449_);
                        crate::leanh::lean_dec_ref(v___y_448_);
                        crate::leanh::lean_dec(v_L_447_);
                        crate::leanh::lean_dec(v_g_446_);
                        return v___x_468_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_451_);
                    crate::leanh::lean_dec_ref(v___y_450_);
                    crate::leanh::lean_dec(v___y_449_);
                    crate::leanh::lean_dec_ref(v___y_448_);
                    crate::leanh::lean_dec(v_L_447_);
                    crate::leanh::lean_dec(v_g_446_);
                    v___x_481_ = crate::leanh::lean_box((v___x_466_) as usize);
                    if v_isShared_465_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_464_, 0, v___x_481_);
                        v___x_483_ = v___x_464_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
                        v___x_483_ = v_reuseFailAlloc_484_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_473_ = (crate::leanh::lean_unbox(v_a_469_) as u8);
                if v___x_473_ == 0 {
                    crate::leanh::lean_del_object(v___x_471_);
                    v___x_474_ = (crate::leanh::lean_unbox(v_a_469_) as u8);
                    crate::leanh::lean_dec(v_a_469_);
                    v___x_475_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
                        v___x_474_, v_g_446_, v_L_447_, v___y_448_, v___y_449_, v___y_450_,
                        v___y_451_,
                    );
                    crate::leanh::lean_dec(v___y_451_);
                    crate::leanh::lean_dec_ref(v___y_450_);
                    crate::leanh::lean_dec(v___y_449_);
                    crate::leanh::lean_dec_ref(v___y_448_);
                    crate::leanh::lean_dec(v_g_446_);
                    return v___x_475_;
                } else {
                    crate::leanh::lean_dec(v_a_469_);
                    crate::leanh::lean_dec(v___y_451_);
                    crate::leanh::lean_dec_ref(v___y_450_);
                    crate::leanh::lean_dec(v___y_449_);
                    crate::leanh::lean_dec_ref(v___y_448_);
                    crate::leanh::lean_dec(v_L_447_);
                    crate::leanh::lean_dec(v_g_446_);
                    v___x_476_ = crate::leanh::lean_box((v___x_466_) as usize);
                    if v_isShared_472_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_471_, 0, v___x_476_);
                        v___x_478_ = v___x_471_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
                        v___x_478_ = v_reuseFailAlloc_479_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_478_;
            }
            5 => {
                return v___x_483_;
            }
            6 => {
                if v_isShared_489_ == 0 {
                    v___x_491_ = v___x_488_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
                    v___x_491_ = v_reuseFailAlloc_492_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_491_;
            }
            8 => {
                return v___x_497_;
            }
            9 => {
                if v_isShared_503_ == 0 {
                    v___x_505_ = v___x_502_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
                    v___x_505_ = v_reuseFailAlloc_506_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_isIndependentOf___lam__0___boxed(
    mut v_g_508_: *mut crate::leanh::LeanObject,
    mut v_L_509_: *mut crate::leanh::LeanObject,
    mut v___y_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Lean_MVarId_isIndependentOf___lam__0(
        v_g_508_, v_L_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_,
    );
    return v_res_515_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf(
    mut v_L_516_: *mut crate::leanh::LeanObject,
    mut v_g_517_: *mut crate::leanh::LeanObject,
    mut v_a_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
    mut v_a_520_: *mut crate::leanh::LeanObject,
    mut v_a_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_g_517_);
    v___f_523_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_isIndependentOf___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_523_, 0, v_g_517_);
    crate::leanh::lean_closure_set(v___f_523_, 1, v_L_516_);
    v___x_524_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
        v_g_517_, v___f_523_, v_a_518_, v_a_519_, v_a_520_, v_a_521_,
    );
    return v___x_524_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf___boxed(
    mut v_L_525_: *mut crate::leanh::LeanObject,
    mut v_g_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
    mut v_a_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ =
        l_Lean_MVarId_isIndependentOf(v_L_525_, v_g_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
    crate::leanh::lean_dec(v_a_530_);
    crate::leanh::lean_dec_ref(v_a_529_);
    crate::leanh::lean_dec(v_a_528_);
    crate::leanh::lean_dec_ref(v_a_527_);
    return v_res_532_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(
    mut v_00_u03b2_533_: *mut crate::leanh::LeanObject,
    mut v_m_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_536_: u8 = 0;
    v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_534_, v_a_535_);
    return v___x_536_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___boxed(
    mut v_00_u03b2_537_: *mut crate::leanh::LeanObject,
    mut v_m_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: u8 = 0;
    let mut v_r_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(
            v_00_u03b2_537_,
            v_m_538_,
            v_a_539_,
        );
    crate::leanh::lean_dec(v_a_539_);
    crate::leanh::lean_dec_ref(v_m_538_);
    v_r_541_ = crate::leanh::lean_box((v_res_540_) as usize);
    return v_r_541_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(
    mut v_00_u03b2_542_: *mut crate::leanh::LeanObject,
    mut v_a_543_: *mut crate::leanh::LeanObject,
    mut v_x_544_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_545_: u8 = 0;
    v___x_545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_543_, v_x_544_);
    return v___x_545_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(
    mut v_00_u03b2_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_x_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: u8 = 0;
    let mut v_r_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(v_00_u03b2_546_, v_a_547_, v_x_548_);
    crate::leanh::lean_dec(v_x_548_);
    crate::leanh::lean_dec(v_a_547_);
    v_r_550_ = crate::leanh::lean_box((v_res_549_) as usize);
    return v_r_550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_IndependentOf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_IndependentOf(
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
pub unsafe fn initialize_Lean_Meta_Tactic_IndependentOf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_IndependentOf(builtin);
}
