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
    mut v_e_276_: *mut leanh::LeanObject,
    mut v___y_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_279_: u8 = 0;
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_293_: u8 = 0;
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut v_unused_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_279_ = l_Lean_Expr_hasMVar(v_e_276_);
                if v___x_279_ == 0 {
                    v___x_280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_280_, 0, v_e_276_);
                    return v___x_280_;
                } else {
                    v___x_281_ = lean_st_ref_get(v___y_277_);
                    v_mctx_282_ = leanh::lean_ctor_get(v___x_281_, 0);
                    leanh::lean_inc_ref(v_mctx_282_);
                    leanh::lean_dec(v___x_281_);
                    v___x_283_ = l_Lean_instantiateMVarsCore(v_mctx_282_, v_e_276_);
                    v_fst_284_ = leanh::lean_ctor_get(v___x_283_, 0);
                    leanh::lean_inc(v_fst_284_);
                    v_snd_285_ = leanh::lean_ctor_get(v___x_283_, 1);
                    leanh::lean_inc(v_snd_285_);
                    leanh::lean_dec_ref(v___x_283_);
                    v___x_286_ = lean_st_ref_take(v___y_277_);
                    v_cache_287_ = leanh::lean_ctor_get(v___x_286_, 1);
                    v_zetaDeltaFVarIds_288_ = leanh::lean_ctor_get(v___x_286_, 2);
                    v_postponed_289_ = leanh::lean_ctor_get(v___x_286_, 3);
                    v_diag_290_ = leanh::lean_ctor_get(v___x_286_, 4);
                    v_isSharedCheck_299_ = (!leanh::lean_is_exclusive(v___x_286_)) as u8;
                    if v_isSharedCheck_299_ == 0 {
                        v_unused_300_ = leanh::lean_ctor_get(v___x_286_, 0);
                        leanh::lean_dec(v_unused_300_);
                        v___x_292_ = v___x_286_;
                        v_isShared_293_ = v_isSharedCheck_299_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_290_);
                        leanh::lean_inc(v_postponed_289_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_288_);
                        leanh::lean_inc(v_cache_287_);
                        leanh::lean_dec(v___x_286_);
                        v___x_292_ = leanh::lean_box(0);
                        v_isShared_293_ = v_isSharedCheck_299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_293_ == 0 {
                    leanh::lean_ctor_set(v___x_292_, 0, v_snd_285_);
                    v___x_295_ = v___x_292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 0, v_snd_285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 1, v_cache_287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 2, v_zetaDeltaFVarIds_288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 3, v_postponed_289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_298_, 4, v_diag_290_);
                    v___x_295_ = v_reuseFailAlloc_298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_296_ = lean_st_ref_set(v___y_277_, v___x_295_);
                v___x_297_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_297_, 0, v_fst_284_);
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(
    mut v_e_301_: *mut leanh::LeanObject,
    mut v___y_302_: *mut leanh::LeanObject,
    mut v___y_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(
        v_e_301_, v___y_302_,
    );
    leanh::lean_dec(v___y_302_);
    return v_res_304_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(
    mut v_e_305_: *mut leanh::LeanObject,
    mut v___y_306_: *mut leanh::LeanObject,
    mut v___y_307_: *mut leanh::LeanObject,
    mut v___y_308_: *mut leanh::LeanObject,
    mut v___y_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(
        v_e_305_, v___y_307_,
    );
    return v___x_311_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(
    mut v_e_312_: *mut leanh::LeanObject,
    mut v___y_313_: *mut leanh::LeanObject,
    mut v___y_314_: *mut leanh::LeanObject,
    mut v___y_315_: *mut leanh::LeanObject,
    mut v___y_316_: *mut leanh::LeanObject,
    mut v___y_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(
        v_e_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_,
    );
    leanh::lean_dec(v___y_316_);
    leanh::lean_dec_ref(v___y_315_);
    leanh::lean_dec(v___y_314_);
    leanh::lean_dec_ref(v___y_313_);
    return v_res_318_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
    mut v_mvarId_319_: *mut leanh::LeanObject,
    mut v_x_320_: *mut leanh::LeanObject,
    mut v___y_321_: *mut leanh::LeanObject,
    mut v___y_322_: *mut leanh::LeanObject,
    mut v___y_323_: *mut leanh::LeanObject,
    mut v___y_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_330_: u8 = 0;
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_334_: u8 = 0;
    let mut v_a_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_319_,
                    v_x_320_,
                    v___y_321_,
                    v___y_322_,
                    v___y_323_,
                    v___y_324_,
                );
                if leanh::lean_obj_tag(v___x_326_) == 0 {
                    v_a_327_ = leanh::lean_ctor_get(v___x_326_, 0);
                    v_isSharedCheck_334_ = (!leanh::lean_is_exclusive(v___x_326_)) as u8;
                    if v_isSharedCheck_334_ == 0 {
                        v___x_329_ = v___x_326_;
                        v_isShared_330_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_327_);
                        leanh::lean_dec(v___x_326_);
                        v___x_329_ = leanh::lean_box(0);
                        v_isShared_330_ = v_isSharedCheck_334_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_335_ = leanh::lean_ctor_get(v___x_326_, 0);
                    v_isSharedCheck_342_ = (!leanh::lean_is_exclusive(v___x_326_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_337_ = v___x_326_;
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_335_);
                        leanh::lean_dec(v___x_326_);
                        v___x_337_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
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
                    v_reuseFailAlloc_341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
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
    mut v_mvarId_343_: *mut leanh::LeanObject,
    mut v_x_344_: *mut leanh::LeanObject,
    mut v___y_345_: *mut leanh::LeanObject,
    mut v___y_346_: *mut leanh::LeanObject,
    mut v___y_347_: *mut leanh::LeanObject,
    mut v___y_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
        v_mvarId_343_,
        v_x_344_,
        v___y_345_,
        v___y_346_,
        v___y_347_,
        v___y_348_,
    );
    leanh::lean_dec(v___y_348_);
    leanh::lean_dec_ref(v___y_347_);
    leanh::lean_dec(v___y_346_);
    leanh::lean_dec_ref(v___y_345_);
    return v_res_350_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(
    mut v_00_u03b1_351_: *mut leanh::LeanObject,
    mut v_mvarId_352_: *mut leanh::LeanObject,
    mut v_x_353_: *mut leanh::LeanObject,
    mut v___y_354_: *mut leanh::LeanObject,
    mut v___y_355_: *mut leanh::LeanObject,
    mut v___y_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_360_: *mut leanh::LeanObject,
    mut v_mvarId_361_: *mut leanh::LeanObject,
    mut v_x_362_: *mut leanh::LeanObject,
    mut v___y_363_: *mut leanh::LeanObject,
    mut v___y_364_: *mut leanh::LeanObject,
    mut v___y_365_: *mut leanh::LeanObject,
    mut v___y_366_: *mut leanh::LeanObject,
    mut v___y_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(
        v_00_u03b1_360_,
        v_mvarId_361_,
        v_x_362_,
        v___y_363_,
        v___y_364_,
        v___y_365_,
        v___y_366_,
    );
    leanh::lean_dec(v___y_366_);
    leanh::lean_dec_ref(v___y_365_);
    leanh::lean_dec(v___y_364_);
    leanh::lean_dec_ref(v___y_363_);
    return v_res_368_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(
    mut v_a_369_: *mut leanh::LeanObject,
    mut v_x_370_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_371_: u8 = 0;
    let mut v_key_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_370_) == 0 {
                    v___x_371_ = 0;
                    return v___x_371_;
                } else {
                    v_key_372_ = leanh::lean_ctor_get(v_x_370_, 0);
                    v_tail_373_ = leanh::lean_ctor_get(v_x_370_, 2);
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
    mut v_a_376_: *mut leanh::LeanObject,
    mut v_x_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_378_: u8 = 0;
    let mut v_r_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_376_, v_x_377_);
    leanh::lean_dec(v_x_377_);
    leanh::lean_dec(v_a_376_);
    v_r_379_ = leanh::lean_box((v_res_378_) as usize);
    return v_r_379_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(
    mut v_m_380_: *mut leanh::LeanObject,
    mut v_a_381_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: u8 = 0;
    v_buckets_382_ = leanh::lean_ctor_get(v_m_380_, 1);
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
    mut v_m_398_: *mut leanh::LeanObject,
    mut v_a_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: u8 = 0;
    let mut v_r_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_398_, v_a_399_);
    leanh::lean_dec(v_a_399_);
    leanh::lean_dec_ref(v_m_398_);
    v_r_401_ = leanh::lean_box((v_res_400_) as usize);
    return v_r_401_;
}
pub unsafe fn l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
    mut v_a_402_: u8,
    mut v_g_403_: *mut leanh::LeanObject,
    mut v_x_404_: *mut leanh::LeanObject,
    mut v___y_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
    mut v___y_407_: *mut leanh::LeanObject,
    mut v___y_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_410_: u8 = 0;
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_419_: u8 = 0;
    let mut v___x_420_: u8 = 0;
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_a_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_404_) == 0 {
                    v___x_410_ = 1;
                    v___x_411_ = leanh::lean_box((v___x_410_) as usize);
                    v___x_412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_412_, 0, v___x_411_);
                    return v___x_412_;
                } else {
                    v_head_413_ = leanh::lean_ctor_get(v_x_404_, 0);
                    leanh::lean_inc(v_head_413_);
                    v_tail_414_ = leanh::lean_ctor_get(v_x_404_, 1);
                    leanh::lean_inc(v_tail_414_);
                    leanh::lean_dec_ref_known(v_x_404_, 2);
                    v___x_415_ = l_Lean_MVarId_getMVarDependencies(
                        v_head_413_,
                        v_a_402_,
                        v___y_405_,
                        v___y_406_,
                        v___y_407_,
                        v___y_408_,
                    );
                    if leanh::lean_obj_tag(v___x_415_) == 0 {
                        v_a_416_ = leanh::lean_ctor_get(v___x_415_, 0);
                        v_isSharedCheck_427_ = (!leanh::lean_is_exclusive(v___x_415_)) as u8;
                        if v_isSharedCheck_427_ == 0 {
                            v___x_418_ = v___x_415_;
                            v_isShared_419_ = v_isSharedCheck_427_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_416_);
                            leanh::lean_dec(v___x_415_);
                            v___x_418_ = leanh::lean_box(0);
                            v_isShared_419_ = v_isSharedCheck_427_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_414_);
                        v_a_428_ = leanh::lean_ctor_get(v___x_415_, 0);
                        v_isSharedCheck_435_ = (!leanh::lean_is_exclusive(v___x_415_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v___x_430_ = v___x_415_;
                            v_isShared_431_ = v_isSharedCheck_435_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_428_);
                            leanh::lean_dec(v___x_415_);
                            v___x_430_ = leanh::lean_box(0);
                            v_isShared_431_ = v_isSharedCheck_435_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_a_416_, v_g_403_);
                leanh::lean_dec(v_a_416_);
                if v___x_420_ == 0 {
                    leanh::lean_del_object(v___x_418_);
                    v_x_404_ = v_tail_414_;
                    state = 0;
                    continue;
                } else {
                    if v_a_402_ == 0 {
                        leanh::lean_dec(v_tail_414_);
                        v___x_422_ = leanh::lean_box((v_a_402_) as usize);
                        if v_isShared_419_ == 0 {
                            leanh::lean_ctor_set(v___x_418_, 0, v___x_422_);
                            v___x_424_ = v___x_418_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
                            v___x_424_ = v_reuseFailAlloc_425_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_418_);
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
                    v_reuseFailAlloc_434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
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
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_g_437_: *mut leanh::LeanObject,
    mut v_x_438_: *mut leanh::LeanObject,
    mut v___y_439_: *mut leanh::LeanObject,
    mut v___y_440_: *mut leanh::LeanObject,
    mut v___y_441_: *mut leanh::LeanObject,
    mut v___y_442_: *mut leanh::LeanObject,
    mut v___y_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2521__boxed_444_: u8 = 0;
    let mut v_res_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_2521__boxed_444_ = (leanh::lean_unbox(v_a_436_) as u8);
    v_res_445_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
        v_a_2521__boxed_444_,
        v_g_437_,
        v_x_438_,
        v___y_439_,
        v___y_440_,
        v___y_441_,
        v___y_442_,
    );
    leanh::lean_dec(v___y_442_);
    leanh::lean_dec_ref(v___y_441_);
    leanh::lean_dec(v___y_440_);
    leanh::lean_dec_ref(v___y_439_);
    leanh::lean_dec(v_g_437_);
    return v_res_445_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf___lam__0(
    mut v_g_446_: *mut leanh::LeanObject,
    mut v_L_447_: *mut leanh::LeanObject,
    mut v___y_448_: *mut leanh::LeanObject,
    mut v___y_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: u8 = 0;
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_465_: u8 = 0;
    let mut v___x_466_: u8 = 0;
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: u8 = 0;
    let mut v___x_474_: u8 = 0;
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_a_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_489_: u8 = 0;
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_493_: u8 = 0;
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_a_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_g_446_);
                v___x_453_ =
                    l_Lean_MVarId_getType(v_g_446_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
                if leanh::lean_obj_tag(v___x_453_) == 0 {
                    v_a_454_ = leanh::lean_ctor_get(v___x_453_, 0);
                    leanh::lean_inc(v_a_454_);
                    leanh::lean_dec_ref_known(v___x_453_, 1);
                    v___x_455_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_a_454_, v___y_449_);
                    v_a_456_ = leanh::lean_ctor_get(v___x_455_, 0);
                    v_isSharedCheck_499_ = (!leanh::lean_is_exclusive(v___x_455_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_458_ = v___x_455_;
                        v_isShared_459_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_456_);
                        leanh::lean_dec(v___x_455_);
                        v___x_458_ = leanh::lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_499_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_451_);
                    leanh::lean_dec_ref(v___y_450_);
                    leanh::lean_dec(v___y_449_);
                    leanh::lean_dec_ref(v___y_448_);
                    leanh::lean_dec(v_L_447_);
                    leanh::lean_dec(v_g_446_);
                    v_a_500_ = leanh::lean_ctor_get(v___x_453_, 0);
                    v_isSharedCheck_507_ = (!leanh::lean_is_exclusive(v___x_453_)) as u8;
                    if v_isSharedCheck_507_ == 0 {
                        v___x_502_ = v___x_453_;
                        v_isShared_503_ = v_isSharedCheck_507_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_500_);
                        leanh::lean_dec(v___x_453_);
                        v___x_502_ = leanh::lean_box(0);
                        v_isShared_503_ = v_isSharedCheck_507_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_460_ = l_Lean_Expr_hasExprMVar(v_a_456_);
                if v___x_460_ == 0 {
                    leanh::lean_del_object(v___x_458_);
                    leanh::lean_inc(v___y_451_);
                    leanh::lean_inc_ref(v___y_450_);
                    leanh::lean_inc(v___y_449_);
                    leanh::lean_inc_ref(v___y_448_);
                    v___x_461_ =
                        lean_infer_type(v_a_456_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
                    if leanh::lean_obj_tag(v___x_461_) == 0 {
                        v_a_462_ = leanh::lean_ctor_get(v___x_461_, 0);
                        v_isSharedCheck_485_ = (!leanh::lean_is_exclusive(v___x_461_)) as u8;
                        if v_isSharedCheck_485_ == 0 {
                            v___x_464_ = v___x_461_;
                            v_isShared_465_ = v_isSharedCheck_485_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_462_);
                            leanh::lean_dec(v___x_461_);
                            v___x_464_ = leanh::lean_box(0);
                            v_isShared_465_ = v_isSharedCheck_485_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_451_);
                        leanh::lean_dec_ref(v___y_450_);
                        leanh::lean_dec(v___y_449_);
                        leanh::lean_dec_ref(v___y_448_);
                        leanh::lean_dec(v_L_447_);
                        leanh::lean_dec(v_g_446_);
                        v_a_486_ = leanh::lean_ctor_get(v___x_461_, 0);
                        v_isSharedCheck_493_ = (!leanh::lean_is_exclusive(v___x_461_)) as u8;
                        if v_isSharedCheck_493_ == 0 {
                            v___x_488_ = v___x_461_;
                            v_isShared_489_ = v_isSharedCheck_493_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_486_);
                            leanh::lean_dec(v___x_461_);
                            v___x_488_ = leanh::lean_box(0);
                            v_isShared_489_ = v_isSharedCheck_493_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_456_);
                    leanh::lean_dec(v___y_451_);
                    leanh::lean_dec_ref(v___y_450_);
                    leanh::lean_dec(v___y_449_);
                    leanh::lean_dec_ref(v___y_448_);
                    leanh::lean_dec(v_L_447_);
                    leanh::lean_dec(v_g_446_);
                    v___x_494_ = 0;
                    v___x_495_ = leanh::lean_box((v___x_494_) as usize);
                    if v_isShared_459_ == 0 {
                        leanh::lean_ctor_set(v___x_458_, 0, v___x_495_);
                        v___x_497_ = v___x_458_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_498_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
                        v___x_497_ = v_reuseFailAlloc_498_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_466_ = 1;
                v___x_467_ = l_Lean_Expr_isProp(v_a_462_);
                leanh::lean_dec(v_a_462_);
                if v___x_467_ == 0 {
                    leanh::lean_del_object(v___x_464_);
                    leanh::lean_inc(v_g_446_);
                    v___x_468_ = l_Lean_MVarId_isSubsingleton(
                        v_g_446_, v___y_448_, v___y_449_, v___y_450_, v___y_451_,
                    );
                    if leanh::lean_obj_tag(v___x_468_) == 0 {
                        v_a_469_ = leanh::lean_ctor_get(v___x_468_, 0);
                        v_isSharedCheck_480_ = (!leanh::lean_is_exclusive(v___x_468_)) as u8;
                        if v_isSharedCheck_480_ == 0 {
                            v___x_471_ = v___x_468_;
                            v_isShared_472_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_469_);
                            leanh::lean_dec(v___x_468_);
                            v___x_471_ = leanh::lean_box(0);
                            v_isShared_472_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_451_);
                        leanh::lean_dec_ref(v___y_450_);
                        leanh::lean_dec(v___y_449_);
                        leanh::lean_dec_ref(v___y_448_);
                        leanh::lean_dec(v_L_447_);
                        leanh::lean_dec(v_g_446_);
                        return v___x_468_;
                    }
                } else {
                    leanh::lean_dec(v___y_451_);
                    leanh::lean_dec_ref(v___y_450_);
                    leanh::lean_dec(v___y_449_);
                    leanh::lean_dec_ref(v___y_448_);
                    leanh::lean_dec(v_L_447_);
                    leanh::lean_dec(v_g_446_);
                    v___x_481_ = leanh::lean_box((v___x_466_) as usize);
                    if v_isShared_465_ == 0 {
                        leanh::lean_ctor_set(v___x_464_, 0, v___x_481_);
                        v___x_483_ = v___x_464_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
                        v___x_483_ = v_reuseFailAlloc_484_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_473_ = (leanh::lean_unbox(v_a_469_) as u8);
                if v___x_473_ == 0 {
                    leanh::lean_del_object(v___x_471_);
                    v___x_474_ = (leanh::lean_unbox(v_a_469_) as u8);
                    leanh::lean_dec(v_a_469_);
                    v___x_475_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(
                        v___x_474_, v_g_446_, v_L_447_, v___y_448_, v___y_449_, v___y_450_,
                        v___y_451_,
                    );
                    leanh::lean_dec(v___y_451_);
                    leanh::lean_dec_ref(v___y_450_);
                    leanh::lean_dec(v___y_449_);
                    leanh::lean_dec_ref(v___y_448_);
                    leanh::lean_dec(v_g_446_);
                    return v___x_475_;
                } else {
                    leanh::lean_dec(v_a_469_);
                    leanh::lean_dec(v___y_451_);
                    leanh::lean_dec_ref(v___y_450_);
                    leanh::lean_dec(v___y_449_);
                    leanh::lean_dec_ref(v___y_448_);
                    leanh::lean_dec(v_L_447_);
                    leanh::lean_dec(v_g_446_);
                    v___x_476_ = leanh::lean_box((v___x_466_) as usize);
                    if v_isShared_472_ == 0 {
                        leanh::lean_ctor_set(v___x_471_, 0, v___x_476_);
                        v___x_478_ = v___x_471_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_479_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
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
                    v_reuseFailAlloc_492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
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
                    v_reuseFailAlloc_506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
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
    mut v_g_508_: *mut leanh::LeanObject,
    mut v_L_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
    mut v___y_512_: *mut leanh::LeanObject,
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Lean_MVarId_isIndependentOf___lam__0(
        v_g_508_, v_L_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_,
    );
    return v_res_515_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf(
    mut v_L_516_: *mut leanh::LeanObject,
    mut v_g_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_g_517_);
    v___f_523_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_isIndependentOf___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_523_, 0, v_g_517_);
    leanh::lean_closure_set(v___f_523_, 1, v_L_516_);
    v___x_524_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(
        v_g_517_, v___f_523_, v_a_518_, v_a_519_, v_a_520_, v_a_521_,
    );
    return v___x_524_;
}
pub unsafe fn l_Lean_MVarId_isIndependentOf___boxed(
    mut v_L_525_: *mut leanh::LeanObject,
    mut v_g_526_: *mut leanh::LeanObject,
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
    mut v_a_529_: *mut leanh::LeanObject,
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_a_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ =
        l_Lean_MVarId_isIndependentOf(v_L_525_, v_g_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
    leanh::lean_dec(v_a_530_);
    leanh::lean_dec_ref(v_a_529_);
    leanh::lean_dec(v_a_528_);
    leanh::lean_dec_ref(v_a_527_);
    return v_res_532_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(
    mut v_00_u03b2_533_: *mut leanh::LeanObject,
    mut v_m_534_: *mut leanh::LeanObject,
    mut v_a_535_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_536_: u8 = 0;
    v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_534_, v_a_535_);
    return v___x_536_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___boxed(
    mut v_00_u03b2_537_: *mut leanh::LeanObject,
    mut v_m_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: u8 = 0;
    let mut v_r_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(
            v_00_u03b2_537_,
            v_m_538_,
            v_a_539_,
        );
    leanh::lean_dec(v_a_539_);
    leanh::lean_dec_ref(v_m_538_);
    v_r_541_ = leanh::lean_box((v_res_540_) as usize);
    return v_r_541_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(
    mut v_00_u03b2_542_: *mut leanh::LeanObject,
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_x_544_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_545_: u8 = 0;
    v___x_545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_543_, v_x_544_);
    return v___x_545_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(
    mut v_00_u03b2_546_: *mut leanh::LeanObject,
    mut v_a_547_: *mut leanh::LeanObject,
    mut v_x_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_549_: u8 = 0;
    let mut v_r_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(v_00_u03b2_546_, v_a_547_, v_x_548_);
    leanh::lean_dec(v_x_548_);
    leanh::lean_dec(v_a_547_);
    v_r_550_ = leanh::lean_box((v_res_549_) as usize);
    return v_r_550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_IndependentOf(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_IndependentOf(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_IndependentOf(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_CollectMVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_IndependentOf(builtin);
}