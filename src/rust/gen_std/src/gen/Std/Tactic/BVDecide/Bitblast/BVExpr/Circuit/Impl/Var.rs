// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Var
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_lor, lean_nat_mul,
    lean_uint64_mix_hash, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::{
    l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg, l_Std_Sat_AIG_instHashableFanin_hash,
};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed,
    l_Std_Tactic_BVDecide_instHashableBVBit_hash,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(
    mut v_x_289_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_289_) {
        0 => {
            let mut v___x_290_: u64 = 0;
            v___x_290_ = 0u64;
            return v___x_290_;
        }
        1 => {
            let mut v_idx_291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_292_: u64 = 0;
            let mut v___x_293_: u64 = 0;
            let mut v___x_294_: u64 = 0;
            v_idx_291_ = leanh::lean_ctor_get(v_x_289_, 0);
            v___x_292_ = 1u64;
            v___x_293_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_idx_291_);
            v___x_294_ = lean_uint64_mix_hash(v___x_292_, v___x_293_);
            return v___x_294_;
        }
        _ => {
            let mut v_l_295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_296_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_297_: u64 = 0;
            let mut v___x_298_: u64 = 0;
            let mut v___x_299_: u64 = 0;
            let mut v___x_300_: u64 = 0;
            let mut v___x_301_: u64 = 0;
            v_l_295_ = leanh::lean_ctor_get(v_x_289_, 0);
            v_r_296_ = leanh::lean_ctor_get(v_x_289_, 1);
            v___x_297_ = 2u64;
            v___x_298_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_295_);
            v___x_299_ = lean_uint64_mix_hash(v___x_297_, v___x_298_);
            v___x_300_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_296_);
            v___x_301_ = lean_uint64_mix_hash(v___x_299_, v___x_300_);
            return v___x_301_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1___boxed(
    mut v_x_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_303_: u64 = 0;
    let mut v_r_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_x_302_);
    leanh::lean_dec(v_x_302_);
    v_r_304_ = leanh::lean_box_uint64(v_res_303_);
    return v_r_304_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(
    mut v_x_305_: *mut leanh::LeanObject,
    mut v_x_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_312_: u8 = 0;
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u64 = 0;
    let mut v___x_315_: u64 = 0;
    let mut v___x_316_: u64 = 0;
    let mut v_fold_317_: u64 = 0;
    let mut v___x_318_: u64 = 0;
    let mut v___x_319_: u64 = 0;
    let mut v___x_320_: u64 = 0;
    let mut v___x_321_: usize = 0;
    let mut v___x_322_: usize = 0;
    let mut v___x_323_: usize = 0;
    let mut v___x_324_: usize = 0;
    let mut v___x_325_: usize = 0;
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_306_) == 0 {
                    return v_x_305_;
                } else {
                    v_key_307_ = leanh::lean_ctor_get(v_x_306_, 0);
                    v_value_308_ = leanh::lean_ctor_get(v_x_306_, 1);
                    v_tail_309_ = leanh::lean_ctor_get(v_x_306_, 2);
                    v_isSharedCheck_332_ = (!leanh::lean_is_exclusive(v_x_306_)) as u8;
                    if v_isSharedCheck_332_ == 0 {
                        v___x_311_ = v_x_306_;
                        v_isShared_312_ = v_isSharedCheck_332_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_309_);
                        leanh::lean_inc(v_value_308_);
                        leanh::lean_inc(v_key_307_);
                        leanh::lean_dec(v_x_306_);
                        v___x_311_ = leanh::lean_box(0);
                        v_isShared_312_ = v_isSharedCheck_332_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_313_ = lean_array_get_size(v_x_305_);
                v___x_314_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_key_307_);
                v___x_315_ = 32u64;
                v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
                v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
                v___x_318_ = 16u64;
                v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
                v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
                v___x_321_ = lean_uint64_to_usize(v___x_320_);
                v___x_322_ = lean_usize_of_nat(v___x_313_);
                v___x_323_ = 1usize;
                v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
                v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
                v___x_326_ = lean_array_uget_borrowed(v_x_305_, v___x_325_);
                leanh::lean_inc(v___x_326_);
                if v_isShared_312_ == 0 {
                    leanh::lean_ctor_set(v___x_311_, 2, v___x_326_);
                    v___x_328_ = v___x_311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_331_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_331_, 0, v_key_307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_331_, 1, v_value_308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_331_, 2, v___x_326_);
                    v___x_328_ = v_reuseFailAlloc_331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_329_ = lean_array_uset(v_x_305_, v___x_325_, v___x_328_);
                v_x_305_ = v___x_329_;
                v_x_306_ = v_tail_309_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(
    mut v_i_333_: *mut leanh::LeanObject,
    mut v_source_334_: *mut leanh::LeanObject,
    mut v_target_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: u8 = 0;
    let mut v_es_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_336_ = lean_array_get_size(v_source_334_);
                v___x_337_ = lean_nat_dec_lt(v_i_333_, v___x_336_);
                if v___x_337_ == 0 {
                    leanh::lean_dec_ref(v_source_334_);
                    leanh::lean_dec(v_i_333_);
                    return v_target_335_;
                } else {
                    v_es_338_ = lean_array_fget(v_source_334_, v_i_333_);
                    v___x_339_ = leanh::lean_box(0);
                    v_source_340_ = lean_array_fset(v_source_334_, v_i_333_, v___x_339_);
                    v_target_341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_target_335_, v_es_338_);
                    v___x_342_ = leanh::lean_unsigned_to_nat(1);
                    v___x_343_ = lean_nat_add(v_i_333_, v___x_342_);
                    leanh::lean_dec(v_i_333_);
                    v_i_333_ = v___x_343_;
                    v_source_334_ = v_source_340_;
                    v_target_335_ = v_target_341_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(
    mut v_data_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = lean_array_get_size(v_data_345_);
    v___x_347_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_348_ = lean_nat_mul(v___x_346_, v___x_347_);
    v___x_349_ = leanh::lean_unsigned_to_nat(0);
    v___x_350_ = leanh::lean_box(0);
    v___x_351_ = lean_mk_array(v_nbuckets_348_, v___x_350_);
    v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v___x_349_, v_data_345_, v___x_351_);
    return v___x_352_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(
    mut v_a_353_: *mut leanh::LeanObject,
    mut v_x_354_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_355_: u8 = 0;
    let mut v_key_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_354_) == 0 {
                    leanh::lean_dec(v_a_353_);
                    v___x_355_ = 0;
                    return v___x_355_;
                } else {
                    v_key_356_ = leanh::lean_ctor_get(v_x_354_, 0);
                    leanh::lean_inc(v_key_356_);
                    v_tail_357_ = leanh::lean_ctor_get(v_x_354_, 2);
                    leanh::lean_inc(v_tail_357_);
                    leanh::lean_dec_ref_known(v_x_354_, 3);
                    v___x_358_ = leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    leanh::lean_inc(v_a_353_);
                    v___x_359_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_358_, v_key_356_, v_a_353_,
                    );
                    if v___x_359_ == 0 {
                        v_x_354_ = v_tail_357_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_357_);
                        leanh::lean_dec(v_a_353_);
                        return v___x_359_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_a_361_: *mut leanh::LeanObject,
    mut v_x_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_363_: u8 = 0;
    let mut v_r_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_361_, v_x_362_);
    v_r_364_ = leanh::lean_box((v_res_363_) as usize);
    return v_r_364_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(
    mut v_a_365_: *mut leanh::LeanObject,
    mut v_b_366_: *mut leanh::LeanObject,
    mut v_x_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: u8 = 0;
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_367_) == 0 {
                    leanh::lean_dec(v_b_366_);
                    leanh::lean_dec(v_a_365_);
                    return v_x_367_;
                } else {
                    v_key_368_ = leanh::lean_ctor_get(v_x_367_, 0);
                    v_value_369_ = leanh::lean_ctor_get(v_x_367_, 1);
                    v_tail_370_ = leanh::lean_ctor_get(v_x_367_, 2);
                    v_isSharedCheck_383_ = (!leanh::lean_is_exclusive(v_x_367_)) as u8;
                    if v_isSharedCheck_383_ == 0 {
                        v___x_372_ = v_x_367_;
                        v_isShared_373_ = v_isSharedCheck_383_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_370_);
                        leanh::lean_inc(v_value_369_);
                        leanh::lean_inc(v_key_368_);
                        leanh::lean_dec(v_x_367_);
                        v___x_372_ = leanh::lean_box(0);
                        v_isShared_373_ = v_isSharedCheck_383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_374_ = leanh::lean_alloc_closure(
                    l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                leanh::lean_inc(v_a_365_);
                leanh::lean_inc(v_key_368_);
                v___x_375_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                    v___x_374_, v_key_368_, v_a_365_,
                );
                if v___x_375_ == 0 {
                    v___x_376_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_365_, v_b_366_, v_tail_370_);
                    if v_isShared_373_ == 0 {
                        leanh::lean_ctor_set(v___x_372_, 2, v___x_376_);
                        v___x_378_ = v___x_372_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 0, v_key_368_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 1, v_value_369_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_379_, 2, v___x_376_);
                        v___x_378_ = v_reuseFailAlloc_379_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_369_);
                    leanh::lean_dec(v_key_368_);
                    if v_isShared_373_ == 0 {
                        leanh::lean_ctor_set(v___x_372_, 1, v_b_366_);
                        leanh::lean_ctor_set(v___x_372_, 0, v_a_365_);
                        v___x_381_ = v___x_372_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_382_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_365_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_382_, 1, v_b_366_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_382_, 2, v_tail_370_);
                        v___x_381_ = v_reuseFailAlloc_382_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_378_;
            }
            3 => {
                return v___x_381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(
    mut v_m_384_: *mut leanh::LeanObject,
    mut v_a_385_: *mut leanh::LeanObject,
    mut v_b_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u64 = 0;
    let mut v___x_394_: u64 = 0;
    let mut v___x_395_: u64 = 0;
    let mut v_fold_396_: u64 = 0;
    let mut v___x_397_: u64 = 0;
    let mut v___x_398_: u64 = 0;
    let mut v___x_399_: u64 = 0;
    let mut v___x_400_: usize = 0;
    let mut v___x_401_: usize = 0;
    let mut v___x_402_: usize = 0;
    let mut v___x_403_: usize = 0;
    let mut v___x_404_: usize = 0;
    let mut v_bkt_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: u8 = 0;
    let mut v_val_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_387_ = leanh::lean_ctor_get(v_m_384_, 0);
                v_buckets_388_ = leanh::lean_ctor_get(v_m_384_, 1);
                v_isSharedCheck_431_ = (!leanh::lean_is_exclusive(v_m_384_)) as u8;
                if v_isSharedCheck_431_ == 0 {
                    v___x_390_ = v_m_384_;
                    v_isShared_391_ = v_isSharedCheck_431_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_388_);
                    leanh::lean_inc(v_size_387_);
                    leanh::lean_dec(v_m_384_);
                    v___x_390_ = leanh::lean_box(0);
                    v_isShared_391_ = v_isSharedCheck_431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_392_ = lean_array_get_size(v_buckets_388_);
                v___x_393_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_385_);
                v___x_394_ = 32u64;
                v___x_395_ = lean_uint64_shift_right(v___x_393_, v___x_394_);
                v_fold_396_ = lean_uint64_xor(v___x_393_, v___x_395_);
                v___x_397_ = 16u64;
                v___x_398_ = lean_uint64_shift_right(v_fold_396_, v___x_397_);
                v___x_399_ = lean_uint64_xor(v_fold_396_, v___x_398_);
                v___x_400_ = lean_uint64_to_usize(v___x_399_);
                v___x_401_ = lean_usize_of_nat(v___x_392_);
                v___x_402_ = 1usize;
                v___x_403_ = lean_usize_sub(v___x_401_, v___x_402_);
                v___x_404_ = lean_usize_land(v___x_400_, v___x_403_);
                v_bkt_405_ = lean_array_uget_borrowed(v_buckets_388_, v___x_404_);
                leanh::lean_inc(v_bkt_405_);
                leanh::lean_inc(v_a_385_);
                v___x_406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_385_, v_bkt_405_);
                if v___x_406_ == 0 {
                    v___x_407_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_408_ = lean_nat_add(v_size_387_, v___x_407_);
                    leanh::lean_dec(v_size_387_);
                    leanh::lean_inc(v_bkt_405_);
                    v___x_409_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_409_, 0, v_a_385_);
                    leanh::lean_ctor_set(v___x_409_, 1, v_b_386_);
                    leanh::lean_ctor_set(v___x_409_, 2, v_bkt_405_);
                    v_buckets_x27_410_ = lean_array_uset(v_buckets_388_, v___x_404_, v___x_409_);
                    v___x_411_ = leanh::lean_unsigned_to_nat(4);
                    v___x_412_ = lean_nat_mul(v_size_x27_408_, v___x_411_);
                    v___x_413_ = leanh::lean_unsigned_to_nat(3);
                    v___x_414_ = lean_nat_div(v___x_412_, v___x_413_);
                    leanh::lean_dec(v___x_412_);
                    v___x_415_ = lean_array_get_size(v_buckets_x27_410_);
                    v___x_416_ = lean_nat_dec_le(v___x_414_, v___x_415_);
                    leanh::lean_dec(v___x_414_);
                    if v___x_416_ == 0 {
                        v_val_417_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_buckets_x27_410_);
                        if v_isShared_391_ == 0 {
                            leanh::lean_ctor_set(v___x_390_, 1, v_val_417_);
                            leanh::lean_ctor_set(v___x_390_, 0, v_size_x27_408_);
                            v___x_419_ = v___x_390_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_420_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_420_, 0, v_size_x27_408_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_420_, 1, v_val_417_);
                            v___x_419_ = v_reuseFailAlloc_420_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_391_ == 0 {
                            leanh::lean_ctor_set(v___x_390_, 1, v_buckets_x27_410_);
                            leanh::lean_ctor_set(v___x_390_, 0, v_size_x27_408_);
                            v___x_422_ = v___x_390_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v_size_x27_408_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_423_,
                                1,
                                v_buckets_x27_410_,
                            );
                            v___x_422_ = v_reuseFailAlloc_423_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_405_);
                    v___x_424_ = leanh::lean_box(0);
                    v_buckets_x27_425_ = lean_array_uset(v_buckets_388_, v___x_404_, v___x_424_);
                    v___x_426_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_385_, v_b_386_, v_bkt_405_);
                    v___x_427_ = lean_array_uset(v_buckets_x27_425_, v___x_404_, v___x_426_);
                    if v_isShared_391_ == 0 {
                        leanh::lean_ctor_set(v___x_390_, 1, v___x_427_);
                        v___x_429_ = v___x_390_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_430_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_430_, 0, v_size_387_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
                        v___x_429_ = v_reuseFailAlloc_430_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_419_;
            }
            3 => {
                return v___x_422_;
            }
            4 => {
                return v___x_429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(
    mut v_a_432_: *mut leanh::LeanObject,
    mut v_x_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: u8 = 0;
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_433_) == 0 {
                    leanh::lean_dec(v_a_432_);
                    v___x_434_ = leanh::lean_box(0);
                    return v___x_434_;
                } else {
                    v_key_435_ = leanh::lean_ctor_get(v_x_433_, 0);
                    leanh::lean_inc(v_key_435_);
                    v_value_436_ = leanh::lean_ctor_get(v_x_433_, 1);
                    leanh::lean_inc(v_value_436_);
                    v_tail_437_ = leanh::lean_ctor_get(v_x_433_, 2);
                    leanh::lean_inc(v_tail_437_);
                    leanh::lean_dec_ref_known(v_x_433_, 3);
                    v___x_438_ = leanh::lean_alloc_closure(
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed
                            as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    leanh::lean_inc(v_a_432_);
                    v___x_439_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
                        v___x_438_, v_key_435_, v_a_432_,
                    );
                    if v___x_439_ == 0 {
                        leanh::lean_dec(v_value_436_);
                        v_x_433_ = v_tail_437_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_437_);
                        leanh::lean_dec(v_a_432_);
                        v___x_441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_441_, 0, v_value_436_);
                        return v___x_441_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(
    mut v_m_442_: *mut leanh::LeanObject,
    mut v_a_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u64 = 0;
    let mut v___x_447_: u64 = 0;
    let mut v___x_448_: u64 = 0;
    let mut v_fold_449_: u64 = 0;
    let mut v___x_450_: u64 = 0;
    let mut v___x_451_: u64 = 0;
    let mut v___x_452_: u64 = 0;
    let mut v___x_453_: usize = 0;
    let mut v___x_454_: usize = 0;
    let mut v___x_455_: usize = 0;
    let mut v___x_456_: usize = 0;
    let mut v___x_457_: usize = 0;
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_444_ = leanh::lean_ctor_get(v_m_442_, 1);
    v___x_445_ = lean_array_get_size(v_buckets_444_);
    v___x_446_ = l_Std_Sat_AIG_instHashableDecl_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__1(v_a_443_);
    v___x_447_ = 32u64;
    v___x_448_ = lean_uint64_shift_right(v___x_446_, v___x_447_);
    v_fold_449_ = lean_uint64_xor(v___x_446_, v___x_448_);
    v___x_450_ = 16u64;
    v___x_451_ = lean_uint64_shift_right(v_fold_449_, v___x_450_);
    v___x_452_ = lean_uint64_xor(v_fold_449_, v___x_451_);
    v___x_453_ = lean_uint64_to_usize(v___x_452_);
    v___x_454_ = lean_usize_of_nat(v___x_445_);
    v___x_455_ = 1usize;
    v___x_456_ = lean_usize_sub(v___x_454_, v___x_455_);
    v___x_457_ = lean_usize_land(v___x_453_, v___x_456_);
    v___x_458_ = lean_array_uget_borrowed(v_buckets_444_, v___x_457_);
    leanh::lean_inc(v___x_458_);
    v___x_459_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_443_, v___x_458_);
    return v___x_459_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg___boxed(
    mut v_m_460_: *mut leanh::LeanObject,
    mut v_a_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_460_, v_a_461_);
    leanh::lean_dec_ref(v_m_460_);
    return v_res_462_;
}
pub unsafe fn l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(
    mut v_aig_463_: *mut leanh::LeanObject,
    mut v_n_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v_decl_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_465_ = leanh::lean_ctor_get(v_aig_463_, 0);
                v_cache_466_ = leanh::lean_ctor_get(v_aig_463_, 1);
                v_isSharedCheck_488_ = (!leanh::lean_is_exclusive(v_aig_463_)) as u8;
                if v_isSharedCheck_488_ == 0 {
                    v___x_468_ = v_aig_463_;
                    v_isShared_469_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_466_);
                    leanh::lean_inc(v_decls_465_);
                    leanh::lean_dec(v_aig_463_);
                    v___x_468_ = leanh::lean_box(0);
                    v_isShared_469_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decl_470_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v_decl_470_, 0, v_n_464_);
                leanh::lean_inc_ref(v_decl_470_);
                v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_cache_466_, v_decl_470_);
                if leanh::lean_obj_tag(v___x_471_) == 0 {
                    v_g_472_ = lean_array_get_size(v_decls_465_);
                    leanh::lean_inc_ref(v_decl_470_);
                    v_cache_473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_cache_466_, v_decl_470_, v_g_472_);
                    v_decls_474_ = lean_array_push(v_decls_465_, v_decl_470_);
                    if v_isShared_469_ == 0 {
                        leanh::lean_ctor_set(v___x_468_, 1, v_cache_473_);
                        leanh::lean_ctor_set(v___x_468_, 0, v_decls_474_);
                        v___x_476_ = v___x_468_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_480_, 0, v_decls_474_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_480_, 1, v_cache_473_);
                        v___x_476_ = v_reuseFailAlloc_480_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_decl_470_, 1);
                    v_val_481_ = leanh::lean_ctor_get(v___x_471_, 0);
                    leanh::lean_inc(v_val_481_);
                    leanh::lean_dec_ref_known(v___x_471_, 1);
                    if v_isShared_469_ == 0 {
                        v___x_483_ = v___x_468_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_487_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v_decls_465_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_487_, 1, v_cache_466_);
                        v___x_483_ = v_reuseFailAlloc_487_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_477_ = 0;
                v___x_478_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_478_, 0, v_g_472_);
                leanh::lean_ctor_set_uint8(
                    v___x_478_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_477_,
                );
                v___x_479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_479_, 0, v___x_476_);
                leanh::lean_ctor_set(v___x_479_, 1, v___x_478_);
                return v___x_479_;
            }
            3 => {
                v___x_484_ = 0;
                v___x_485_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_485_, 0, v_val_481_);
                leanh::lean_ctor_set_uint8(
                    v___x_485_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_484_,
                );
                v___x_486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_486_, 0, v___x_483_);
                leanh::lean_ctor_set(v___x_486_, 1, v___x_485_);
                return v___x_486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = 0;
    v___x_490_ = l_Bool_toNat(v___x_489_);
    return v___x_490_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(
    mut v_aig_491_: *mut leanh::LeanObject,
    mut v_w_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
    mut v_curr_494_: *mut leanh::LeanObject,
    mut v_s_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_496_: u8 = 0;
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_496_ = lean_nat_dec_lt(v_curr_494_, v_w_492_);
                if v___x_496_ == 0 {
                    leanh::lean_dec(v_curr_494_);
                    leanh::lean_dec(v_a_493_);
                    leanh::lean_dec(v_w_492_);
                    v___x_497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_497_, 0, v_aig_491_);
                    leanh::lean_ctor_set(v___x_497_, 1, v_s_495_);
                    return v___x_497_;
                } else {
                    leanh::lean_inc(v_curr_494_);
                    leanh::lean_inc(v_w_492_);
                    leanh::lean_inc(v_a_493_);
                    v___x_498_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_498_, 0, v_a_493_);
                    leanh::lean_ctor_set(v___x_498_, 1, v_w_492_);
                    leanh::lean_ctor_set(v___x_498_, 2, v_curr_494_);
                    v_res_499_ = l_Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0(v_aig_491_, v___x_498_);
                    v_ref_500_ = leanh::lean_ctor_get(v_res_499_, 1);
                    leanh::lean_inc_ref(v_ref_500_);
                    v_aig_501_ = leanh::lean_ctor_get(v_res_499_, 0);
                    leanh::lean_inc_ref(v_aig_501_);
                    leanh::lean_dec_ref(v_res_499_);
                    v_gate_502_ = leanh::lean_ctor_get(v_ref_500_, 0);
                    leanh::lean_inc(v_gate_502_);
                    leanh::lean_dec_ref(v_ref_500_);
                    v___x_503_ = leanh::lean_unsigned_to_nat(1);
                    v___x_504_ = lean_nat_add(v_curr_494_, v___x_503_);
                    leanh::lean_dec(v_curr_494_);
                    v___x_505_ = leanh::lean_unsigned_to_nat(2);
                    v___x_506_ = lean_nat_mul(v_gate_502_, v___x_505_);
                    leanh::lean_dec(v_gate_502_);
                    v___x_507_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg___closed__0);
                    v___x_508_ = lean_nat_lor(v___x_506_, v___x_507_);
                    leanh::lean_dec(v___x_506_);
                    v_s_509_ = lean_array_push(v_s_495_, v___x_508_);
                    v_aig_491_ = v_aig_501_;
                    v_curr_494_ = v___x_504_;
                    v_s_495_ = v_s_509_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go(
    mut v_aig_511_: *mut leanh::LeanObject,
    mut v_w_512_: *mut leanh::LeanObject,
    mut v_a_513_: *mut leanh::LeanObject,
    mut v_curr_514_: *mut leanh::LeanObject,
    mut v_s_515_: *mut leanh::LeanObject,
    mut v_hcurr_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(
        v_aig_511_,
        v_w_512_,
        v_a_513_,
        v_curr_514_,
        v_s_515_,
    );
    return v___x_517_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(
    mut v_00_u03b2_518_: *mut leanh::LeanObject,
    mut v_m_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___redArg(v_m_519_, v_a_520_);
    return v___x_521_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_522_: *mut leanh::LeanObject,
    mut v_m_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0(v_00_u03b2_522_, v_m_523_, v_a_524_);
    leanh::lean_dec_ref(v_m_523_);
    return v_res_525_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1(
    mut v_00_u03b2_526_: *mut leanh::LeanObject,
    mut v_m_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
    mut v_b_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1___redArg(v_m_527_, v_a_528_, v_b_529_);
    return v___x_530_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2(
    mut v_00_u03b2_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_x_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__0_spec__2___redArg(v_a_532_, v_x_533_);
    return v___x_534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(
    mut v_00_u03b2_535_: *mut leanh::LeanObject,
    mut v_a_536_: *mut leanh::LeanObject,
    mut v_x_537_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_538_: u8 = 0;
    v___x_538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___redArg(v_a_536_, v_x_537_);
    return v___x_538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
    mut v_x_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_542_: u8 = 0;
    let mut v_r_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__4(v_00_u03b2_539_, v_a_540_, v_x_541_);
    v_r_543_ = leanh::lean_box((v_res_542_) as usize);
    return v_r_543_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5(
    mut v_00_u03b2_544_: *mut leanh::LeanObject,
    mut v_data_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5___redArg(v_data_545_);
    return v___x_546_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6(
    mut v_00_u03b2_547_: *mut leanh::LeanObject,
    mut v_a_548_: *mut leanh::LeanObject,
    mut v_b_549_: *mut leanh::LeanObject,
    mut v_x_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__6___redArg(v_a_548_, v_b_549_, v_x_550_);
    return v___x_551_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6(
    mut v_00_u03b2_552_: *mut leanh::LeanObject,
    mut v_i_553_: *mut leanh::LeanObject,
    mut v_source_554_: *mut leanh::LeanObject,
    mut v_target_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6___redArg(v_i_553_, v_source_554_, v_target_555_);
    return v___x_556_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7(
    mut v_00_u03b2_557_: *mut leanh::LeanObject,
    mut v_x_558_: *mut leanh::LeanObject,
    mut v_x_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_mkAtomCached___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_x_558_, v_x_559_);
    return v___x_560_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(
    mut v_c_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = lean_mk_empty_array_with_capacity(v_c_561_);
    return v___x_562_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg___boxed(
    mut v_c_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_564_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___redArg(v_c_563_);
    leanh::lean_dec(v_c_563_);
    return v_res_564_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(
    mut v_aig_565_: *mut leanh::LeanObject,
    mut v_c_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = lean_mk_empty_array_with_capacity(v_c_566_);
    return v___x_567_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0___boxed(
    mut v_aig_568_: *mut leanh::LeanObject,
    mut v_c_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___at___00Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_spec__0(v_aig_568_, v_c_569_);
    leanh::lean_dec(v_c_569_);
    leanh::lean_dec_ref(v_aig_568_);
    return v_res_570_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar(
    mut v_w_571_: *mut leanh::LeanObject,
    mut v_aig_572_: *mut leanh::LeanObject,
    mut v_var_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = leanh::lean_unsigned_to_nat(0);
    v___x_575_ = lean_mk_empty_array_with_capacity(v_w_571_);
    v___x_576_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastVar_go___redArg(
        v_aig_572_, v_w_571_, v_var_573_, v___x_574_, v___x_575_,
    );
    return v___x_576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Var(builtin);
}