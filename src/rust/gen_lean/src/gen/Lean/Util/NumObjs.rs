// Lean compiler output
// Module: Lean.Util.NumObjs
// Imports: Lean.Expr Lean.Util.PtrSet
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
use crate::r#gen::Lean::Util::PtrSet::{
    initialize_Lean_Util_PtrSet, l_Lean_mkPtrSet___redArg, runtime_initialize_Lean_Util_PtrSet,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_to_uint64,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::ffi::lean_ptr_addr;
static mut l_Lean_Expr_NumObjs_main___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_NumObjs_main___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_NumObjs_main___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_NumObjs_main___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(
    mut v_a_239_: *mut crate::leanh::LeanObject,
    mut v_x_240_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_241_: u8 = 0;
    let mut v_key_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: usize = 0;
    let mut v___x_245_: usize = 0;
    let mut v___x_246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_240_) == 0 {
                    v___x_241_ = 0;
                    return v___x_241_;
                } else {
                    v_key_242_ = crate::leanh::lean_ctor_get(v_x_240_, 0);
                    v_tail_243_ = crate::leanh::lean_ctor_get(v_x_240_, 2);
                    v___x_244_ = lean_ptr_addr(v_key_242_);
                    v___x_245_ = lean_ptr_addr(v_a_239_);
                    v___x_246_ = lean_usize_dec_eq(v___x_244_, v___x_245_);
                    if v___x_246_ == 0 {
                        v_x_240_ = v_tail_243_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_246_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_248_: *mut crate::leanh::LeanObject,
    mut v_x_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_250_: u8 = 0;
    let mut v_r_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_248_, v_x_249_);
    crate::leanh::lean_dec(v_x_249_);
    crate::leanh::lean_dec_ref(v_a_248_);
    v_r_251_ = crate::leanh::lean_box((v_res_250_) as usize);
    return v_r_251_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(
    mut v_m_252_: *mut crate::leanh::LeanObject,
    mut v_a_253_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: usize = 0;
    let mut v___x_257_: u64 = 0;
    let mut v___x_258_: u64 = 0;
    let mut v___x_259_: u64 = 0;
    let mut v___x_260_: u64 = 0;
    let mut v___x_261_: u64 = 0;
    let mut v_fold_262_: u64 = 0;
    let mut v___x_263_: u64 = 0;
    let mut v___x_264_: u64 = 0;
    let mut v___x_265_: u64 = 0;
    let mut v___x_266_: usize = 0;
    let mut v___x_267_: usize = 0;
    let mut v___x_268_: usize = 0;
    let mut v___x_269_: usize = 0;
    let mut v___x_270_: usize = 0;
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: u8 = 0;
    v_buckets_254_ = crate::leanh::lean_ctor_get(v_m_252_, 1);
    v___x_255_ = lean_array_get_size(v_buckets_254_);
    v___x_256_ = lean_ptr_addr(v_a_253_);
    v___x_257_ = lean_usize_to_uint64(v___x_256_);
    v___x_258_ = 11u64;
    v___x_259_ = lean_uint64_mix_hash(v___x_257_, v___x_258_);
    v___x_260_ = 32u64;
    v___x_261_ = lean_uint64_shift_right(v___x_259_, v___x_260_);
    v_fold_262_ = lean_uint64_xor(v___x_259_, v___x_261_);
    v___x_263_ = 16u64;
    v___x_264_ = lean_uint64_shift_right(v_fold_262_, v___x_263_);
    v___x_265_ = lean_uint64_xor(v_fold_262_, v___x_264_);
    v___x_266_ = lean_uint64_to_usize(v___x_265_);
    v___x_267_ = lean_usize_of_nat(v___x_255_);
    v___x_268_ = 1usize;
    v___x_269_ = lean_usize_sub(v___x_267_, v___x_268_);
    v___x_270_ = lean_usize_land(v___x_266_, v___x_269_);
    v___x_271_ = lean_array_uget_borrowed(v_buckets_254_, v___x_270_);
    v___x_272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_253_, v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg___boxed(
    mut v_m_273_: *mut crate::leanh::LeanObject,
    mut v_a_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_275_: u8 = 0;
    let mut v_r_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_275_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_273_, v_a_274_);
    crate::leanh::lean_dec_ref(v_a_274_);
    crate::leanh::lean_dec_ref(v_m_273_);
    v_r_276_ = crate::leanh::lean_box((v_res_275_) as usize);
    return v_r_276_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_277_: *mut crate::leanh::LeanObject,
    mut v_x_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_284_: u8 = 0;
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: usize = 0;
    let mut v___x_287_: u64 = 0;
    let mut v___x_288_: u64 = 0;
    let mut v___x_289_: u64 = 0;
    let mut v___x_290_: u64 = 0;
    let mut v___x_291_: u64 = 0;
    let mut v_fold_292_: u64 = 0;
    let mut v___x_293_: u64 = 0;
    let mut v___x_294_: u64 = 0;
    let mut v___x_295_: u64 = 0;
    let mut v___x_296_: usize = 0;
    let mut v___x_297_: usize = 0;
    let mut v___x_298_: usize = 0;
    let mut v___x_299_: usize = 0;
    let mut v___x_300_: usize = 0;
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_278_) == 0 {
                    return v_x_277_;
                } else {
                    v_key_279_ = crate::leanh::lean_ctor_get(v_x_278_, 0);
                    v_value_280_ = crate::leanh::lean_ctor_get(v_x_278_, 1);
                    v_tail_281_ = crate::leanh::lean_ctor_get(v_x_278_, 2);
                    v_isSharedCheck_307_ = (!crate::leanh::lean_is_exclusive(v_x_278_)) as u8;
                    if v_isSharedCheck_307_ == 0 {
                        v___x_283_ = v_x_278_;
                        v_isShared_284_ = v_isSharedCheck_307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_281_);
                        crate::leanh::lean_inc(v_value_280_);
                        crate::leanh::lean_inc(v_key_279_);
                        crate::leanh::lean_dec(v_x_278_);
                        v___x_283_ = crate::leanh::lean_box(0);
                        v_isShared_284_ = v_isSharedCheck_307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_285_ = lean_array_get_size(v_x_277_);
                v___x_286_ = lean_ptr_addr(v_key_279_);
                v___x_287_ = lean_usize_to_uint64(v___x_286_);
                v___x_288_ = 11u64;
                v___x_289_ = lean_uint64_mix_hash(v___x_287_, v___x_288_);
                v___x_290_ = 32u64;
                v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
                v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
                v___x_293_ = 16u64;
                v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
                v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
                v___x_296_ = lean_uint64_to_usize(v___x_295_);
                v___x_297_ = lean_usize_of_nat(v___x_285_);
                v___x_298_ = 1usize;
                v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
                v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
                v___x_301_ = lean_array_uget_borrowed(v_x_277_, v___x_300_);
                crate::leanh::lean_inc(v___x_301_);
                if v_isShared_284_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_283_, 2, v___x_301_);
                    v___x_303_ = v___x_283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_306_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 0, v_key_279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 1, v_value_280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_301_);
                    v___x_303_ = v_reuseFailAlloc_306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_304_ = lean_array_uset(v_x_277_, v___x_300_, v___x_303_);
                v_x_277_ = v___x_304_;
                v_x_278_ = v_tail_281_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(
    mut v_i_308_: *mut crate::leanh::LeanObject,
    mut v_source_309_: *mut crate::leanh::LeanObject,
    mut v_target_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: u8 = 0;
    let mut v_es_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_311_ = lean_array_get_size(v_source_309_);
                v___x_312_ = lean_nat_dec_lt(v_i_308_, v___x_311_);
                if v___x_312_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_309_);
                    crate::leanh::lean_dec(v_i_308_);
                    return v_target_310_;
                } else {
                    v_es_313_ = lean_array_fget(v_source_309_, v_i_308_);
                    v___x_314_ = crate::leanh::lean_box(0);
                    v_source_315_ = lean_array_fset(v_source_309_, v_i_308_, v___x_314_);
                    v_target_316_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_310_, v_es_313_);
                    v___x_317_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_318_ = lean_nat_add(v_i_308_, v___x_317_);
                    crate::leanh::lean_dec(v_i_308_);
                    v_i_308_ = v___x_318_;
                    v_source_309_ = v_source_315_;
                    v_target_310_ = v_target_316_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(
    mut v_data_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = lean_array_get_size(v_data_320_);
    v___x_322_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_323_ = lean_nat_mul(v___x_321_, v___x_322_);
    v___x_324_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_325_ = crate::leanh::lean_box(0);
    v___x_326_ = lean_mk_array(v_nbuckets_323_, v___x_325_);
    v___x_327_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v___x_324_, v_data_320_, v___x_326_);
    return v___x_327_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(
    mut v_m_328_: *mut crate::leanh::LeanObject,
    mut v_a_329_: *mut crate::leanh::LeanObject,
    mut v_b_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: usize = 0;
    let mut v___x_335_: u64 = 0;
    let mut v___x_336_: u64 = 0;
    let mut v___x_337_: u64 = 0;
    let mut v___x_338_: u64 = 0;
    let mut v___x_339_: u64 = 0;
    let mut v_fold_340_: u64 = 0;
    let mut v___x_341_: u64 = 0;
    let mut v___x_342_: u64 = 0;
    let mut v___x_343_: u64 = 0;
    let mut v___x_344_: usize = 0;
    let mut v___x_345_: usize = 0;
    let mut v___x_346_: usize = 0;
    let mut v___x_347_: usize = 0;
    let mut v___x_348_: usize = 0;
    let mut v_bkt_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: u8 = 0;
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: u8 = 0;
    let mut v_val_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_371_: u8 = 0;
    let mut v_unused_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_331_ = crate::leanh::lean_ctor_get(v_m_328_, 0);
                v_buckets_332_ = crate::leanh::lean_ctor_get(v_m_328_, 1);
                v___x_333_ = lean_array_get_size(v_buckets_332_);
                v___x_334_ = lean_ptr_addr(v_a_329_);
                v___x_335_ = lean_usize_to_uint64(v___x_334_);
                v___x_336_ = 11u64;
                v___x_337_ = lean_uint64_mix_hash(v___x_335_, v___x_336_);
                v___x_338_ = 32u64;
                v___x_339_ = lean_uint64_shift_right(v___x_337_, v___x_338_);
                v_fold_340_ = lean_uint64_xor(v___x_337_, v___x_339_);
                v___x_341_ = 16u64;
                v___x_342_ = lean_uint64_shift_right(v_fold_340_, v___x_341_);
                v___x_343_ = lean_uint64_xor(v_fold_340_, v___x_342_);
                v___x_344_ = lean_uint64_to_usize(v___x_343_);
                v___x_345_ = lean_usize_of_nat(v___x_333_);
                v___x_346_ = 1usize;
                v___x_347_ = lean_usize_sub(v___x_345_, v___x_346_);
                v___x_348_ = lean_usize_land(v___x_344_, v___x_347_);
                v_bkt_349_ = lean_array_uget_borrowed(v_buckets_332_, v___x_348_);
                v___x_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_329_, v_bkt_349_);
                if v___x_350_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_332_);
                    crate::leanh::lean_inc(v_size_331_);
                    v_isSharedCheck_371_ = (!crate::leanh::lean_is_exclusive(v_m_328_)) as u8;
                    if v_isSharedCheck_371_ == 0 {
                        v_unused_372_ = crate::leanh::lean_ctor_get(v_m_328_, 1);
                        crate::leanh::lean_dec(v_unused_372_);
                        v_unused_373_ = crate::leanh::lean_ctor_get(v_m_328_, 0);
                        crate::leanh::lean_dec(v_unused_373_);
                        v___x_352_ = v_m_328_;
                        v_isShared_353_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_328_);
                        v___x_352_ = crate::leanh::lean_box(0);
                        v_isShared_353_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_330_);
                    crate::leanh::lean_dec_ref(v_a_329_);
                    return v_m_328_;
                }
            }
            1 => {
                v___x_354_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_355_ = lean_nat_add(v_size_331_, v___x_354_);
                crate::leanh::lean_dec(v_size_331_);
                crate::leanh::lean_inc(v_bkt_349_);
                v___x_356_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_356_, 0, v_a_329_);
                crate::leanh::lean_ctor_set(v___x_356_, 1, v_b_330_);
                crate::leanh::lean_ctor_set(v___x_356_, 2, v_bkt_349_);
                v_buckets_x27_357_ = lean_array_uset(v_buckets_332_, v___x_348_, v___x_356_);
                v___x_358_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_359_ = lean_nat_mul(v_size_x27_355_, v___x_358_);
                v___x_360_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_361_ = lean_nat_div(v___x_359_, v___x_360_);
                crate::leanh::lean_dec(v___x_359_);
                v___x_362_ = lean_array_get_size(v_buckets_x27_357_);
                v___x_363_ = lean_nat_dec_le(v___x_361_, v___x_362_);
                crate::leanh::lean_dec(v___x_361_);
                if v___x_363_ == 0 {
                    v_val_364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_buckets_x27_357_);
                    if v_isShared_353_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_352_, 1, v_val_364_);
                        crate::leanh::lean_ctor_set(v___x_352_, 0, v_size_x27_355_);
                        v___x_366_ = v___x_352_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_x27_355_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_367_, 1, v_val_364_);
                        v___x_366_ = v_reuseFailAlloc_367_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_353_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_352_, 1, v_buckets_x27_357_);
                        crate::leanh::lean_ctor_set(v___x_352_, 0, v_size_x27_355_);
                        v___x_369_ = v___x_352_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_370_, 0, v_size_x27_355_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_370_, 1, v_buckets_x27_357_);
                        v___x_369_ = v_reuseFailAlloc_370_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_366_;
            }
            3 => {
                return v___x_369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_NumObjs_visit(
    mut v_e_374_: *mut crate::leanh::LeanObject,
    mut v_a_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counter_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: u8 = 0;
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_418_: u8 = 0;
    let mut v_unused_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_383_ = crate::leanh::lean_ctor_get(v_a_375_, 0);
                v_counter_384_ = crate::leanh::lean_ctor_get(v_a_375_, 1);
                v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_visited_383_, v_e_374_);
                if v___x_385_ == 0 {
                    crate::leanh::lean_inc(v_counter_384_);
                    crate::leanh::lean_inc_ref(v_visited_383_);
                    v_isSharedCheck_418_ = (!crate::leanh::lean_is_exclusive(v_a_375_)) as u8;
                    if v_isSharedCheck_418_ == 0 {
                        v_unused_419_ = crate::leanh::lean_ctor_get(v_a_375_, 1);
                        crate::leanh::lean_dec(v_unused_419_);
                        v_unused_420_ = crate::leanh::lean_ctor_get(v_a_375_, 0);
                        crate::leanh::lean_dec(v_unused_420_);
                        v___x_387_ = v_a_375_;
                        v_isShared_388_ = v_isSharedCheck_418_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_375_);
                        v___x_387_ = crate::leanh::lean_box(0);
                        v_isShared_388_ = v_isSharedCheck_418_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_374_);
                    v___x_421_ = crate::leanh::lean_box(0);
                    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
                    crate::leanh::lean_ctor_set(v___x_422_, 1, v_a_375_);
                    return v___x_422_;
                }
            }
            1 => {
                v___x_380_ = l_Lean_Expr_NumObjs_visit(v_d_377_, v___y_379_);
                v_snd_381_ = crate::leanh::lean_ctor_get(v___x_380_, 1);
                crate::leanh::lean_inc(v_snd_381_);
                crate::leanh::lean_dec_ref(v___x_380_);
                v_e_374_ = v_b_378_;
                v_a_375_ = v_snd_381_;
                state = 0;
                continue;
            }
            2 => {
                v___x_389_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_374_);
                v___x_390_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_visited_383_, v_e_374_, v___x_389_);
                v___x_391_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_392_ = lean_nat_add(v_counter_384_, v___x_391_);
                crate::leanh::lean_dec(v_counter_384_);
                if v_isShared_388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_387_, 1, v___x_392_);
                    crate::leanh::lean_ctor_set(v___x_387_, 0, v___x_390_);
                    v___x_394_ = v___x_387_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_392_);
                    v___x_394_ = v_reuseFailAlloc_417_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_e_374_) {
                7 => {
                    v_binderType_395_ = crate::leanh::lean_ctor_get(v_e_374_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_395_);
                    v_body_396_ = crate::leanh::lean_ctor_get(v_e_374_, 2);
                    crate::leanh::lean_inc_ref(v_body_396_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 3);
                    v_d_377_ = v_binderType_395_;
                    v_b_378_ = v_body_396_;
                    v___y_379_ = v___x_394_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_397_ = crate::leanh::lean_ctor_get(v_e_374_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_397_);
                    v_body_398_ = crate::leanh::lean_ctor_get(v_e_374_, 2);
                    crate::leanh::lean_inc_ref(v_body_398_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 3);
                    v_d_377_ = v_binderType_397_;
                    v_b_378_ = v_body_398_;
                    v___y_379_ = v___x_394_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_expr_399_ = crate::leanh::lean_ctor_get(v_e_374_, 1);
                    crate::leanh::lean_inc_ref(v_expr_399_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 2);
                    v_e_374_ = v_expr_399_;
                    v_a_375_ = v___x_394_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_type_401_ = crate::leanh::lean_ctor_get(v_e_374_, 1);
                    crate::leanh::lean_inc_ref(v_type_401_);
                    v_value_402_ = crate::leanh::lean_ctor_get(v_e_374_, 2);
                    crate::leanh::lean_inc_ref(v_value_402_);
                    v_body_403_ = crate::leanh::lean_ctor_get(v_e_374_, 3);
                    crate::leanh::lean_inc_ref(v_body_403_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 4);
                    v___x_404_ = l_Lean_Expr_NumObjs_visit(v_type_401_, v___x_394_);
                    v_snd_405_ = crate::leanh::lean_ctor_get(v___x_404_, 1);
                    crate::leanh::lean_inc(v_snd_405_);
                    crate::leanh::lean_dec_ref(v___x_404_);
                    v___x_406_ = l_Lean_Expr_NumObjs_visit(v_value_402_, v_snd_405_);
                    v_snd_407_ = crate::leanh::lean_ctor_get(v___x_406_, 1);
                    crate::leanh::lean_inc(v_snd_407_);
                    crate::leanh::lean_dec_ref(v___x_406_);
                    v_e_374_ = v_body_403_;
                    v_a_375_ = v_snd_407_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_fn_409_ = crate::leanh::lean_ctor_get(v_e_374_, 0);
                    crate::leanh::lean_inc_ref(v_fn_409_);
                    v_arg_410_ = crate::leanh::lean_ctor_get(v_e_374_, 1);
                    crate::leanh::lean_inc_ref(v_arg_410_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 2);
                    v___x_411_ = l_Lean_Expr_NumObjs_visit(v_fn_409_, v___x_394_);
                    v_snd_412_ = crate::leanh::lean_ctor_get(v___x_411_, 1);
                    crate::leanh::lean_inc(v_snd_412_);
                    crate::leanh::lean_dec_ref(v___x_411_);
                    v_e_374_ = v_arg_410_;
                    v_a_375_ = v_snd_412_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_414_ = crate::leanh::lean_ctor_get(v_e_374_, 2);
                    crate::leanh::lean_inc_ref(v_struct_414_);
                    crate::leanh::lean_dec_ref_known(v_e_374_, 3);
                    v_e_374_ = v_struct_414_;
                    v_a_375_ = v___x_394_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_374_);
                    v___x_416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_389_);
                    crate::leanh::lean_ctor_set(v___x_416_, 1, v___x_394_);
                    return v___x_416_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(
    mut v_00_u03b2_423_: *mut crate::leanh::LeanObject,
    mut v_m_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_426_: u8 = 0;
    v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___redArg(v_m_424_, v_a_425_);
    return v___x_426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0___boxed(
    mut v_00_u03b2_427_: *mut crate::leanh::LeanObject,
    mut v_m_428_: *mut crate::leanh::LeanObject,
    mut v_a_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0(
            v_00_u03b2_427_,
            v_m_428_,
            v_a_429_,
        );
    crate::leanh::lean_dec_ref(v_a_429_);
    crate::leanh::lean_dec_ref(v_m_428_);
    v_r_431_ = crate::leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1(
    mut v_00_u03b2_432_: *mut crate::leanh::LeanObject,
    mut v_m_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_b_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1___redArg(v_m_433_, v_a_434_, v_b_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(
    mut v_00_u03b2_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_x_439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_440_: u8 = 0;
    v___x_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___redArg(v_a_438_, v_x_439_);
    return v___x_440_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
    mut v_x_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_444_: u8 = 0;
    let mut v_r_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumObjs_visit_spec__0_spec__0(v_00_u03b2_441_, v_a_442_, v_x_443_);
    crate::leanh::lean_dec(v_x_443_);
    crate::leanh::lean_dec_ref(v_a_442_);
    v_r_445_ = crate::leanh::lean_box((v_res_444_) as usize);
    return v_r_445_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2(
    mut v_00_u03b2_446_: *mut crate::leanh::LeanObject,
    mut v_data_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2___redArg(v_data_447_);
    return v___x_448_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3(
    mut v_00_u03b2_449_: *mut crate::leanh::LeanObject,
    mut v_i_450_: *mut crate::leanh::LeanObject,
    mut v_source_451_: *mut crate::leanh::LeanObject,
    mut v_target_452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3___redArg(v_i_450_, v_source_451_, v_target_452_);
    return v___x_453_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumObjs_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_455_, v_x_456_);
    return v___x_457_;
}
pub unsafe fn _init_l_Lean_Expr_NumObjs_main___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_459_ = l_Lean_mkPtrSet___redArg(v___x_458_);
    return v___x_459_;
}
pub unsafe fn _init_l_Lean_Expr_NumObjs_main___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_461_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_NumObjs_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_NumObjs_main___closed__0_once),
        _init_l_Lean_Expr_NumObjs_main___closed__0,
    );
    v___x_462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_462_, 0, v___x_461_);
    crate::leanh::lean_ctor_set(v___x_462_, 1, v___x_460_);
    return v___x_462_;
}
pub unsafe fn l_Lean_Expr_NumObjs_main(
    mut v_e_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counter_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_NumObjs_main___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_NumObjs_main___closed__1_once),
        _init_l_Lean_Expr_NumObjs_main___closed__1,
    );
    v___x_465_ = l_Lean_Expr_NumObjs_visit(v_e_463_, v___x_464_);
    v_snd_466_ = crate::leanh::lean_ctor_get(v___x_465_, 1);
    crate::leanh::lean_inc(v_snd_466_);
    crate::leanh::lean_dec_ref(v___x_465_);
    v_counter_467_ = crate::leanh::lean_ctor_get(v_snd_466_, 1);
    crate::leanh::lean_inc(v_counter_467_);
    crate::leanh::lean_dec(v_snd_466_);
    return v_counter_467_;
}
pub unsafe fn l___private_Lean_Util_NumObjs_0__Lean_Expr_numObjs_unsafe__1(
    mut v_e_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = l_Lean_Expr_NumObjs_main(v_e_468_);
    return v___x_469_;
}
pub unsafe fn l_Lean_Expr_numObjs(
    mut v_e_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = l_Lean_Expr_NumObjs_main(v_e_470_);
    v___x_473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
    return v___x_473_;
}
pub unsafe fn l_Lean_Expr_numObjs___boxed(
    mut v_e_474_: *mut crate::leanh::LeanObject,
    mut v_a_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Expr_numObjs(v_e_474_);
    return v_res_476_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_NumObjs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_NumObjs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_NumObjs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumObjs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_NumObjs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_NumObjs(builtin);
}
