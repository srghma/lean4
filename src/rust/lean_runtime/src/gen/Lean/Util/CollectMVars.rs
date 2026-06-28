// Lean compiler output
// Module: Lean.Util.CollectMVars
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasExprMVar, l_Lean_Expr_hash, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
static mut l_Lean_CollectMVars_instInhabitedState___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CollectMVars_instInhabitedState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CollectMVars_instInhabitedState___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CollectMVars_instInhabitedState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CollectMVars_instInhabitedState___closed__2_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_CollectMVars_instInhabitedState___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CollectMVars_instInhabitedState___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_CollectMVars_instInhabitedState___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CollectMVars_instInhabitedState___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_CollectMVars_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_CollectMVars_instInhabitedState___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = crate::leanh::lean_box(0);
    v___x_231_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_232_ = lean_mk_array(v___x_231_, v___x_230_);
    return v___x_232_;
}
pub unsafe fn _init_l_Lean_CollectMVars_instInhabitedState___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_233_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__0_once),
        _init_l_Lean_CollectMVars_instInhabitedState___closed__0,
    );
    v___x_234_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_235_, 0, v___x_234_);
    crate::leanh::lean_ctor_set(v___x_235_, 1, v___x_233_);
    return v___x_235_;
}
pub unsafe fn _init_l_Lean_CollectMVars_instInhabitedState___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = l_Lean_CollectMVars_instInhabitedState___closed__2;
    v___x_239_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__1_once),
        _init_l_Lean_CollectMVars_instInhabitedState___closed__1,
    );
    v___x_240_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_240_, 0, v___x_239_);
    crate::leanh::lean_ctor_set(v___x_240_, 1, v___x_238_);
    return v___x_240_;
}
pub unsafe fn _init_l_Lean_CollectMVars_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__3),
        core::ptr::addr_of_mut!(l_Lean_CollectMVars_instInhabitedState___closed__3_once),
        _init_l_Lean_CollectMVars_instInhabitedState___closed__3,
    );
    return v___x_241_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(
    mut v_a_242_: *mut crate::leanh::LeanObject,
    mut v_x_243_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_244_: u8 = 0;
    let mut v_key_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_243_) == 0 {
                    v___x_244_ = 0;
                    return v___x_244_;
                } else {
                    v_key_245_ = crate::leanh::lean_ctor_get(v_x_243_, 0);
                    v_tail_246_ = crate::leanh::lean_ctor_get(v_x_243_, 2);
                    v___x_247_ = lean_expr_eqv(v_key_245_, v_a_242_);
                    if v___x_247_ == 0 {
                        v_x_243_ = v_tail_246_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_247_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(
    mut v_a_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_251_: u8 = 0;
    let mut v_r_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_249_, v_x_250_);
    crate::leanh::lean_dec(v_x_250_);
    crate::leanh::lean_dec_ref(v_a_249_);
    v_r_252_ = crate::leanh::lean_box((v_res_251_) as usize);
    return v_r_252_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(
    mut v_m_253_: *mut crate::leanh::LeanObject,
    mut v_a_254_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u64 = 0;
    let mut v___x_258_: u64 = 0;
    let mut v___x_259_: u64 = 0;
    let mut v_fold_260_: u64 = 0;
    let mut v___x_261_: u64 = 0;
    let mut v___x_262_: u64 = 0;
    let mut v___x_263_: u64 = 0;
    let mut v___x_264_: usize = 0;
    let mut v___x_265_: usize = 0;
    let mut v___x_266_: usize = 0;
    let mut v___x_267_: usize = 0;
    let mut v___x_268_: usize = 0;
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: u8 = 0;
    v_buckets_255_ = crate::leanh::lean_ctor_get(v_m_253_, 1);
    v___x_256_ = lean_array_get_size(v_buckets_255_);
    v___x_257_ = l_Lean_Expr_hash(v_a_254_);
    v___x_258_ = 32u64;
    v___x_259_ = lean_uint64_shift_right(v___x_257_, v___x_258_);
    v_fold_260_ = lean_uint64_xor(v___x_257_, v___x_259_);
    v___x_261_ = 16u64;
    v___x_262_ = lean_uint64_shift_right(v_fold_260_, v___x_261_);
    v___x_263_ = lean_uint64_xor(v_fold_260_, v___x_262_);
    v___x_264_ = lean_uint64_to_usize(v___x_263_);
    v___x_265_ = lean_usize_of_nat(v___x_256_);
    v___x_266_ = 1usize;
    v___x_267_ = lean_usize_sub(v___x_265_, v___x_266_);
    v___x_268_ = lean_usize_land(v___x_264_, v___x_267_);
    v___x_269_ = lean_array_uget_borrowed(v_buckets_255_, v___x_268_);
    v___x_270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_254_, v___x_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(
    mut v_m_271_: *mut crate::leanh::LeanObject,
    mut v_a_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_273_: u8 = 0;
    let mut v_r_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_271_, v_a_272_);
    crate::leanh::lean_dec_ref(v_a_272_);
    crate::leanh::lean_dec_ref(v_m_271_);
    v_r_274_ = crate::leanh::lean_box((v_res_273_) as usize);
    return v_r_274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_275_: *mut crate::leanh::LeanObject,
    mut v_x_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_282_: u8 = 0;
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: u64 = 0;
    let mut v___x_285_: u64 = 0;
    let mut v___x_286_: u64 = 0;
    let mut v_fold_287_: u64 = 0;
    let mut v___x_288_: u64 = 0;
    let mut v___x_289_: u64 = 0;
    let mut v___x_290_: u64 = 0;
    let mut v___x_291_: usize = 0;
    let mut v___x_292_: usize = 0;
    let mut v___x_293_: usize = 0;
    let mut v___x_294_: usize = 0;
    let mut v___x_295_: usize = 0;
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_276_) == 0 {
                    return v_x_275_;
                } else {
                    v_key_277_ = crate::leanh::lean_ctor_get(v_x_276_, 0);
                    v_value_278_ = crate::leanh::lean_ctor_get(v_x_276_, 1);
                    v_tail_279_ = crate::leanh::lean_ctor_get(v_x_276_, 2);
                    v_isSharedCheck_302_ = (!crate::leanh::lean_is_exclusive(v_x_276_)) as u8;
                    if v_isSharedCheck_302_ == 0 {
                        v___x_281_ = v_x_276_;
                        v_isShared_282_ = v_isSharedCheck_302_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_279_);
                        crate::leanh::lean_inc(v_value_278_);
                        crate::leanh::lean_inc(v_key_277_);
                        crate::leanh::lean_dec(v_x_276_);
                        v___x_281_ = crate::leanh::lean_box(0);
                        v_isShared_282_ = v_isSharedCheck_302_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_283_ = lean_array_get_size(v_x_275_);
                v___x_284_ = l_Lean_Expr_hash(v_key_277_);
                v___x_285_ = 32u64;
                v___x_286_ = lean_uint64_shift_right(v___x_284_, v___x_285_);
                v_fold_287_ = lean_uint64_xor(v___x_284_, v___x_286_);
                v___x_288_ = 16u64;
                v___x_289_ = lean_uint64_shift_right(v_fold_287_, v___x_288_);
                v___x_290_ = lean_uint64_xor(v_fold_287_, v___x_289_);
                v___x_291_ = lean_uint64_to_usize(v___x_290_);
                v___x_292_ = lean_usize_of_nat(v___x_283_);
                v___x_293_ = 1usize;
                v___x_294_ = lean_usize_sub(v___x_292_, v___x_293_);
                v___x_295_ = lean_usize_land(v___x_291_, v___x_294_);
                v___x_296_ = lean_array_uget_borrowed(v_x_275_, v___x_295_);
                crate::leanh::lean_inc(v___x_296_);
                if v_isShared_282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_281_, 2, v___x_296_);
                    v___x_298_ = v___x_281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_301_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_301_, 0, v_key_277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_301_, 1, v_value_278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_301_, 2, v___x_296_);
                    v___x_298_ = v_reuseFailAlloc_301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_299_ = lean_array_uset(v_x_275_, v___x_295_, v___x_298_);
                v_x_275_ = v___x_299_;
                v_x_276_ = v_tail_279_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(
    mut v_i_303_: *mut crate::leanh::LeanObject,
    mut v_source_304_: *mut crate::leanh::LeanObject,
    mut v_target_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: u8 = 0;
    let mut v_es_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_306_ = lean_array_get_size(v_source_304_);
                v___x_307_ = lean_nat_dec_lt(v_i_303_, v___x_306_);
                if v___x_307_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_304_);
                    crate::leanh::lean_dec(v_i_303_);
                    return v_target_305_;
                } else {
                    v_es_308_ = lean_array_fget(v_source_304_, v_i_303_);
                    v___x_309_ = crate::leanh::lean_box(0);
                    v_source_310_ = lean_array_fset(v_source_304_, v_i_303_, v___x_309_);
                    v_target_311_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_target_305_, v_es_308_);
                    v___x_312_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_313_ = lean_nat_add(v_i_303_, v___x_312_);
                    crate::leanh::lean_dec(v_i_303_);
                    v_i_303_ = v___x_313_;
                    v_source_304_ = v_source_310_;
                    v_target_305_ = v_target_311_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(
    mut v_data_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = lean_array_get_size(v_data_315_);
    v___x_317_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_318_ = lean_nat_mul(v___x_316_, v___x_317_);
    v___x_319_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_320_ = crate::leanh::lean_box(0);
    v___x_321_ = lean_mk_array(v_nbuckets_318_, v___x_320_);
    v___x_322_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(v___x_319_, v_data_315_, v___x_321_);
    return v___x_322_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(
    mut v_m_323_: *mut crate::leanh::LeanObject,
    mut v_a_324_: *mut crate::leanh::LeanObject,
    mut v_b_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: u64 = 0;
    let mut v___x_330_: u64 = 0;
    let mut v___x_331_: u64 = 0;
    let mut v_fold_332_: u64 = 0;
    let mut v___x_333_: u64 = 0;
    let mut v___x_334_: u64 = 0;
    let mut v___x_335_: u64 = 0;
    let mut v___x_336_: usize = 0;
    let mut v___x_337_: usize = 0;
    let mut v___x_338_: usize = 0;
    let mut v___x_339_: usize = 0;
    let mut v___x_340_: usize = 0;
    let mut v_bkt_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: u8 = 0;
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    let mut v_val_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_363_: u8 = 0;
    let mut v_unused_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_326_ = crate::leanh::lean_ctor_get(v_m_323_, 0);
                v_buckets_327_ = crate::leanh::lean_ctor_get(v_m_323_, 1);
                v___x_328_ = lean_array_get_size(v_buckets_327_);
                v___x_329_ = l_Lean_Expr_hash(v_a_324_);
                v___x_330_ = 32u64;
                v___x_331_ = lean_uint64_shift_right(v___x_329_, v___x_330_);
                v_fold_332_ = lean_uint64_xor(v___x_329_, v___x_331_);
                v___x_333_ = 16u64;
                v___x_334_ = lean_uint64_shift_right(v_fold_332_, v___x_333_);
                v___x_335_ = lean_uint64_xor(v_fold_332_, v___x_334_);
                v___x_336_ = lean_uint64_to_usize(v___x_335_);
                v___x_337_ = lean_usize_of_nat(v___x_328_);
                v___x_338_ = 1usize;
                v___x_339_ = lean_usize_sub(v___x_337_, v___x_338_);
                v___x_340_ = lean_usize_land(v___x_336_, v___x_339_);
                v_bkt_341_ = lean_array_uget_borrowed(v_buckets_327_, v___x_340_);
                v___x_342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_324_, v_bkt_341_);
                if v___x_342_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_327_);
                    crate::leanh::lean_inc(v_size_326_);
                    v_isSharedCheck_363_ = (!crate::leanh::lean_is_exclusive(v_m_323_)) as u8;
                    if v_isSharedCheck_363_ == 0 {
                        v_unused_364_ = crate::leanh::lean_ctor_get(v_m_323_, 1);
                        crate::leanh::lean_dec(v_unused_364_);
                        v_unused_365_ = crate::leanh::lean_ctor_get(v_m_323_, 0);
                        crate::leanh::lean_dec(v_unused_365_);
                        v___x_344_ = v_m_323_;
                        v_isShared_345_ = v_isSharedCheck_363_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_323_);
                        v___x_344_ = crate::leanh::lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_363_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_325_);
                    crate::leanh::lean_dec_ref(v_a_324_);
                    return v_m_323_;
                }
            }
            1 => {
                v___x_346_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_347_ = lean_nat_add(v_size_326_, v___x_346_);
                crate::leanh::lean_dec(v_size_326_);
                crate::leanh::lean_inc(v_bkt_341_);
                v___x_348_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_348_, 0, v_a_324_);
                crate::leanh::lean_ctor_set(v___x_348_, 1, v_b_325_);
                crate::leanh::lean_ctor_set(v___x_348_, 2, v_bkt_341_);
                v_buckets_x27_349_ = lean_array_uset(v_buckets_327_, v___x_340_, v___x_348_);
                v___x_350_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_351_ = lean_nat_mul(v_size_x27_347_, v___x_350_);
                v___x_352_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_353_ = lean_nat_div(v___x_351_, v___x_352_);
                crate::leanh::lean_dec(v___x_351_);
                v___x_354_ = lean_array_get_size(v_buckets_x27_349_);
                v___x_355_ = lean_nat_dec_le(v___x_353_, v___x_354_);
                crate::leanh::lean_dec(v___x_353_);
                if v___x_355_ == 0 {
                    v_val_356_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_buckets_x27_349_);
                    if v_isShared_345_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_344_, 1, v_val_356_);
                        crate::leanh::lean_ctor_set(v___x_344_, 0, v_size_x27_347_);
                        v___x_358_ = v___x_344_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 0, v_size_x27_347_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 1, v_val_356_);
                        v___x_358_ = v_reuseFailAlloc_359_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_345_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_344_, 1, v_buckets_x27_349_);
                        crate::leanh::lean_ctor_set(v___x_344_, 0, v_size_x27_347_);
                        v___x_361_ = v___x_344_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_362_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_347_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_362_, 1, v_buckets_x27_349_);
                        v___x_361_ = v_reuseFailAlloc_362_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_358_;
            }
            3 => {
                return v___x_361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectMVars_main(
    mut v_x_366_: *mut crate::leanh::LeanObject,
    mut v_a_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_397_: u8 = 0;
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_366_) {
                11 => {
                    v_struct_374_ = crate::leanh::lean_ctor_get(v_x_366_, 2);
                    crate::leanh::lean_inc_ref(v_struct_374_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 3);
                    v___x_375_ = l_Lean_CollectMVars_visit(v_struct_374_, v_a_367_);
                    return v___x_375_;
                }
                7 => {
                    v_binderType_376_ = crate::leanh::lean_ctor_get(v_x_366_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_376_);
                    v_body_377_ = crate::leanh::lean_ctor_get(v_x_366_, 2);
                    crate::leanh::lean_inc_ref(v_body_377_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 3);
                    v_d_369_ = v_binderType_376_;
                    v_b_370_ = v_body_377_;
                    v___y_371_ = v_a_367_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_378_ = crate::leanh::lean_ctor_get(v_x_366_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_378_);
                    v_body_379_ = crate::leanh::lean_ctor_get(v_x_366_, 2);
                    crate::leanh::lean_inc_ref(v_body_379_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 3);
                    v_d_369_ = v_binderType_378_;
                    v_b_370_ = v_body_379_;
                    v___y_371_ = v_a_367_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_380_ = crate::leanh::lean_ctor_get(v_x_366_, 1);
                    crate::leanh::lean_inc_ref(v_type_380_);
                    v_value_381_ = crate::leanh::lean_ctor_get(v_x_366_, 2);
                    crate::leanh::lean_inc_ref(v_value_381_);
                    v_body_382_ = crate::leanh::lean_ctor_get(v_x_366_, 3);
                    crate::leanh::lean_inc_ref(v_body_382_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 4);
                    v___x_383_ = l_Lean_CollectMVars_visit(v_type_380_, v_a_367_);
                    v___x_384_ = l_Lean_CollectMVars_visit(v_value_381_, v___x_383_);
                    v___x_385_ = l_Lean_CollectMVars_visit(v_body_382_, v___x_384_);
                    return v___x_385_;
                }
                5 => {
                    v_fn_386_ = crate::leanh::lean_ctor_get(v_x_366_, 0);
                    crate::leanh::lean_inc_ref(v_fn_386_);
                    v_arg_387_ = crate::leanh::lean_ctor_get(v_x_366_, 1);
                    crate::leanh::lean_inc_ref(v_arg_387_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 2);
                    v___x_388_ = l_Lean_CollectMVars_visit(v_fn_386_, v_a_367_);
                    v___x_389_ = l_Lean_CollectMVars_visit(v_arg_387_, v___x_388_);
                    return v___x_389_;
                }
                10 => {
                    v_expr_390_ = crate::leanh::lean_ctor_get(v_x_366_, 1);
                    crate::leanh::lean_inc_ref(v_expr_390_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 2);
                    v___x_391_ = l_Lean_CollectMVars_visit(v_expr_390_, v_a_367_);
                    return v___x_391_;
                }
                2 => {
                    v_mvarId_392_ = crate::leanh::lean_ctor_get(v_x_366_, 0);
                    crate::leanh::lean_inc(v_mvarId_392_);
                    crate::leanh::lean_dec_ref_known(v_x_366_, 1);
                    v_visitedExpr_393_ = crate::leanh::lean_ctor_get(v_a_367_, 0);
                    v_result_394_ = crate::leanh::lean_ctor_get(v_a_367_, 1);
                    v_isSharedCheck_402_ = (!crate::leanh::lean_is_exclusive(v_a_367_)) as u8;
                    if v_isSharedCheck_402_ == 0 {
                        v___x_396_ = v_a_367_;
                        v_isShared_397_ = v_isSharedCheck_402_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_result_394_);
                        crate::leanh::lean_inc(v_visitedExpr_393_);
                        crate::leanh::lean_dec(v_a_367_);
                        v___x_396_ = crate::leanh::lean_box(0);
                        v_isShared_397_ = v_isSharedCheck_402_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_366_);
                    return v_a_367_;
                }
            },
            1 => {
                v___x_372_ = l_Lean_CollectMVars_visit(v_d_369_, v___y_371_);
                v___x_373_ = l_Lean_CollectMVars_visit(v_b_370_, v___x_372_);
                return v___x_373_;
            }
            2 => {
                v___x_398_ = lean_array_push(v_result_394_, v_mvarId_392_);
                if v_isShared_397_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_396_, 1, v___x_398_);
                    v___x_400_ = v___x_396_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_401_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v_visitedExpr_393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_398_);
                    v___x_400_ = v_reuseFailAlloc_401_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectMVars_visit(
    mut v_e_403_: *mut crate::leanh::LeanObject,
    mut v_s_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_405_: u8 = 0;
    let mut v_visitedExpr_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: u8 = 0;
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_411_: u8 = 0;
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_418_: u8 = 0;
    let mut v_unused_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_405_ = l_Lean_Expr_hasExprMVar(v_e_403_);
                if v___x_405_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_403_);
                    return v_s_404_;
                } else {
                    v_visitedExpr_406_ = crate::leanh::lean_ctor_get(v_s_404_, 0);
                    v_result_407_ = crate::leanh::lean_ctor_get(v_s_404_, 1);
                    v___x_408_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_visitedExpr_406_, v_e_403_);
                    if v___x_408_ == 0 {
                        crate::leanh::lean_inc_ref(v_result_407_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_406_);
                        v_isSharedCheck_418_ = (!crate::leanh::lean_is_exclusive(v_s_404_)) as u8;
                        if v_isSharedCheck_418_ == 0 {
                            v_unused_419_ = crate::leanh::lean_ctor_get(v_s_404_, 1);
                            crate::leanh::lean_dec(v_unused_419_);
                            v_unused_420_ = crate::leanh::lean_ctor_get(v_s_404_, 0);
                            crate::leanh::lean_dec(v_unused_420_);
                            v___x_410_ = v_s_404_;
                            v_isShared_411_ = v_isSharedCheck_418_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_404_);
                            v___x_410_ = crate::leanh::lean_box(0);
                            v_isShared_411_ = v_isSharedCheck_418_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_403_);
                        return v_s_404_;
                    }
                }
            }
            1 => {
                v___x_412_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_403_);
                v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_visitedExpr_406_, v_e_403_, v___x_412_);
                if v_isShared_411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_410_, 0, v___x_413_);
                    v___x_415_ = v___x_410_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_417_, 1, v_result_407_);
                    v___x_415_ = v_reuseFailAlloc_417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_416_ = l_Lean_CollectMVars_main(v_e_403_, v___x_415_);
                return v___x_416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(
    mut v_00_u03b2_421_: *mut crate::leanh::LeanObject,
    mut v_m_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_424_: u8 = 0;
    v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_422_, v_a_423_);
    return v___x_424_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(
    mut v_00_u03b2_425_: *mut crate::leanh::LeanObject,
    mut v_m_426_: *mut crate::leanh::LeanObject,
    mut v_a_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_428_: u8 = 0;
    let mut v_r_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(
            v_00_u03b2_425_,
            v_m_426_,
            v_a_427_,
        );
    crate::leanh::lean_dec_ref(v_a_427_);
    crate::leanh::lean_dec_ref(v_m_426_);
    v_r_429_ = crate::leanh::lean_box((v_res_428_) as usize);
    return v_r_429_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1(
    mut v_00_u03b2_430_: *mut crate::leanh::LeanObject,
    mut v_m_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
    mut v_b_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_431_, v_a_432_, v_b_433_);
    return v___x_434_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(
    mut v_00_u03b2_435_: *mut crate::leanh::LeanObject,
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_x_437_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_438_: u8 = 0;
    v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_a_436_, v_x_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(
    mut v_00_u03b2_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: u8 = 0;
    let mut v_r_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(v_00_u03b2_439_, v_a_440_, v_x_441_);
    crate::leanh::lean_dec(v_x_441_);
    crate::leanh::lean_dec_ref(v_a_440_);
    v_r_443_ = crate::leanh::lean_box((v_res_442_) as usize);
    return v_r_443_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3(
    mut v_00_u03b2_444_: *mut crate::leanh::LeanObject,
    mut v_data_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_data_445_);
    return v___x_446_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4(
    mut v_00_u03b2_447_: *mut crate::leanh::LeanObject,
    mut v_i_448_: *mut crate::leanh::LeanObject,
    mut v_source_449_: *mut crate::leanh::LeanObject,
    mut v_target_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4___redArg(v_i_448_, v_source_449_, v_target_450_);
    return v___x_451_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_452_: *mut crate::leanh::LeanObject,
    mut v_x_453_: *mut crate::leanh::LeanObject,
    mut v_x_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectMVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_x_453_, v_x_454_);
    return v___x_455_;
}
pub unsafe fn l_Lean_Expr_collectMVars(
    mut v_s_456_: *mut crate::leanh::LeanObject,
    mut v_e_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Lean_CollectMVars_visit(v_e_457_, v_s_456_);
    return v___x_458_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectMVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    l_Lean_CollectMVars_instInhabitedState = _init_l_Lean_CollectMVars_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectMVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_CollectMVars(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectMVars(builtin);
}
