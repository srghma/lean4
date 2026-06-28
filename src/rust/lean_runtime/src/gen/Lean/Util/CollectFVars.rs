// Lean compiler output
// Module: Lean.Util.CollectFVars
// Imports: Lean.LocalContext
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasFVar, l_Lean_Expr_hash, l_Lean_FVarIdSet_insert};
use crate::r#gen::Lean::LocalContext::{
    initialize_Lean_LocalContext, runtime_initialize_Lean_LocalContext,
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
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_CollectFVars_instInhabitedState_default___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CollectFVars_instInhabitedState_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectFVars_instInhabitedState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_CollectFVars_instInhabitedState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_CollectFVars_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = crate::leanh::lean_box(0);
    v___x_240_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_241_ = lean_mk_array(v___x_240_, v___x_239_);
    return v___x_241_;
}
pub unsafe fn _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_242_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__0_once),
        _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0,
    );
    v___x_243_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_244_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_244_, 0, v___x_243_);
    crate::leanh::lean_ctor_set(v___x_244_, 1, v___x_242_);
    return v___x_244_;
}
pub unsafe fn _init_l_Lean_CollectFVars_instInhabitedState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = l_Lean_CollectFVars_instInhabitedState_default___closed__2;
    v___x_248_ = crate::leanh::lean_box(1);
    v___x_249_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__1_once),
        _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1,
    );
    v___x_250_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
    crate::leanh::lean_ctor_set(v___x_250_, 1, v___x_248_);
    crate::leanh::lean_ctor_set(v___x_250_, 2, v___x_247_);
    return v___x_250_;
}
pub unsafe fn _init_l_Lean_CollectFVars_instInhabitedState_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_CollectFVars_instInhabitedState_default___closed__3_once),
        _init_l_Lean_CollectFVars_instInhabitedState_default___closed__3,
    );
    return v___x_251_;
}
pub unsafe fn _init_l_Lean_CollectFVars_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Lean_CollectFVars_instInhabitedState_default;
    return v___x_252_;
}
pub unsafe fn l_Lean_CollectFVars_State_add(
    mut v_s_253_: *mut crate::leanh::LeanObject,
    mut v_fvarId_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visitedExpr_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_260_: u8 = 0;
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visitedExpr_255_ = crate::leanh::lean_ctor_get(v_s_253_, 0);
                v_fvarSet_256_ = crate::leanh::lean_ctor_get(v_s_253_, 1);
                v_fvarIds_257_ = crate::leanh::lean_ctor_get(v_s_253_, 2);
                v_isSharedCheck_266_ = (!crate::leanh::lean_is_exclusive(v_s_253_)) as u8;
                if v_isSharedCheck_266_ == 0 {
                    v___x_259_ = v_s_253_;
                    v_isShared_260_ = v_isSharedCheck_266_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fvarIds_257_);
                    crate::leanh::lean_inc(v_fvarSet_256_);
                    crate::leanh::lean_inc(v_visitedExpr_255_);
                    crate::leanh::lean_dec(v_s_253_);
                    v___x_259_ = crate::leanh::lean_box(0);
                    v_isShared_260_ = v_isSharedCheck_266_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fvarId_254_);
                v___x_261_ = l_Lean_FVarIdSet_insert(v_fvarSet_256_, v_fvarId_254_);
                v___x_262_ = lean_array_push(v_fvarIds_257_, v_fvarId_254_);
                if v_isShared_260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_259_, 2, v___x_262_);
                    crate::leanh::lean_ctor_set(v___x_259_, 1, v___x_261_);
                    v___x_264_ = v___x_259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_265_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_265_, 0, v_visitedExpr_255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_265_, 2, v___x_262_);
                    v___x_264_ = v_reuseFailAlloc_265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(
    mut v_a_267_: *mut crate::leanh::LeanObject,
    mut v_x_268_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_269_: u8 = 0;
    let mut v_key_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_268_) == 0 {
                    v___x_269_ = 0;
                    return v___x_269_;
                } else {
                    v_key_270_ = crate::leanh::lean_ctor_get(v_x_268_, 0);
                    v_tail_271_ = crate::leanh::lean_ctor_get(v_x_268_, 2);
                    v___x_272_ = lean_expr_eqv(v_key_270_, v_a_267_);
                    if v___x_272_ == 0 {
                        v_x_268_ = v_tail_271_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_272_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(
    mut v_a_274_: *mut crate::leanh::LeanObject,
    mut v_x_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: u8 = 0;
    let mut v_r_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_274_, v_x_275_);
    crate::leanh::lean_dec(v_x_275_);
    crate::leanh::lean_dec_ref(v_a_274_);
    v_r_277_ = crate::leanh::lean_box((v_res_276_) as usize);
    return v_r_277_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_278_: *mut crate::leanh::LeanObject,
    mut v_x_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_285_: u8 = 0;
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: u64 = 0;
    let mut v___x_288_: u64 = 0;
    let mut v___x_289_: u64 = 0;
    let mut v_fold_290_: u64 = 0;
    let mut v___x_291_: u64 = 0;
    let mut v___x_292_: u64 = 0;
    let mut v___x_293_: u64 = 0;
    let mut v___x_294_: usize = 0;
    let mut v___x_295_: usize = 0;
    let mut v___x_296_: usize = 0;
    let mut v___x_297_: usize = 0;
    let mut v___x_298_: usize = 0;
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_279_) == 0 {
                    return v_x_278_;
                } else {
                    v_key_280_ = crate::leanh::lean_ctor_get(v_x_279_, 0);
                    v_value_281_ = crate::leanh::lean_ctor_get(v_x_279_, 1);
                    v_tail_282_ = crate::leanh::lean_ctor_get(v_x_279_, 2);
                    v_isSharedCheck_305_ = (!crate::leanh::lean_is_exclusive(v_x_279_)) as u8;
                    if v_isSharedCheck_305_ == 0 {
                        v___x_284_ = v_x_279_;
                        v_isShared_285_ = v_isSharedCheck_305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_282_);
                        crate::leanh::lean_inc(v_value_281_);
                        crate::leanh::lean_inc(v_key_280_);
                        crate::leanh::lean_dec(v_x_279_);
                        v___x_284_ = crate::leanh::lean_box(0);
                        v_isShared_285_ = v_isSharedCheck_305_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_286_ = lean_array_get_size(v_x_278_);
                v___x_287_ = l_Lean_Expr_hash(v_key_280_);
                v___x_288_ = 32u64;
                v___x_289_ = lean_uint64_shift_right(v___x_287_, v___x_288_);
                v_fold_290_ = lean_uint64_xor(v___x_287_, v___x_289_);
                v___x_291_ = 16u64;
                v___x_292_ = lean_uint64_shift_right(v_fold_290_, v___x_291_);
                v___x_293_ = lean_uint64_xor(v_fold_290_, v___x_292_);
                v___x_294_ = lean_uint64_to_usize(v___x_293_);
                v___x_295_ = lean_usize_of_nat(v___x_286_);
                v___x_296_ = 1usize;
                v___x_297_ = lean_usize_sub(v___x_295_, v___x_296_);
                v___x_298_ = lean_usize_land(v___x_294_, v___x_297_);
                v___x_299_ = lean_array_uget_borrowed(v_x_278_, v___x_298_);
                crate::leanh::lean_inc(v___x_299_);
                if v_isShared_285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_284_, 2, v___x_299_);
                    v___x_301_ = v___x_284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_304_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 0, v_key_280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 1, v_value_281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 2, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_302_ = lean_array_uset(v_x_278_, v___x_298_, v___x_301_);
                v_x_278_ = v___x_302_;
                v_x_279_ = v_tail_282_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(
    mut v_i_306_: *mut crate::leanh::LeanObject,
    mut v_source_307_: *mut crate::leanh::LeanObject,
    mut v_target_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: u8 = 0;
    let mut v_es_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_309_ = lean_array_get_size(v_source_307_);
                v___x_310_ = lean_nat_dec_lt(v_i_306_, v___x_309_);
                if v___x_310_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_307_);
                    crate::leanh::lean_dec(v_i_306_);
                    return v_target_308_;
                } else {
                    v_es_311_ = lean_array_fget(v_source_307_, v_i_306_);
                    v___x_312_ = crate::leanh::lean_box(0);
                    v_source_313_ = lean_array_fset(v_source_307_, v_i_306_, v___x_312_);
                    v_target_314_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_target_308_, v_es_311_);
                    v___x_315_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_316_ = lean_nat_add(v_i_306_, v___x_315_);
                    crate::leanh::lean_dec(v_i_306_);
                    v_i_306_ = v___x_316_;
                    v_source_307_ = v_source_313_;
                    v_target_308_ = v_target_314_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(
    mut v_data_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_array_get_size(v_data_318_);
    v___x_320_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_321_ = lean_nat_mul(v___x_319_, v___x_320_);
    v___x_322_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_323_ = crate::leanh::lean_box(0);
    v___x_324_ = lean_mk_array(v_nbuckets_321_, v___x_323_);
    v___x_325_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v___x_322_, v_data_318_, v___x_324_);
    return v___x_325_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(
    mut v_m_326_: *mut crate::leanh::LeanObject,
    mut v_a_327_: *mut crate::leanh::LeanObject,
    mut v_b_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u64 = 0;
    let mut v___x_333_: u64 = 0;
    let mut v___x_334_: u64 = 0;
    let mut v_fold_335_: u64 = 0;
    let mut v___x_336_: u64 = 0;
    let mut v___x_337_: u64 = 0;
    let mut v___x_338_: u64 = 0;
    let mut v___x_339_: usize = 0;
    let mut v___x_340_: usize = 0;
    let mut v___x_341_: usize = 0;
    let mut v___x_342_: usize = 0;
    let mut v___x_343_: usize = 0;
    let mut v_bkt_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_348_: u8 = 0;
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: u8 = 0;
    let mut v_val_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_366_: u8 = 0;
    let mut v_unused_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_329_ = crate::leanh::lean_ctor_get(v_m_326_, 0);
                v_buckets_330_ = crate::leanh::lean_ctor_get(v_m_326_, 1);
                v___x_331_ = lean_array_get_size(v_buckets_330_);
                v___x_332_ = l_Lean_Expr_hash(v_a_327_);
                v___x_333_ = 32u64;
                v___x_334_ = lean_uint64_shift_right(v___x_332_, v___x_333_);
                v_fold_335_ = lean_uint64_xor(v___x_332_, v___x_334_);
                v___x_336_ = 16u64;
                v___x_337_ = lean_uint64_shift_right(v_fold_335_, v___x_336_);
                v___x_338_ = lean_uint64_xor(v_fold_335_, v___x_337_);
                v___x_339_ = lean_uint64_to_usize(v___x_338_);
                v___x_340_ = lean_usize_of_nat(v___x_331_);
                v___x_341_ = 1usize;
                v___x_342_ = lean_usize_sub(v___x_340_, v___x_341_);
                v___x_343_ = lean_usize_land(v___x_339_, v___x_342_);
                v_bkt_344_ = lean_array_uget_borrowed(v_buckets_330_, v___x_343_);
                v___x_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_327_, v_bkt_344_);
                if v___x_345_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_330_);
                    crate::leanh::lean_inc(v_size_329_);
                    v_isSharedCheck_366_ = (!crate::leanh::lean_is_exclusive(v_m_326_)) as u8;
                    if v_isSharedCheck_366_ == 0 {
                        v_unused_367_ = crate::leanh::lean_ctor_get(v_m_326_, 1);
                        crate::leanh::lean_dec(v_unused_367_);
                        v_unused_368_ = crate::leanh::lean_ctor_get(v_m_326_, 0);
                        crate::leanh::lean_dec(v_unused_368_);
                        v___x_347_ = v_m_326_;
                        v_isShared_348_ = v_isSharedCheck_366_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_326_);
                        v___x_347_ = crate::leanh::lean_box(0);
                        v_isShared_348_ = v_isSharedCheck_366_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_328_);
                    crate::leanh::lean_dec_ref(v_a_327_);
                    return v_m_326_;
                }
            }
            1 => {
                v___x_349_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_350_ = lean_nat_add(v_size_329_, v___x_349_);
                crate::leanh::lean_dec(v_size_329_);
                crate::leanh::lean_inc(v_bkt_344_);
                v___x_351_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_351_, 0, v_a_327_);
                crate::leanh::lean_ctor_set(v___x_351_, 1, v_b_328_);
                crate::leanh::lean_ctor_set(v___x_351_, 2, v_bkt_344_);
                v_buckets_x27_352_ = lean_array_uset(v_buckets_330_, v___x_343_, v___x_351_);
                v___x_353_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
                v___x_355_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
                crate::leanh::lean_dec(v___x_354_);
                v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
                v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
                crate::leanh::lean_dec(v___x_356_);
                if v___x_358_ == 0 {
                    v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_buckets_x27_352_);
                    if v_isShared_348_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_347_, 1, v_val_359_);
                        crate::leanh::lean_ctor_set(v___x_347_, 0, v_size_x27_350_);
                        v___x_361_ = v___x_347_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_362_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_359_);
                        v___x_361_ = v_reuseFailAlloc_362_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_348_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_347_, 1, v_buckets_x27_352_);
                        crate::leanh::lean_ctor_set(v___x_347_, 0, v_size_x27_350_);
                        v___x_364_ = v___x_347_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_365_, 1, v_buckets_x27_352_);
                        v___x_364_ = v_reuseFailAlloc_365_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_361_;
            }
            3 => {
                return v___x_364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(
    mut v_m_369_: *mut crate::leanh::LeanObject,
    mut v_a_370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: u64 = 0;
    let mut v___x_374_: u64 = 0;
    let mut v___x_375_: u64 = 0;
    let mut v_fold_376_: u64 = 0;
    let mut v___x_377_: u64 = 0;
    let mut v___x_378_: u64 = 0;
    let mut v___x_379_: u64 = 0;
    let mut v___x_380_: usize = 0;
    let mut v___x_381_: usize = 0;
    let mut v___x_382_: usize = 0;
    let mut v___x_383_: usize = 0;
    let mut v___x_384_: usize = 0;
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    v_buckets_371_ = crate::leanh::lean_ctor_get(v_m_369_, 1);
    v___x_372_ = lean_array_get_size(v_buckets_371_);
    v___x_373_ = l_Lean_Expr_hash(v_a_370_);
    v___x_374_ = 32u64;
    v___x_375_ = lean_uint64_shift_right(v___x_373_, v___x_374_);
    v_fold_376_ = lean_uint64_xor(v___x_373_, v___x_375_);
    v___x_377_ = 16u64;
    v___x_378_ = lean_uint64_shift_right(v_fold_376_, v___x_377_);
    v___x_379_ = lean_uint64_xor(v_fold_376_, v___x_378_);
    v___x_380_ = lean_uint64_to_usize(v___x_379_);
    v___x_381_ = lean_usize_of_nat(v___x_372_);
    v___x_382_ = 1usize;
    v___x_383_ = lean_usize_sub(v___x_381_, v___x_382_);
    v___x_384_ = lean_usize_land(v___x_380_, v___x_383_);
    v___x_385_ = lean_array_uget_borrowed(v_buckets_371_, v___x_384_);
    v___x_386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_370_, v___x_385_);
    return v___x_386_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(
    mut v_m_387_: *mut crate::leanh::LeanObject,
    mut v_a_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_389_: u8 = 0;
    let mut v_r_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_389_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_387_, v_a_388_);
    crate::leanh::lean_dec_ref(v_a_388_);
    crate::leanh::lean_dec_ref(v_m_387_);
    v_r_390_ = crate::leanh::lean_box((v_res_389_) as usize);
    return v_r_390_;
}
pub unsafe fn l_Lean_CollectFVars_main(
    mut v_x_391_: *mut crate::leanh::LeanObject,
    mut v_a_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_391_) {
                11 => {
                    v_struct_399_ = crate::leanh::lean_ctor_get(v_x_391_, 2);
                    crate::leanh::lean_inc_ref(v_struct_399_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 3);
                    v___x_400_ = l_Lean_CollectFVars_visit(v_struct_399_, v_a_392_);
                    return v___x_400_;
                }
                7 => {
                    v_binderType_401_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_401_);
                    v_body_402_ = crate::leanh::lean_ctor_get(v_x_391_, 2);
                    crate::leanh::lean_inc_ref(v_body_402_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 3);
                    v_d_394_ = v_binderType_401_;
                    v_b_395_ = v_body_402_;
                    v___y_396_ = v_a_392_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_403_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_403_);
                    v_body_404_ = crate::leanh::lean_ctor_get(v_x_391_, 2);
                    crate::leanh::lean_inc_ref(v_body_404_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 3);
                    v_d_394_ = v_binderType_403_;
                    v_b_395_ = v_body_404_;
                    v___y_396_ = v_a_392_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_405_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
                    crate::leanh::lean_inc_ref(v_type_405_);
                    v_value_406_ = crate::leanh::lean_ctor_get(v_x_391_, 2);
                    crate::leanh::lean_inc_ref(v_value_406_);
                    v_body_407_ = crate::leanh::lean_ctor_get(v_x_391_, 3);
                    crate::leanh::lean_inc_ref(v_body_407_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 4);
                    v___x_408_ = l_Lean_CollectFVars_visit(v_type_405_, v_a_392_);
                    v___x_409_ = l_Lean_CollectFVars_visit(v_value_406_, v___x_408_);
                    v___x_410_ = l_Lean_CollectFVars_visit(v_body_407_, v___x_409_);
                    return v___x_410_;
                }
                5 => {
                    v_fn_411_ = crate::leanh::lean_ctor_get(v_x_391_, 0);
                    crate::leanh::lean_inc_ref(v_fn_411_);
                    v_arg_412_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
                    crate::leanh::lean_inc_ref(v_arg_412_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 2);
                    v___x_413_ = l_Lean_CollectFVars_visit(v_fn_411_, v_a_392_);
                    v___x_414_ = l_Lean_CollectFVars_visit(v_arg_412_, v___x_413_);
                    return v___x_414_;
                }
                10 => {
                    v_expr_415_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
                    crate::leanh::lean_inc_ref(v_expr_415_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 2);
                    v___x_416_ = l_Lean_CollectFVars_visit(v_expr_415_, v_a_392_);
                    return v___x_416_;
                }
                1 => {
                    v_fvarId_417_ = crate::leanh::lean_ctor_get(v_x_391_, 0);
                    crate::leanh::lean_inc(v_fvarId_417_);
                    crate::leanh::lean_dec_ref_known(v_x_391_, 1);
                    v___x_418_ = l_Lean_CollectFVars_State_add(v_a_392_, v_fvarId_417_);
                    return v___x_418_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_391_);
                    return v_a_392_;
                }
            },
            1 => {
                v___x_397_ = l_Lean_CollectFVars_visit(v_d_394_, v___y_396_);
                v___x_398_ = l_Lean_CollectFVars_visit(v_b_395_, v___x_397_);
                return v___x_398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectFVars_visit(
    mut v_e_419_: *mut crate::leanh::LeanObject,
    mut v_s_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: u8 = 0;
    let mut v_visitedExpr_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_428_: u8 = 0;
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_unused_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_421_ = l_Lean_Expr_hasFVar(v_e_419_);
                if v___x_421_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_419_);
                    return v_s_420_;
                } else {
                    v_visitedExpr_422_ = crate::leanh::lean_ctor_get(v_s_420_, 0);
                    v_fvarSet_423_ = crate::leanh::lean_ctor_get(v_s_420_, 1);
                    v_fvarIds_424_ = crate::leanh::lean_ctor_get(v_s_420_, 2);
                    v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visitedExpr_422_, v_e_419_);
                    if v___x_425_ == 0 {
                        crate::leanh::lean_inc_ref(v_fvarIds_424_);
                        crate::leanh::lean_inc(v_fvarSet_423_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_422_);
                        v_isSharedCheck_435_ = (!crate::leanh::lean_is_exclusive(v_s_420_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v_unused_436_ = crate::leanh::lean_ctor_get(v_s_420_, 2);
                            crate::leanh::lean_dec(v_unused_436_);
                            v_unused_437_ = crate::leanh::lean_ctor_get(v_s_420_, 1);
                            crate::leanh::lean_dec(v_unused_437_);
                            v_unused_438_ = crate::leanh::lean_ctor_get(v_s_420_, 0);
                            crate::leanh::lean_dec(v_unused_438_);
                            v___x_427_ = v_s_420_;
                            v_isShared_428_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_420_);
                            v___x_427_ = crate::leanh::lean_box(0);
                            v_isShared_428_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_419_);
                        return v_s_420_;
                    }
                }
            }
            1 => {
                v___x_429_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_419_);
                v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visitedExpr_422_, v_e_419_, v___x_429_);
                if v_isShared_428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_427_, 0, v___x_430_);
                    v___x_432_ = v___x_427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 1, v_fvarSet_423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 2, v_fvarIds_424_);
                    v___x_432_ = v_reuseFailAlloc_434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_433_ = l_Lean_CollectFVars_main(v_e_419_, v___x_432_);
                return v___x_433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(
    mut v_00_u03b2_439_: *mut crate::leanh::LeanObject,
    mut v_m_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_442_: u8 = 0;
    v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_440_, v_a_441_);
    return v___x_442_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(
    mut v_00_u03b2_443_: *mut crate::leanh::LeanObject,
    mut v_m_444_: *mut crate::leanh::LeanObject,
    mut v_a_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_446_: u8 = 0;
    let mut v_r_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_446_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(
            v_00_u03b2_443_,
            v_m_444_,
            v_a_445_,
        );
    crate::leanh::lean_dec_ref(v_a_445_);
    crate::leanh::lean_dec_ref(v_m_444_);
    v_r_447_ = crate::leanh::lean_box((v_res_446_) as usize);
    return v_r_447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1(
    mut v_00_u03b2_448_: *mut crate::leanh::LeanObject,
    mut v_m_449_: *mut crate::leanh::LeanObject,
    mut v_a_450_: *mut crate::leanh::LeanObject,
    mut v_b_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_449_, v_a_450_, v_b_451_);
    return v___x_452_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(
    mut v_00_u03b2_453_: *mut crate::leanh::LeanObject,
    mut v_a_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_456_: u8 = 0;
    v___x_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_a_454_, v_x_455_);
    return v___x_456_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(
    mut v_00_u03b2_457_: *mut crate::leanh::LeanObject,
    mut v_a_458_: *mut crate::leanh::LeanObject,
    mut v_x_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_460_: u8 = 0;
    let mut v_r_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_460_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(v_00_u03b2_457_, v_a_458_, v_x_459_);
    crate::leanh::lean_dec(v_x_459_);
    crate::leanh::lean_dec_ref(v_a_458_);
    v_r_461_ = crate::leanh::lean_box((v_res_460_) as usize);
    return v_r_461_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3(
    mut v_00_u03b2_462_: *mut crate::leanh::LeanObject,
    mut v_data_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_data_463_);
    return v___x_464_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4(
    mut v_00_u03b2_465_: *mut crate::leanh::LeanObject,
    mut v_i_466_: *mut crate::leanh::LeanObject,
    mut v_source_467_: *mut crate::leanh::LeanObject,
    mut v_target_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4___redArg(v_i_466_, v_source_467_, v_target_468_);
    return v___x_469_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_470_: *mut crate::leanh::LeanObject,
    mut v_x_471_: *mut crate::leanh::LeanObject,
    mut v_x_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectFVars_visit_spec__1_spec__3_spec__4_spec__5___redArg(v_x_471_, v_x_472_);
    return v___x_473_;
}
pub unsafe fn l_Lean_collectFVars(
    mut v_s_474_: *mut crate::leanh::LeanObject,
    mut v_e_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_CollectFVars_main(v_e_475_, v_s_474_);
    return v___x_476_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectFVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_LocalContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_CollectFVars_instInhabitedState_default =
        _init_l_Lean_CollectFVars_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState_default);
    l_Lean_CollectFVars_instInhabitedState = _init_l_Lean_CollectFVars_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectFVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_CollectFVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_LocalContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectFVars(builtin);
}
