// Lean compiler output
// Module: Lean.Meta.Tactic.Cleanup
// Imports: Lean.Meta.Basic Lean.Meta.CollectFVars Lean.Meta.Tactic.Util
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_mk_array, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_FVarIdSet_insert, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f,
    lean_local_ctx_erase,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_mkFreshExprMVarAt,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::CollectFVars::{
    initialize_Lean_Meta_CollectFVars, l_Lean_Expr_collectFVars,
    runtime_initialize_Lean_Meta_CollectFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::{
    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit, l_Lean_instantiateMVarsCore,
};
pub static l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 108, 101, 97, 110, 117, 112, 0],
};
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value
        ) as *mut leanh::LeanObject,
        13766534629173687669 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(
    mut v_k_2095_: *mut leanh::LeanObject,
    mut v_t_2096_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: u8 = 0;
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2096_) == 0 {
                    v_k_2097_ = leanh::lean_ctor_get(v_t_2096_, 1);
                    v_l_2098_ = leanh::lean_ctor_get(v_t_2096_, 3);
                    v_r_2099_ = leanh::lean_ctor_get(v_t_2096_, 4);
                    v___x_2100_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2095_, v_k_2097_);
                    match v___x_2100_ {
                        0 => {
                            v_t_2096_ = v_l_2098_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2102_ = 1;
                            return v___x_2102_;
                        }
                        _ => {
                            v_t_2096_ = v_r_2099_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2104_ = 0;
                    return v___x_2104_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg___boxed(
    mut v_k_2105_: *mut leanh::LeanObject,
    mut v_t_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2107_: u8 = 0;
    let mut v_r_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2107_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_2105_, v_t_2106_);
    leanh::lean_dec(v_t_2106_);
    leanh::lean_dec(v_k_2105_);
    v_r_2108_ = leanh::lean_box((v_res_2107_) as usize);
    return v_r_2108_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(
    mut v_e_2109_: *mut leanh::LeanObject,
    mut v___y_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_unused_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2112_ = l_Lean_Expr_hasMVar(v_e_2109_);
                if v___x_2112_ == 0 {
                    v___x_2113_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2113_, 0, v_e_2109_);
                    return v___x_2113_;
                } else {
                    v___x_2114_ = lean_st_ref_get(v___y_2110_);
                    v_mctx_2115_ = leanh::lean_ctor_get(v___x_2114_, 0);
                    leanh::lean_inc_ref(v_mctx_2115_);
                    leanh::lean_dec(v___x_2114_);
                    v___x_2116_ = l_Lean_instantiateMVarsCore(v_mctx_2115_, v_e_2109_);
                    v_fst_2117_ = leanh::lean_ctor_get(v___x_2116_, 0);
                    leanh::lean_inc(v_fst_2117_);
                    v_snd_2118_ = leanh::lean_ctor_get(v___x_2116_, 1);
                    leanh::lean_inc(v_snd_2118_);
                    leanh::lean_dec_ref(v___x_2116_);
                    v___x_2119_ = lean_st_ref_take(v___y_2110_);
                    v_cache_2120_ = leanh::lean_ctor_get(v___x_2119_, 1);
                    v_zetaDeltaFVarIds_2121_ = leanh::lean_ctor_get(v___x_2119_, 2);
                    v_postponed_2122_ = leanh::lean_ctor_get(v___x_2119_, 3);
                    v_diag_2123_ = leanh::lean_ctor_get(v___x_2119_, 4);
                    v_isSharedCheck_2132_ = (!leanh::lean_is_exclusive(v___x_2119_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v_unused_2133_ = leanh::lean_ctor_get(v___x_2119_, 0);
                        leanh::lean_dec(v_unused_2133_);
                        v___x_2125_ = v___x_2119_;
                        v_isShared_2126_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2123_);
                        leanh::lean_inc(v_postponed_2122_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2121_);
                        leanh::lean_inc(v_cache_2120_);
                        leanh::lean_dec(v___x_2119_);
                        v___x_2125_ = leanh::lean_box(0);
                        v_isShared_2126_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2126_ == 0 {
                    leanh::lean_ctor_set(v___x_2125_, 0, v_snd_2118_);
                    v___x_2128_ = v___x_2125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_snd_2118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_cache_2120_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2131_,
                        2,
                        v_zetaDeltaFVarIds_2121_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_postponed_2122_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 4, v_diag_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2129_ = lean_st_ref_set(v___y_2110_, v___x_2128_);
                v___x_2130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2130_, 0, v_fst_2117_);
                return v___x_2130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg___boxed(
    mut v_e_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_2134_, v___y_2135_);
    leanh::lean_dec(v___y_2135_);
    return v_res_2137_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = leanh::lean_box(0);
    v___x_2141_ = leanh::lean_unsigned_to_nat(16);
    v___x_2142_ = lean_mk_array(v___x_2141_, v___x_2140_);
    return v___x_2142_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once), _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0);
    v___x_2144_ = leanh::lean_unsigned_to_nat(0);
    v___x_2145_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2145_, 0, v___x_2144_);
    leanh::lean_ctor_set(v___x_2145_, 1, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ =
        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2;
    v___x_2147_ = leanh::lean_box(1);
    v___x_2148_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
    v___x_2149_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2149_, 0, v___x_2148_);
    leanh::lean_ctor_set(v___x_2149_, 1, v___x_2147_);
    leanh::lean_ctor_set(v___x_2149_, 2, v___x_2146_);
    return v___x_2149_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(
    mut v_fvarId_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
    mut v_a_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_unused_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ = lean_st_ref_get(v_a_2151_);
                v_snd_2158_ = leanh::lean_ctor_get(v___x_2157_, 1);
                leanh::lean_inc(v_snd_2158_);
                leanh::lean_dec(v___x_2157_);
                v___x_2159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_fvarId_2150_, v_snd_2158_);
                leanh::lean_dec(v_snd_2158_);
                if v___x_2159_ == 0 {
                    v___x_2160_ = lean_st_ref_take(v_a_2151_);
                    v_snd_2161_ = leanh::lean_ctor_get(v___x_2160_, 1);
                    v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v___x_2160_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v_unused_2174_ = leanh::lean_ctor_get(v___x_2160_, 0);
                        leanh::lean_dec(v_unused_2174_);
                        v___x_2163_ = v___x_2160_;
                        v_isShared_2164_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2161_);
                        leanh::lean_dec(v___x_2160_);
                        v___x_2163_ = leanh::lean_box(0);
                        v_isShared_2164_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fvarId_2150_);
                    v___x_2175_ = leanh::lean_box(0);
                    v___x_2176_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
                    return v___x_2176_;
                }
            }
            1 => {
                v___x_2165_ = 1;
                leanh::lean_inc(v_fvarId_2150_);
                v___x_2166_ = l_Lean_FVarIdSet_insert(v_snd_2161_, v_fvarId_2150_);
                v___x_2167_ = leanh::lean_box((v___x_2165_) as usize);
                if v_isShared_2164_ == 0 {
                    leanh::lean_ctor_set(v___x_2163_, 1, v___x_2166_);
                    leanh::lean_ctor_set(v___x_2163_, 0, v___x_2167_);
                    v___x_2169_ = v___x_2163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2166_);
                    v___x_2169_ = v_reuseFailAlloc_2172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2170_ = lean_st_ref_set(v_a_2151_, v___x_2169_);
                v___x_2171_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(
                    v_fvarId_2150_,
                    v_a_2151_,
                    v_a_2152_,
                    v_a_2153_,
                    v_a_2154_,
                    v_a_2155_,
                );
                return v___x_2171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(
    mut v_init_2177_: *mut leanh::LeanObject,
    mut v_x_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2178_) == 0 {
                    v_k_2185_ = leanh::lean_ctor_get(v_x_2178_, 1);
                    leanh::lean_inc(v_k_2185_);
                    v_l_2186_ = leanh::lean_ctor_get(v_x_2178_, 3);
                    leanh::lean_inc(v_l_2186_);
                    v_r_2187_ = leanh::lean_ctor_get(v_x_2178_, 4);
                    leanh::lean_inc(v_r_2187_);
                    leanh::lean_dec_ref_known(v_x_2178_, 5);
                    v___x_2188_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_2177_, v_l_2186_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                    if leanh::lean_obj_tag(v___x_2188_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2188_, 1);
                        v___x_2189_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_2185_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                        if leanh::lean_obj_tag(v___x_2189_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2189_, 1);
                            v___x_2190_ = leanh::lean_box(0);
                            v_init_2177_ = v___x_2190_;
                            v_x_2178_ = v_r_2187_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_2187_);
                            v_a_2192_ = leanh::lean_ctor_get(v___x_2189_, 0);
                            v_isSharedCheck_2199_ =
                                (!leanh::lean_is_exclusive(v___x_2189_)) as u8;
                            if v_isSharedCheck_2199_ == 0 {
                                v___x_2194_ = v___x_2189_;
                                v_isShared_2195_ = v_isSharedCheck_2199_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2192_);
                                leanh::lean_dec(v___x_2189_);
                                v___x_2194_ = leanh::lean_box(0);
                                v_isShared_2195_ = v_isSharedCheck_2199_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_r_2187_);
                        leanh::lean_dec(v_k_2185_);
                        return v___x_2188_;
                    }
                } else {
                    v___x_2200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2200_, 0, v_init_2177_);
                    v___x_2201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2201_, 0, v___x_2200_);
                    return v___x_2201_;
                }
            }
            1 => {
                if v_isShared_2195_ == 0 {
                    v___x_2197_ = v___x_2194_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(
    mut v_e_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
    mut v_a_2204_: *mut leanh::LeanObject,
    mut v_a_2205_: *mut leanh::LeanObject,
    mut v_a_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_unused_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_a_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2209_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_2202_, v_a_2205_);
                if leanh::lean_obj_tag(v___x_2209_) == 0 {
                    v_a_2210_ = leanh::lean_ctor_get(v___x_2209_, 0);
                    leanh::lean_inc(v_a_2210_);
                    leanh::lean_dec_ref_known(v___x_2209_, 1);
                    v___x_2211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once), _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3);
                    v___x_2212_ = lean_st_mk_ref(v___x_2211_);
                    v___x_2213_ = l_Lean_Expr_collectFVars(
                        v_a_2210_,
                        v___x_2212_,
                        v_a_2204_,
                        v_a_2205_,
                        v_a_2206_,
                        v_a_2207_,
                    );
                    if leanh::lean_obj_tag(v___x_2213_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2213_, 1);
                        v___x_2214_ = lean_st_ref_get(v___x_2212_);
                        leanh::lean_dec(v___x_2212_);
                        v_fvarSet_2215_ = leanh::lean_ctor_get(v___x_2214_, 1);
                        leanh::lean_inc(v_fvarSet_2215_);
                        leanh::lean_dec(v___x_2214_);
                        v___x_2216_ = leanh::lean_box(0);
                        v___x_2217_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v___x_2216_, v_fvarSet_2215_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
                        if leanh::lean_obj_tag(v___x_2217_) == 0 {
                            v_isSharedCheck_2224_ =
                                (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                            if v_isSharedCheck_2224_ == 0 {
                                v_unused_2225_ = leanh::lean_ctor_get(v___x_2217_, 0);
                                leanh::lean_dec(v_unused_2225_);
                                v___x_2219_ = v___x_2217_;
                                v_isShared_2220_ = v_isSharedCheck_2224_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2217_);
                                v___x_2219_ = leanh::lean_box(0);
                                v_isShared_2220_ = v_isSharedCheck_2224_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2226_ = leanh::lean_ctor_get(v___x_2217_, 0);
                            v_isSharedCheck_2233_ =
                                (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                            if v_isSharedCheck_2233_ == 0 {
                                v___x_2228_ = v___x_2217_;
                                v_isShared_2229_ = v_isSharedCheck_2233_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2226_);
                                leanh::lean_dec(v___x_2217_);
                                v___x_2228_ = leanh::lean_box(0);
                                v_isShared_2229_ = v_isSharedCheck_2233_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2212_);
                        return v___x_2213_;
                    }
                } else {
                    v_a_2234_ = leanh::lean_ctor_get(v___x_2209_, 0);
                    v_isSharedCheck_2241_ = (!leanh::lean_is_exclusive(v___x_2209_)) as u8;
                    if v_isSharedCheck_2241_ == 0 {
                        v___x_2236_ = v___x_2209_;
                        v_isShared_2237_ = v_isSharedCheck_2241_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2234_);
                        leanh::lean_dec(v___x_2209_);
                        v___x_2236_ = leanh::lean_box(0);
                        v_isShared_2237_ = v_isSharedCheck_2241_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2220_ == 0 {
                    leanh::lean_ctor_set(v___x_2219_, 0, v___x_2216_);
                    v___x_2222_ = v___x_2219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2216_);
                    v___x_2222_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2222_;
            }
            3 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2231_;
            }
            5 => {
                if v_isShared_2237_ == 0 {
                    v___x_2239_ = v___x_2236_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(
    mut v_fvarId_2242_: *mut leanh::LeanObject,
    mut v_a_2243_: *mut leanh::LeanObject,
    mut v_a_2244_: *mut leanh::LeanObject,
    mut v_a_2245_: *mut leanh::LeanObject,
    mut v_a_2246_: *mut leanh::LeanObject,
    mut v_a_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2256_: u8 = 0;
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_unused_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ =
                    l_Lean_FVarId_getDecl___redArg(v_fvarId_2242_, v_a_2244_, v_a_2246_, v_a_2247_);
                if leanh::lean_obj_tag(v___x_2249_) == 0 {
                    v_a_2250_ = leanh::lean_ctor_get(v___x_2249_, 0);
                    leanh::lean_inc(v_a_2250_);
                    leanh::lean_dec_ref_known(v___x_2249_, 1);
                    v___x_2251_ = l_Lean_LocalDecl_type(v_a_2250_);
                    v___x_2252_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(
                            v___x_2251_,
                            v_a_2243_,
                            v_a_2244_,
                            v_a_2245_,
                            v_a_2246_,
                            v_a_2247_,
                        );
                    if leanh::lean_obj_tag(v___x_2252_) == 0 {
                        v_isSharedCheck_2264_ =
                            (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2264_ == 0 {
                            v_unused_2265_ = leanh::lean_ctor_get(v___x_2252_, 0);
                            leanh::lean_dec(v_unused_2265_);
                            v___x_2254_ = v___x_2252_;
                            v_isShared_2255_ = v_isSharedCheck_2264_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2252_);
                            v___x_2254_ = leanh::lean_box(0);
                            v_isShared_2255_ = v_isSharedCheck_2264_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2250_);
                        return v___x_2252_;
                    }
                } else {
                    v_a_2266_ = leanh::lean_ctor_get(v___x_2249_, 0);
                    v_isSharedCheck_2273_ = (!leanh::lean_is_exclusive(v___x_2249_)) as u8;
                    if v_isSharedCheck_2273_ == 0 {
                        v___x_2268_ = v___x_2249_;
                        v_isShared_2269_ = v_isSharedCheck_2273_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2266_);
                        leanh::lean_dec(v___x_2249_);
                        v___x_2268_ = leanh::lean_box(0);
                        v_isShared_2269_ = v_isSharedCheck_2273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2256_ = 0;
                v___x_2257_ = l_Lean_LocalDecl_value_x3f(v_a_2250_, v___x_2256_);
                leanh::lean_dec(v_a_2250_);
                if leanh::lean_obj_tag(v___x_2257_) == 1 {
                    leanh::lean_del_object(v___x_2254_);
                    v_val_2258_ = leanh::lean_ctor_get(v___x_2257_, 0);
                    leanh::lean_inc(v_val_2258_);
                    leanh::lean_dec_ref_known(v___x_2257_, 1);
                    v___x_2259_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(
                            v_val_2258_,
                            v_a_2243_,
                            v_a_2244_,
                            v_a_2245_,
                            v_a_2246_,
                            v_a_2247_,
                        );
                    return v___x_2259_;
                } else {
                    leanh::lean_dec(v___x_2257_);
                    v___x_2260_ = leanh::lean_box(0);
                    if v_isShared_2255_ == 0 {
                        leanh::lean_ctor_set(v___x_2254_, 0, v___x_2260_);
                        v___x_2262_ = v___x_2254_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
                        v___x_2262_ = v_reuseFailAlloc_2263_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2262_;
            }
            3 => {
                if v_isShared_2269_ == 0 {
                    v___x_2271_ = v___x_2268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
                    v___x_2271_ = v_reuseFailAlloc_2272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(
    mut v_fvarId_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
    mut v_a_2277_: *mut leanh::LeanObject,
    mut v_a_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2281_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(
        v_fvarId_2274_,
        v_a_2275_,
        v_a_2276_,
        v_a_2277_,
        v_a_2278_,
        v_a_2279_,
    );
    leanh::lean_dec(v_a_2279_);
    leanh::lean_dec_ref(v_a_2278_);
    leanh::lean_dec(v_a_2277_);
    leanh::lean_dec_ref(v_a_2276_);
    leanh::lean_dec(v_a_2275_);
    return v_res_2281_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(
    mut v_init_2282_: *mut leanh::LeanObject,
    mut v_x_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_2282_, v_x_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
    leanh::lean_dec(v___y_2288_);
    leanh::lean_dec_ref(v___y_2287_);
    leanh::lean_dec(v___y_2286_);
    leanh::lean_dec_ref(v___y_2285_);
    leanh::lean_dec(v___y_2284_);
    return v_res_2290_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(
    mut v_fvarId_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_a_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
    mut v_a_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(
        v_fvarId_2291_,
        v_a_2292_,
        v_a_2293_,
        v_a_2294_,
        v_a_2295_,
        v_a_2296_,
    );
    leanh::lean_dec(v_a_2296_);
    leanh::lean_dec_ref(v_a_2295_);
    leanh::lean_dec(v_a_2294_);
    leanh::lean_dec_ref(v_a_2293_);
    leanh::lean_dec(v_a_2292_);
    return v_res_2298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(
    mut v_e_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
    mut v_a_2301_: *mut leanh::LeanObject,
    mut v_a_2302_: *mut leanh::LeanObject,
    mut v_a_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
    mut v_a_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2306_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(
        v_e_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_,
    );
    leanh::lean_dec(v_a_2304_);
    leanh::lean_dec_ref(v_a_2303_);
    leanh::lean_dec(v_a_2302_);
    leanh::lean_dec_ref(v_a_2301_);
    leanh::lean_dec(v_a_2300_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(
    mut v_e_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_2307_, v___y_2310_);
    return v___x_2314_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(
    mut v_e_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
    leanh::lean_dec(v___y_2320_);
    leanh::lean_dec_ref(v___y_2319_);
    leanh::lean_dec(v___y_2318_);
    leanh::lean_dec_ref(v___y_2317_);
    leanh::lean_dec(v___y_2316_);
    return v_res_2322_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(
    mut v_00_u03b2_2323_: *mut leanh::LeanObject,
    mut v_k_2324_: *mut leanh::LeanObject,
    mut v_t_2325_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2326_: u8 = 0;
    v___x_2326_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_2324_, v_t_2325_);
    return v___x_2326_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(
    mut v_00_u03b2_2327_: *mut leanh::LeanObject,
    mut v_k_2328_: *mut leanh::LeanObject,
    mut v_t_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: u8 = 0;
    let mut v_r_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(v_00_u03b2_2327_, v_k_2328_, v_t_2329_);
    leanh::lean_dec(v_t_2329_);
    leanh::lean_dec(v_k_2328_);
    v_r_2331_ = leanh::lean_box((v_res_2330_) as usize);
    return v_r_2331_;
}
pub unsafe fn l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(
    mut v_e_2332_: *mut leanh::LeanObject,
    mut v_pf_2333_: *mut leanh::LeanObject,
    mut v_pm_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2339_: u8 = 0;
    let mut v_mctx_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut v_unused_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v_mctx_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2337_ = lean_st_ref_get(v___y_2335_);
                v_mctx_2363_ = leanh::lean_ctor_get(v___x_2337_, 0);
                leanh::lean_inc_ref_n(v_mctx_2363_, 2);
                leanh::lean_dec(v___x_2337_);
                v___x_2364_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
                v___x_2365_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2365_, 0, v___x_2364_);
                leanh::lean_ctor_set(v___x_2365_, 1, v_mctx_2363_);
                v___x_2366_ = l_Lean_Expr_hasFVar(v_e_2332_);
                if v___x_2366_ == 0 {
                    v___x_2367_ = l_Lean_Expr_hasMVar(v_e_2332_);
                    if v___x_2367_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2365_, 2);
                        leanh::lean_dec_ref(v_pm_2334_);
                        leanh::lean_dec_ref(v_pf_2333_);
                        leanh::lean_dec_ref(v_e_2332_);
                        v_fst_2339_ = v___x_2367_;
                        v_mctx_2340_ = v_mctx_2363_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_mctx_2363_);
                        v___x_2368_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v_pf_2333_,
                            v_pm_2334_,
                            v_e_2332_,
                            v___x_2365_,
                        );
                        v___y_2358_ = v___x_2368_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_2363_);
                    v___x_2369_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v_pf_2333_,
                        v_pm_2334_,
                        v_e_2332_,
                        v___x_2365_,
                    );
                    v___y_2358_ = v___x_2369_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2341_ = lean_st_ref_take(v___y_2335_);
                v_cache_2342_ = leanh::lean_ctor_get(v___x_2341_, 1);
                v_zetaDeltaFVarIds_2343_ = leanh::lean_ctor_get(v___x_2341_, 2);
                v_postponed_2344_ = leanh::lean_ctor_get(v___x_2341_, 3);
                v_diag_2345_ = leanh::lean_ctor_get(v___x_2341_, 4);
                v_isSharedCheck_2355_ = (!leanh::lean_is_exclusive(v___x_2341_)) as u8;
                if v_isSharedCheck_2355_ == 0 {
                    v_unused_2356_ = leanh::lean_ctor_get(v___x_2341_, 0);
                    leanh::lean_dec(v_unused_2356_);
                    v___x_2347_ = v___x_2341_;
                    v_isShared_2348_ = v_isSharedCheck_2355_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2345_);
                    leanh::lean_inc(v_postponed_2344_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2343_);
                    leanh::lean_inc(v_cache_2342_);
                    leanh::lean_dec(v___x_2341_);
                    v___x_2347_ = leanh::lean_box(0);
                    v_isShared_2348_ = v_isSharedCheck_2355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2348_ == 0 {
                    leanh::lean_ctor_set(v___x_2347_, 0, v_mctx_2340_);
                    v___x_2350_ = v___x_2347_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2354_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_mctx_2340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_cache_2342_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2354_,
                        2,
                        v_zetaDeltaFVarIds_2343_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_postponed_2344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 4, v_diag_2345_);
                    v___x_2350_ = v_reuseFailAlloc_2354_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2351_ = lean_st_ref_set(v___y_2335_, v___x_2350_);
                v___x_2352_ = leanh::lean_box((v_fst_2339_) as usize);
                v___x_2353_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
                return v___x_2353_;
            }
            4 => {
                v_snd_2359_ = leanh::lean_ctor_get(v___y_2358_, 1);
                leanh::lean_inc(v_snd_2359_);
                v_fst_2360_ = leanh::lean_ctor_get(v___y_2358_, 0);
                leanh::lean_inc(v_fst_2360_);
                leanh::lean_dec_ref(v___y_2358_);
                v_mctx_2361_ = leanh::lean_ctor_get(v_snd_2359_, 1);
                leanh::lean_inc_ref(v_mctx_2361_);
                leanh::lean_dec(v_snd_2359_);
                v___x_2362_ = (leanh::lean_unbox(v_fst_2360_) as u8);
                leanh::lean_dec(v_fst_2360_);
                v_fst_2339_ = v___x_2362_;
                v_mctx_2340_ = v_mctx_2361_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(
    mut v_e_2370_: *mut leanh::LeanObject,
    mut v_pf_2371_: *mut leanh::LeanObject,
    mut v_pm_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_2370_, v_pf_2371_, v_pm_2372_, v___y_2373_);
    leanh::lean_dec(v___y_2373_);
    return v_res_2375_;
}
pub unsafe fn l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(
    mut v_e_2376_: *mut leanh::LeanObject,
    mut v_pf_2377_: *mut leanh::LeanObject,
    mut v_pm_2378_: *mut leanh::LeanObject,
    mut v___y_2379_: *mut leanh::LeanObject,
    mut v___y_2380_: *mut leanh::LeanObject,
    mut v___y_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: *mut leanh::LeanObject,
    mut v___y_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_2376_, v_pf_2377_, v_pm_2378_, v___y_2381_);
    return v___x_2385_;
}
pub unsafe fn l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(
    mut v_e_2386_: *mut leanh::LeanObject,
    mut v_pf_2387_: *mut leanh::LeanObject,
    mut v_pm_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_2386_, v_pf_2387_, v_pm_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    leanh::lean_dec(v___y_2393_);
    leanh::lean_dec_ref(v___y_2392_);
    leanh::lean_dec(v___y_2391_);
    leanh::lean_dec_ref(v___y_2390_);
    leanh::lean_dec(v___y_2389_);
    return v_res_2395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(
    mut v_snd_2396_: *mut leanh::LeanObject,
    mut v___y_2397_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2398_: u8 = 0;
    v___x_2398_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___y_2397_, v_snd_2396_);
    return v___x_2398_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(
    mut v_snd_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2401_: u8 = 0;
    let mut v_r_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_2399_, v___y_2400_);
    leanh::lean_dec(v___y_2400_);
    leanh::lean_dec(v_snd_2399_);
    v_r_2402_ = leanh::lean_box((v_res_2401_) as usize);
    return v_r_2402_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(
    mut v___x_2403_: u8,
    mut v_x_2404_: *mut leanh::LeanObject,
) -> u8 {
    return v___x_2403_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed(
    mut v___x_2405_: *mut leanh::LeanObject,
    mut v_x_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9700__boxed_2407_: u8 = 0;
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9700__boxed_2407_ = (leanh::lean_unbox(v___x_2405_) as u8);
    v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(v___x_9700__boxed_2407_, v_x_2406_);
    leanh::lean_dec(v_x_2406_);
    v_r_2409_ = leanh::lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(
    mut v_as_2410_: *mut leanh::LeanObject,
    mut v_sz_2411_: usize,
    mut v_i_2412_: usize,
    mut v_b_2413_: *mut leanh::LeanObject,
    mut v___y_2414_: *mut leanh::LeanObject,
    mut v___y_2415_: *mut leanh::LeanObject,
    mut v___y_2416_: *mut leanh::LeanObject,
    mut v___y_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2425_: u8 = 0;
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: usize = 0;
    let mut v_reuseFailAlloc_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v_a_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v___x_2476_: u8 = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: u8 = 0;
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_a_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2492_: u8 = 0;
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_a_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v_unused_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2420_ = lean_usize_dec_lt(v_i_2412_, v_sz_2411_);
                if v___x_2420_ == 0 {
                    v___x_2421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2421_, 0, v_b_2413_);
                    return v___x_2421_;
                } else {
                    v_snd_2422_ = leanh::lean_ctor_get(v_b_2413_, 1);
                    v_isSharedCheck_2505_ = (!leanh::lean_is_exclusive(v_b_2413_)) as u8;
                    if v_isSharedCheck_2505_ == 0 {
                        v_unused_2506_ = leanh::lean_ctor_get(v_b_2413_, 0);
                        leanh::lean_dec(v_unused_2506_);
                        v___x_2424_ = v_b_2413_;
                        v_isShared_2425_ = v_isSharedCheck_2505_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2422_);
                        leanh::lean_dec(v_b_2413_);
                        v___x_2424_ = leanh::lean_box(0);
                        v_isShared_2425_ = v_isSharedCheck_2505_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2426_ = leanh::lean_box(0);
                v_a_2435_ = lean_array_uget_borrowed(v_as_2410_, v_i_2412_);
                if leanh::lean_obj_tag(v_a_2435_) == 0 {
                    v_a_2428_ = v_snd_2422_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2422_);
                    v_val_2436_ = leanh::lean_ctor_get(v_a_2435_, 0);
                    v___x_2437_ = lean_st_ref_get(v___y_2414_);
                    v_snd_2438_ = leanh::lean_ctor_get(v___x_2437_, 1);
                    leanh::lean_inc(v_snd_2438_);
                    leanh::lean_dec(v___x_2437_);
                    v___x_2439_ = leanh::lean_box(0);
                    v___x_2440_ = l_Lean_LocalDecl_fvarId(v_val_2436_);
                    v___x_2441_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_2440_, v_snd_2438_);
                    if v___x_2441_ == 0 {
                        v___x_2442_ = l_Lean_LocalDecl_type(v_val_2436_);
                        leanh::lean_inc_ref(v___x_2442_);
                        v___x_2443_ = l_Lean_Meta_isProp(
                            v___x_2442_,
                            v___y_2415_,
                            v___y_2416_,
                            v___y_2417_,
                            v___y_2418_,
                        );
                        if leanh::lean_obj_tag(v___x_2443_) == 0 {
                            v_a_2444_ = leanh::lean_ctor_get(v___x_2443_, 0);
                            leanh::lean_inc(v_a_2444_);
                            leanh::lean_dec_ref_known(v___x_2443_, 1);
                            v___f_2445_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2445_, 0, v_snd_2438_);
                            v___x_2446_ = leanh::lean_box((v___x_2441_) as usize);
                            v___f_2447_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2447_, 0, v___x_2446_);
                            v___x_2476_ = (leanh::lean_unbox(v_a_2444_) as u8);
                            leanh::lean_dec(v_a_2444_);
                            if v___x_2476_ == 0 {
                                leanh::lean_dec_ref(v___x_2442_);
                                v___y_2449_ = v___y_2414_;
                                v___y_2450_ = v___y_2415_;
                                v___y_2451_ = v___y_2416_;
                                v___y_2452_ = v___y_2417_;
                                v___y_2453_ = v___y_2418_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v___f_2447_);
                                leanh::lean_inc_ref(v___f_2445_);
                                v___x_2477_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_2442_, v___f_2445_, v___f_2447_, v___y_2416_);
                                if leanh::lean_obj_tag(v___x_2477_) == 0 {
                                    v_a_2478_ = leanh::lean_ctor_get(v___x_2477_, 0);
                                    leanh::lean_inc(v_a_2478_);
                                    leanh::lean_dec_ref_known(v___x_2477_, 1);
                                    v___x_2479_ = (leanh::lean_unbox(v_a_2478_) as u8);
                                    leanh::lean_dec(v_a_2478_);
                                    if v___x_2479_ == 0 {
                                        v___y_2449_ = v___y_2414_;
                                        v___y_2450_ = v___y_2415_;
                                        v___y_2451_ = v___y_2416_;
                                        v___y_2452_ = v___y_2417_;
                                        v___y_2453_ = v___y_2418_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___x_2440_);
                                        v___x_2480_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2440_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
                                        if leanh::lean_obj_tag(v___x_2480_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2480_, 1);
                                            v___y_2449_ = v___y_2414_;
                                            v___y_2450_ = v___y_2415_;
                                            v___y_2451_ = v___y_2416_;
                                            v___y_2452_ = v___y_2417_;
                                            v___y_2453_ = v___y_2418_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v___f_2447_);
                                            leanh::lean_dec_ref(v___f_2445_);
                                            leanh::lean_dec(v___x_2440_);
                                            leanh::lean_del_object(v___x_2424_);
                                            v_a_2481_ = leanh::lean_ctor_get(v___x_2480_, 0);
                                            v_isSharedCheck_2488_ =
                                                (!leanh::lean_is_exclusive(v___x_2480_))
                                                    as u8;
                                            if v_isSharedCheck_2488_ == 0 {
                                                v___x_2483_ = v___x_2480_;
                                                v_isShared_2484_ = v_isSharedCheck_2488_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2481_);
                                                leanh::lean_dec(v___x_2480_);
                                                v___x_2483_ = leanh::lean_box(0);
                                                v_isShared_2484_ = v_isSharedCheck_2488_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___f_2447_);
                                    leanh::lean_dec_ref(v___f_2445_);
                                    leanh::lean_dec(v___x_2440_);
                                    leanh::lean_del_object(v___x_2424_);
                                    v_a_2489_ = leanh::lean_ctor_get(v___x_2477_, 0);
                                    v_isSharedCheck_2496_ =
                                        (!leanh::lean_is_exclusive(v___x_2477_)) as u8;
                                    if v_isSharedCheck_2496_ == 0 {
                                        v___x_2491_ = v___x_2477_;
                                        v_isShared_2492_ = v_isSharedCheck_2496_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2489_);
                                        leanh::lean_dec(v___x_2477_);
                                        v___x_2491_ = leanh::lean_box(0);
                                        v_isShared_2492_ = v_isSharedCheck_2496_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2442_);
                            leanh::lean_dec(v___x_2440_);
                            leanh::lean_dec(v_snd_2438_);
                            leanh::lean_del_object(v___x_2424_);
                            v_a_2497_ = leanh::lean_ctor_get(v___x_2443_, 0);
                            v_isSharedCheck_2504_ =
                                (!leanh::lean_is_exclusive(v___x_2443_)) as u8;
                            if v_isSharedCheck_2504_ == 0 {
                                v___x_2499_ = v___x_2443_;
                                v_isShared_2500_ = v_isSharedCheck_2504_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2497_);
                                leanh::lean_dec(v___x_2443_);
                                v___x_2499_ = leanh::lean_box(0);
                                v_isShared_2500_ = v_isSharedCheck_2504_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2440_);
                        leanh::lean_dec(v_snd_2438_);
                        v_a_2428_ = v___x_2439_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2425_ == 0 {
                    leanh::lean_ctor_set(v___x_2424_, 1, v_a_2428_);
                    leanh::lean_ctor_set(v___x_2424_, 0, v___x_2426_);
                    v___x_2430_ = v___x_2424_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_a_2428_);
                    v___x_2430_ = v_reuseFailAlloc_2434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2431_ = 1usize;
                v___x_2432_ = lean_usize_add(v_i_2412_, v___x_2431_);
                v_i_2412_ = v___x_2432_;
                v_b_2413_ = v___x_2430_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2454_ = l_Lean_LocalDecl_value_x3f(v_val_2436_, v___x_2441_);
                if leanh::lean_obj_tag(v___x_2454_) == 1 {
                    v_val_2455_ = leanh::lean_ctor_get(v___x_2454_, 0);
                    leanh::lean_inc(v_val_2455_);
                    leanh::lean_dec_ref_known(v___x_2454_, 1);
                    v___x_2456_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_2455_, v___f_2445_, v___f_2447_, v___y_2451_);
                    if leanh::lean_obj_tag(v___x_2456_) == 0 {
                        v_a_2457_ = leanh::lean_ctor_get(v___x_2456_, 0);
                        leanh::lean_inc(v_a_2457_);
                        leanh::lean_dec_ref_known(v___x_2456_, 1);
                        v___x_2458_ = (leanh::lean_unbox(v_a_2457_) as u8);
                        leanh::lean_dec(v_a_2457_);
                        if v___x_2458_ == 0 {
                            leanh::lean_dec(v___x_2440_);
                            v_a_2428_ = v___x_2439_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2459_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2440_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
                            if leanh::lean_obj_tag(v___x_2459_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2459_, 1);
                                v_a_2428_ = v___x_2439_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2424_);
                                v_a_2460_ = leanh::lean_ctor_get(v___x_2459_, 0);
                                v_isSharedCheck_2467_ =
                                    (!leanh::lean_is_exclusive(v___x_2459_)) as u8;
                                if v_isSharedCheck_2467_ == 0 {
                                    v___x_2462_ = v___x_2459_;
                                    v_isShared_2463_ = v_isSharedCheck_2467_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2460_);
                                    leanh::lean_dec(v___x_2459_);
                                    v___x_2462_ = leanh::lean_box(0);
                                    v_isShared_2463_ = v_isSharedCheck_2467_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2440_);
                        leanh::lean_del_object(v___x_2424_);
                        v_a_2468_ = leanh::lean_ctor_get(v___x_2456_, 0);
                        v_isSharedCheck_2475_ =
                            (!leanh::lean_is_exclusive(v___x_2456_)) as u8;
                        if v_isSharedCheck_2475_ == 0 {
                            v___x_2470_ = v___x_2456_;
                            v_isShared_2471_ = v_isSharedCheck_2475_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2468_);
                            leanh::lean_dec(v___x_2456_);
                            v___x_2470_ = leanh::lean_box(0);
                            v_isShared_2471_ = v_isSharedCheck_2475_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2454_);
                    leanh::lean_dec_ref(v___f_2447_);
                    leanh::lean_dec_ref(v___f_2445_);
                    leanh::lean_dec(v___x_2440_);
                    v_a_2428_ = v___x_2439_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2465_;
            }
            7 => {
                if v_isShared_2471_ == 0 {
                    v___x_2473_ = v___x_2470_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2473_;
            }
            9 => {
                if v_isShared_2484_ == 0 {
                    v___x_2486_ = v___x_2483_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
                    v___x_2486_ = v_reuseFailAlloc_2487_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2486_;
            }
            11 => {
                if v_isShared_2492_ == 0 {
                    v___x_2494_ = v___x_2491_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
                    v___x_2494_ = v_reuseFailAlloc_2495_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2494_;
            }
            13 => {
                if v_isShared_2500_ == 0 {
                    v___x_2502_ = v___x_2499_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
                    v___x_2502_ = v_reuseFailAlloc_2503_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(
    mut v_as_2507_: *mut leanh::LeanObject,
    mut v_sz_2508_: *mut leanh::LeanObject,
    mut v_i_2509_: *mut leanh::LeanObject,
    mut v_b_2510_: *mut leanh::LeanObject,
    mut v___y_2511_: *mut leanh::LeanObject,
    mut v___y_2512_: *mut leanh::LeanObject,
    mut v___y_2513_: *mut leanh::LeanObject,
    mut v___y_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2517_: usize = 0;
    let mut v_i_boxed_2518_: usize = 0;
    let mut v_res_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2517_ = leanh::lean_unbox_usize(v_sz_2508_);
    leanh::lean_dec(v_sz_2508_);
    v_i_boxed_2518_ = leanh::lean_unbox_usize(v_i_2509_);
    leanh::lean_dec(v_i_2509_);
    v_res_2519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_2507_, v_sz_boxed_2517_, v_i_boxed_2518_, v_b_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
    leanh::lean_dec(v___y_2515_);
    leanh::lean_dec_ref(v___y_2514_);
    leanh::lean_dec(v___y_2513_);
    leanh::lean_dec_ref(v___y_2512_);
    leanh::lean_dec(v___y_2511_);
    leanh::lean_dec_ref(v_as_2507_);
    return v_res_2519_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(
    mut v_as_2520_: *mut leanh::LeanObject,
    mut v_sz_2521_: usize,
    mut v_i_2522_: usize,
    mut v_b_2523_: *mut leanh::LeanObject,
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2535_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: usize = 0;
    let mut v___x_2542_: usize = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_a_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2598_: u8 = 0;
    let mut v_a_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2602_: u8 = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_a_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_unused_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2530_ = lean_usize_dec_lt(v_i_2522_, v_sz_2521_);
                if v___x_2530_ == 0 {
                    v___x_2531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2531_, 0, v_b_2523_);
                    return v___x_2531_;
                } else {
                    v_snd_2532_ = leanh::lean_ctor_get(v_b_2523_, 1);
                    v_isSharedCheck_2615_ = (!leanh::lean_is_exclusive(v_b_2523_)) as u8;
                    if v_isSharedCheck_2615_ == 0 {
                        v_unused_2616_ = leanh::lean_ctor_get(v_b_2523_, 0);
                        leanh::lean_dec(v_unused_2616_);
                        v___x_2534_ = v_b_2523_;
                        v_isShared_2535_ = v_isSharedCheck_2615_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2532_);
                        leanh::lean_dec(v_b_2523_);
                        v___x_2534_ = leanh::lean_box(0);
                        v_isShared_2535_ = v_isSharedCheck_2615_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2536_ = leanh::lean_box(0);
                v_a_2545_ = lean_array_uget_borrowed(v_as_2520_, v_i_2522_);
                if leanh::lean_obj_tag(v_a_2545_) == 0 {
                    v_a_2538_ = v_snd_2532_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2532_);
                    v_val_2546_ = leanh::lean_ctor_get(v_a_2545_, 0);
                    v___x_2547_ = lean_st_ref_get(v___y_2524_);
                    v_snd_2548_ = leanh::lean_ctor_get(v___x_2547_, 1);
                    leanh::lean_inc(v_snd_2548_);
                    leanh::lean_dec(v___x_2547_);
                    v___x_2549_ = leanh::lean_box(0);
                    v___x_2550_ = l_Lean_LocalDecl_fvarId(v_val_2546_);
                    v___x_2551_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_2550_, v_snd_2548_);
                    if v___x_2551_ == 0 {
                        v___x_2552_ = l_Lean_LocalDecl_type(v_val_2546_);
                        leanh::lean_inc_ref(v___x_2552_);
                        v___x_2553_ = l_Lean_Meta_isProp(
                            v___x_2552_,
                            v___y_2525_,
                            v___y_2526_,
                            v___y_2527_,
                            v___y_2528_,
                        );
                        if leanh::lean_obj_tag(v___x_2553_) == 0 {
                            v_a_2554_ = leanh::lean_ctor_get(v___x_2553_, 0);
                            leanh::lean_inc(v_a_2554_);
                            leanh::lean_dec_ref_known(v___x_2553_, 1);
                            v___f_2555_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2555_, 0, v_snd_2548_);
                            v___x_2556_ = leanh::lean_box((v___x_2551_) as usize);
                            v___f_2557_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2557_, 0, v___x_2556_);
                            v___x_2586_ = (leanh::lean_unbox(v_a_2554_) as u8);
                            leanh::lean_dec(v_a_2554_);
                            if v___x_2586_ == 0 {
                                leanh::lean_dec_ref(v___x_2552_);
                                v___y_2559_ = v___y_2524_;
                                v___y_2560_ = v___y_2525_;
                                v___y_2561_ = v___y_2526_;
                                v___y_2562_ = v___y_2527_;
                                v___y_2563_ = v___y_2528_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v___f_2557_);
                                leanh::lean_inc_ref(v___f_2555_);
                                v___x_2587_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_2552_, v___f_2555_, v___f_2557_, v___y_2526_);
                                if leanh::lean_obj_tag(v___x_2587_) == 0 {
                                    v_a_2588_ = leanh::lean_ctor_get(v___x_2587_, 0);
                                    leanh::lean_inc(v_a_2588_);
                                    leanh::lean_dec_ref_known(v___x_2587_, 1);
                                    v___x_2589_ = (leanh::lean_unbox(v_a_2588_) as u8);
                                    leanh::lean_dec(v_a_2588_);
                                    if v___x_2589_ == 0 {
                                        v___y_2559_ = v___y_2524_;
                                        v___y_2560_ = v___y_2525_;
                                        v___y_2561_ = v___y_2526_;
                                        v___y_2562_ = v___y_2527_;
                                        v___y_2563_ = v___y_2528_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___x_2550_);
                                        v___x_2590_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2550_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
                                        if leanh::lean_obj_tag(v___x_2590_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2590_, 1);
                                            v___y_2559_ = v___y_2524_;
                                            v___y_2560_ = v___y_2525_;
                                            v___y_2561_ = v___y_2526_;
                                            v___y_2562_ = v___y_2527_;
                                            v___y_2563_ = v___y_2528_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v___f_2557_);
                                            leanh::lean_dec_ref(v___f_2555_);
                                            leanh::lean_dec(v___x_2550_);
                                            leanh::lean_del_object(v___x_2534_);
                                            v_a_2591_ = leanh::lean_ctor_get(v___x_2590_, 0);
                                            v_isSharedCheck_2598_ =
                                                (!leanh::lean_is_exclusive(v___x_2590_))
                                                    as u8;
                                            if v_isSharedCheck_2598_ == 0 {
                                                v___x_2593_ = v___x_2590_;
                                                v_isShared_2594_ = v_isSharedCheck_2598_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2591_);
                                                leanh::lean_dec(v___x_2590_);
                                                v___x_2593_ = leanh::lean_box(0);
                                                v_isShared_2594_ = v_isSharedCheck_2598_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___f_2557_);
                                    leanh::lean_dec_ref(v___f_2555_);
                                    leanh::lean_dec(v___x_2550_);
                                    leanh::lean_del_object(v___x_2534_);
                                    v_a_2599_ = leanh::lean_ctor_get(v___x_2587_, 0);
                                    v_isSharedCheck_2606_ =
                                        (!leanh::lean_is_exclusive(v___x_2587_)) as u8;
                                    if v_isSharedCheck_2606_ == 0 {
                                        v___x_2601_ = v___x_2587_;
                                        v_isShared_2602_ = v_isSharedCheck_2606_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2599_);
                                        leanh::lean_dec(v___x_2587_);
                                        v___x_2601_ = leanh::lean_box(0);
                                        v_isShared_2602_ = v_isSharedCheck_2606_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2552_);
                            leanh::lean_dec(v___x_2550_);
                            leanh::lean_dec(v_snd_2548_);
                            leanh::lean_del_object(v___x_2534_);
                            v_a_2607_ = leanh::lean_ctor_get(v___x_2553_, 0);
                            v_isSharedCheck_2614_ =
                                (!leanh::lean_is_exclusive(v___x_2553_)) as u8;
                            if v_isSharedCheck_2614_ == 0 {
                                v___x_2609_ = v___x_2553_;
                                v_isShared_2610_ = v_isSharedCheck_2614_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2607_);
                                leanh::lean_dec(v___x_2553_);
                                v___x_2609_ = leanh::lean_box(0);
                                v_isShared_2610_ = v_isSharedCheck_2614_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2550_);
                        leanh::lean_dec(v_snd_2548_);
                        v_a_2538_ = v___x_2549_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2535_ == 0 {
                    leanh::lean_ctor_set(v___x_2534_, 1, v_a_2538_);
                    leanh::lean_ctor_set(v___x_2534_, 0, v___x_2536_);
                    v___x_2540_ = v___x_2534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_a_2538_);
                    v___x_2540_ = v_reuseFailAlloc_2544_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2541_ = 1usize;
                v___x_2542_ = lean_usize_add(v_i_2522_, v___x_2541_);
                v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_2520_, v_sz_2521_, v___x_2542_, v___x_2540_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
                return v___x_2543_;
            }
            4 => {
                v___x_2564_ = l_Lean_LocalDecl_value_x3f(v_val_2546_, v___x_2551_);
                if leanh::lean_obj_tag(v___x_2564_) == 1 {
                    v_val_2565_ = leanh::lean_ctor_get(v___x_2564_, 0);
                    leanh::lean_inc(v_val_2565_);
                    leanh::lean_dec_ref_known(v___x_2564_, 1);
                    v___x_2566_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_2565_, v___f_2555_, v___f_2557_, v___y_2561_);
                    if leanh::lean_obj_tag(v___x_2566_) == 0 {
                        v_a_2567_ = leanh::lean_ctor_get(v___x_2566_, 0);
                        leanh::lean_inc(v_a_2567_);
                        leanh::lean_dec_ref_known(v___x_2566_, 1);
                        v___x_2568_ = (leanh::lean_unbox(v_a_2567_) as u8);
                        leanh::lean_dec(v_a_2567_);
                        if v___x_2568_ == 0 {
                            leanh::lean_dec(v___x_2550_);
                            v_a_2538_ = v___x_2549_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2569_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2550_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
                            if leanh::lean_obj_tag(v___x_2569_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2569_, 1);
                                v_a_2538_ = v___x_2549_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2534_);
                                v_a_2570_ = leanh::lean_ctor_get(v___x_2569_, 0);
                                v_isSharedCheck_2577_ =
                                    (!leanh::lean_is_exclusive(v___x_2569_)) as u8;
                                if v_isSharedCheck_2577_ == 0 {
                                    v___x_2572_ = v___x_2569_;
                                    v_isShared_2573_ = v_isSharedCheck_2577_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2570_);
                                    leanh::lean_dec(v___x_2569_);
                                    v___x_2572_ = leanh::lean_box(0);
                                    v_isShared_2573_ = v_isSharedCheck_2577_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2550_);
                        leanh::lean_del_object(v___x_2534_);
                        v_a_2578_ = leanh::lean_ctor_get(v___x_2566_, 0);
                        v_isSharedCheck_2585_ =
                            (!leanh::lean_is_exclusive(v___x_2566_)) as u8;
                        if v_isSharedCheck_2585_ == 0 {
                            v___x_2580_ = v___x_2566_;
                            v_isShared_2581_ = v_isSharedCheck_2585_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2578_);
                            leanh::lean_dec(v___x_2566_);
                            v___x_2580_ = leanh::lean_box(0);
                            v_isShared_2581_ = v_isSharedCheck_2585_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2564_);
                    leanh::lean_dec_ref(v___f_2557_);
                    leanh::lean_dec_ref(v___f_2555_);
                    leanh::lean_dec(v___x_2550_);
                    v_a_2538_ = v___x_2549_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2573_ == 0 {
                    v___x_2575_ = v___x_2572_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2576_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
                    v___x_2575_ = v_reuseFailAlloc_2576_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2575_;
            }
            7 => {
                if v_isShared_2581_ == 0 {
                    v___x_2583_ = v___x_2580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2583_;
            }
            9 => {
                if v_isShared_2594_ == 0 {
                    v___x_2596_ = v___x_2593_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
                    v___x_2596_ = v_reuseFailAlloc_2597_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2596_;
            }
            11 => {
                if v_isShared_2602_ == 0 {
                    v___x_2604_ = v___x_2601_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
                    v___x_2604_ = v_reuseFailAlloc_2605_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2604_;
            }
            13 => {
                if v_isShared_2610_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(
    mut v_as_2617_: *mut leanh::LeanObject,
    mut v_sz_2618_: *mut leanh::LeanObject,
    mut v_i_2619_: *mut leanh::LeanObject,
    mut v_b_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
    mut v___y_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2627_: usize = 0;
    let mut v_i_boxed_2628_: usize = 0;
    let mut v_res_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2627_ = leanh::lean_unbox_usize(v_sz_2618_);
    leanh::lean_dec(v_sz_2618_);
    v_i_boxed_2628_ = leanh::lean_unbox_usize(v_i_2619_);
    leanh::lean_dec(v_i_2619_);
    v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_2617_, v_sz_boxed_2627_, v_i_boxed_2628_, v_b_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
    leanh::lean_dec(v___y_2625_);
    leanh::lean_dec_ref(v___y_2624_);
    leanh::lean_dec(v___y_2623_);
    leanh::lean_dec_ref(v___y_2622_);
    leanh::lean_dec(v___y_2621_);
    leanh::lean_dec_ref(v_as_2617_);
    return v_res_2629_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(
    mut v_as_2630_: *mut leanh::LeanObject,
    mut v_sz_2631_: usize,
    mut v_i_2632_: usize,
    mut v_b_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
    mut v___y_2638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2645_: u8 = 0;
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v_reuseFailAlloc_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u8 = 0;
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v_a_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v_a_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2712_: u8 = 0;
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2716_: u8 = 0;
    let mut v_a_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_isSharedCheck_2725_: u8 = 0;
    let mut v_unused_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2640_ = lean_usize_dec_lt(v_i_2632_, v_sz_2631_);
                if v___x_2640_ == 0 {
                    v___x_2641_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2641_, 0, v_b_2633_);
                    return v___x_2641_;
                } else {
                    v_snd_2642_ = leanh::lean_ctor_get(v_b_2633_, 1);
                    v_isSharedCheck_2725_ = (!leanh::lean_is_exclusive(v_b_2633_)) as u8;
                    if v_isSharedCheck_2725_ == 0 {
                        v_unused_2726_ = leanh::lean_ctor_get(v_b_2633_, 0);
                        leanh::lean_dec(v_unused_2726_);
                        v___x_2644_ = v_b_2633_;
                        v_isShared_2645_ = v_isSharedCheck_2725_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2642_);
                        leanh::lean_dec(v_b_2633_);
                        v___x_2644_ = leanh::lean_box(0);
                        v_isShared_2645_ = v_isSharedCheck_2725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2646_ = leanh::lean_box(0);
                v_a_2655_ = lean_array_uget_borrowed(v_as_2630_, v_i_2632_);
                if leanh::lean_obj_tag(v_a_2655_) == 0 {
                    v_a_2648_ = v_snd_2642_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2642_);
                    v_val_2656_ = leanh::lean_ctor_get(v_a_2655_, 0);
                    v___x_2657_ = lean_st_ref_get(v___y_2634_);
                    v_snd_2658_ = leanh::lean_ctor_get(v___x_2657_, 1);
                    leanh::lean_inc(v_snd_2658_);
                    leanh::lean_dec(v___x_2657_);
                    v___x_2659_ = leanh::lean_box(0);
                    v___x_2660_ = l_Lean_LocalDecl_fvarId(v_val_2656_);
                    v___x_2661_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_2660_, v_snd_2658_);
                    if v___x_2661_ == 0 {
                        v___x_2662_ = l_Lean_LocalDecl_type(v_val_2656_);
                        leanh::lean_inc_ref(v___x_2662_);
                        v___x_2663_ = l_Lean_Meta_isProp(
                            v___x_2662_,
                            v___y_2635_,
                            v___y_2636_,
                            v___y_2637_,
                            v___y_2638_,
                        );
                        if leanh::lean_obj_tag(v___x_2663_) == 0 {
                            v_a_2664_ = leanh::lean_ctor_get(v___x_2663_, 0);
                            leanh::lean_inc(v_a_2664_);
                            leanh::lean_dec_ref_known(v___x_2663_, 1);
                            v___f_2665_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2665_, 0, v_snd_2658_);
                            v___x_2666_ = leanh::lean_box((v___x_2661_) as usize);
                            v___f_2667_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2667_, 0, v___x_2666_);
                            v___x_2696_ = (leanh::lean_unbox(v_a_2664_) as u8);
                            leanh::lean_dec(v_a_2664_);
                            if v___x_2696_ == 0 {
                                leanh::lean_dec_ref(v___x_2662_);
                                v___y_2669_ = v___y_2634_;
                                v___y_2670_ = v___y_2635_;
                                v___y_2671_ = v___y_2636_;
                                v___y_2672_ = v___y_2637_;
                                v___y_2673_ = v___y_2638_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v___f_2667_);
                                leanh::lean_inc_ref(v___f_2665_);
                                v___x_2697_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_2662_, v___f_2665_, v___f_2667_, v___y_2636_);
                                if leanh::lean_obj_tag(v___x_2697_) == 0 {
                                    v_a_2698_ = leanh::lean_ctor_get(v___x_2697_, 0);
                                    leanh::lean_inc(v_a_2698_);
                                    leanh::lean_dec_ref_known(v___x_2697_, 1);
                                    v___x_2699_ = (leanh::lean_unbox(v_a_2698_) as u8);
                                    leanh::lean_dec(v_a_2698_);
                                    if v___x_2699_ == 0 {
                                        v___y_2669_ = v___y_2634_;
                                        v___y_2670_ = v___y_2635_;
                                        v___y_2671_ = v___y_2636_;
                                        v___y_2672_ = v___y_2637_;
                                        v___y_2673_ = v___y_2638_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___x_2660_);
                                        v___x_2700_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2660_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                                        if leanh::lean_obj_tag(v___x_2700_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2700_, 1);
                                            v___y_2669_ = v___y_2634_;
                                            v___y_2670_ = v___y_2635_;
                                            v___y_2671_ = v___y_2636_;
                                            v___y_2672_ = v___y_2637_;
                                            v___y_2673_ = v___y_2638_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v___f_2667_);
                                            leanh::lean_dec_ref(v___f_2665_);
                                            leanh::lean_dec(v___x_2660_);
                                            leanh::lean_del_object(v___x_2644_);
                                            v_a_2701_ = leanh::lean_ctor_get(v___x_2700_, 0);
                                            v_isSharedCheck_2708_ =
                                                (!leanh::lean_is_exclusive(v___x_2700_))
                                                    as u8;
                                            if v_isSharedCheck_2708_ == 0 {
                                                v___x_2703_ = v___x_2700_;
                                                v_isShared_2704_ = v_isSharedCheck_2708_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2701_);
                                                leanh::lean_dec(v___x_2700_);
                                                v___x_2703_ = leanh::lean_box(0);
                                                v_isShared_2704_ = v_isSharedCheck_2708_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___f_2667_);
                                    leanh::lean_dec_ref(v___f_2665_);
                                    leanh::lean_dec(v___x_2660_);
                                    leanh::lean_del_object(v___x_2644_);
                                    v_a_2709_ = leanh::lean_ctor_get(v___x_2697_, 0);
                                    v_isSharedCheck_2716_ =
                                        (!leanh::lean_is_exclusive(v___x_2697_)) as u8;
                                    if v_isSharedCheck_2716_ == 0 {
                                        v___x_2711_ = v___x_2697_;
                                        v_isShared_2712_ = v_isSharedCheck_2716_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2709_);
                                        leanh::lean_dec(v___x_2697_);
                                        v___x_2711_ = leanh::lean_box(0);
                                        v_isShared_2712_ = v_isSharedCheck_2716_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2662_);
                            leanh::lean_dec(v___x_2660_);
                            leanh::lean_dec(v_snd_2658_);
                            leanh::lean_del_object(v___x_2644_);
                            v_a_2717_ = leanh::lean_ctor_get(v___x_2663_, 0);
                            v_isSharedCheck_2724_ =
                                (!leanh::lean_is_exclusive(v___x_2663_)) as u8;
                            if v_isSharedCheck_2724_ == 0 {
                                v___x_2719_ = v___x_2663_;
                                v_isShared_2720_ = v_isSharedCheck_2724_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2717_);
                                leanh::lean_dec(v___x_2663_);
                                v___x_2719_ = leanh::lean_box(0);
                                v_isShared_2720_ = v_isSharedCheck_2724_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2660_);
                        leanh::lean_dec(v_snd_2658_);
                        v_a_2648_ = v___x_2659_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2645_ == 0 {
                    leanh::lean_ctor_set(v___x_2644_, 1, v_a_2648_);
                    leanh::lean_ctor_set(v___x_2644_, 0, v___x_2646_);
                    v___x_2650_ = v___x_2644_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_a_2648_);
                    v___x_2650_ = v_reuseFailAlloc_2654_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2651_ = 1usize;
                v___x_2652_ = lean_usize_add(v_i_2632_, v___x_2651_);
                v_i_2632_ = v___x_2652_;
                v_b_2633_ = v___x_2650_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2674_ = l_Lean_LocalDecl_value_x3f(v_val_2656_, v___x_2661_);
                if leanh::lean_obj_tag(v___x_2674_) == 1 {
                    v_val_2675_ = leanh::lean_ctor_get(v___x_2674_, 0);
                    leanh::lean_inc(v_val_2675_);
                    leanh::lean_dec_ref_known(v___x_2674_, 1);
                    v___x_2676_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_2675_, v___f_2665_, v___f_2667_, v___y_2671_);
                    if leanh::lean_obj_tag(v___x_2676_) == 0 {
                        v_a_2677_ = leanh::lean_ctor_get(v___x_2676_, 0);
                        leanh::lean_inc(v_a_2677_);
                        leanh::lean_dec_ref_known(v___x_2676_, 1);
                        v___x_2678_ = (leanh::lean_unbox(v_a_2677_) as u8);
                        leanh::lean_dec(v_a_2677_);
                        if v___x_2678_ == 0 {
                            leanh::lean_dec(v___x_2660_);
                            v_a_2648_ = v___x_2659_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2679_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2660_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
                            if leanh::lean_obj_tag(v___x_2679_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2679_, 1);
                                v_a_2648_ = v___x_2659_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2644_);
                                v_a_2680_ = leanh::lean_ctor_get(v___x_2679_, 0);
                                v_isSharedCheck_2687_ =
                                    (!leanh::lean_is_exclusive(v___x_2679_)) as u8;
                                if v_isSharedCheck_2687_ == 0 {
                                    v___x_2682_ = v___x_2679_;
                                    v_isShared_2683_ = v_isSharedCheck_2687_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2680_);
                                    leanh::lean_dec(v___x_2679_);
                                    v___x_2682_ = leanh::lean_box(0);
                                    v_isShared_2683_ = v_isSharedCheck_2687_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2660_);
                        leanh::lean_del_object(v___x_2644_);
                        v_a_2688_ = leanh::lean_ctor_get(v___x_2676_, 0);
                        v_isSharedCheck_2695_ =
                            (!leanh::lean_is_exclusive(v___x_2676_)) as u8;
                        if v_isSharedCheck_2695_ == 0 {
                            v___x_2690_ = v___x_2676_;
                            v_isShared_2691_ = v_isSharedCheck_2695_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2688_);
                            leanh::lean_dec(v___x_2676_);
                            v___x_2690_ = leanh::lean_box(0);
                            v_isShared_2691_ = v_isSharedCheck_2695_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2674_);
                    leanh::lean_dec_ref(v___f_2667_);
                    leanh::lean_dec_ref(v___f_2665_);
                    leanh::lean_dec(v___x_2660_);
                    v_a_2648_ = v___x_2659_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2683_ == 0 {
                    v___x_2685_ = v___x_2682_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2686_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
                    v___x_2685_ = v_reuseFailAlloc_2686_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2685_;
            }
            7 => {
                if v_isShared_2691_ == 0 {
                    v___x_2693_ = v___x_2690_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2693_;
            }
            9 => {
                if v_isShared_2704_ == 0 {
                    v___x_2706_ = v___x_2703_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
                    v___x_2706_ = v_reuseFailAlloc_2707_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2706_;
            }
            11 => {
                if v_isShared_2712_ == 0 {
                    v___x_2714_ = v___x_2711_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2715_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
                    v___x_2714_ = v_reuseFailAlloc_2715_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2714_;
            }
            13 => {
                if v_isShared_2720_ == 0 {
                    v___x_2722_ = v___x_2719_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
                    v___x_2722_ = v_reuseFailAlloc_2723_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_as_2727_: *mut leanh::LeanObject,
    mut v_sz_2728_: *mut leanh::LeanObject,
    mut v_i_2729_: *mut leanh::LeanObject,
    mut v_b_2730_: *mut leanh::LeanObject,
    mut v___y_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
    mut v___y_2734_: *mut leanh::LeanObject,
    mut v___y_2735_: *mut leanh::LeanObject,
    mut v___y_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2737_: usize = 0;
    let mut v_i_boxed_2738_: usize = 0;
    let mut v_res_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2737_ = leanh::lean_unbox_usize(v_sz_2728_);
    leanh::lean_dec(v_sz_2728_);
    v_i_boxed_2738_ = leanh::lean_unbox_usize(v_i_2729_);
    leanh::lean_dec(v_i_2729_);
    v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_2727_, v_sz_boxed_2737_, v_i_boxed_2738_, v_b_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
    leanh::lean_dec(v___y_2735_);
    leanh::lean_dec_ref(v___y_2734_);
    leanh::lean_dec(v___y_2733_);
    leanh::lean_dec_ref(v___y_2732_);
    leanh::lean_dec(v___y_2731_);
    leanh::lean_dec_ref(v_as_2727_);
    return v_res_2739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(
    mut v_as_2740_: *mut leanh::LeanObject,
    mut v_sz_2741_: usize,
    mut v_i_2742_: usize,
    mut v_b_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_a_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v_a_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_a_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_unused_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2750_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
                if v___x_2750_ == 0 {
                    v___x_2751_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2751_, 0, v_b_2743_);
                    return v___x_2751_;
                } else {
                    v_snd_2752_ = leanh::lean_ctor_get(v_b_2743_, 1);
                    v_isSharedCheck_2835_ = (!leanh::lean_is_exclusive(v_b_2743_)) as u8;
                    if v_isSharedCheck_2835_ == 0 {
                        v_unused_2836_ = leanh::lean_ctor_get(v_b_2743_, 0);
                        leanh::lean_dec(v_unused_2836_);
                        v___x_2754_ = v_b_2743_;
                        v_isShared_2755_ = v_isSharedCheck_2835_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2752_);
                        leanh::lean_dec(v_b_2743_);
                        v___x_2754_ = leanh::lean_box(0);
                        v_isShared_2755_ = v_isSharedCheck_2835_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2756_ = leanh::lean_box(0);
                v_a_2765_ = lean_array_uget_borrowed(v_as_2740_, v_i_2742_);
                if leanh::lean_obj_tag(v_a_2765_) == 0 {
                    v_a_2758_ = v_snd_2752_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_2752_);
                    v_val_2766_ = leanh::lean_ctor_get(v_a_2765_, 0);
                    v___x_2767_ = lean_st_ref_get(v___y_2744_);
                    v_snd_2768_ = leanh::lean_ctor_get(v___x_2767_, 1);
                    leanh::lean_inc(v_snd_2768_);
                    leanh::lean_dec(v___x_2767_);
                    v___x_2769_ = leanh::lean_box(0);
                    v___x_2770_ = l_Lean_LocalDecl_fvarId(v_val_2766_);
                    v___x_2771_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_2770_, v_snd_2768_);
                    if v___x_2771_ == 0 {
                        v___x_2772_ = l_Lean_LocalDecl_type(v_val_2766_);
                        leanh::lean_inc_ref(v___x_2772_);
                        v___x_2773_ = l_Lean_Meta_isProp(
                            v___x_2772_,
                            v___y_2745_,
                            v___y_2746_,
                            v___y_2747_,
                            v___y_2748_,
                        );
                        if leanh::lean_obj_tag(v___x_2773_) == 0 {
                            v_a_2774_ = leanh::lean_ctor_get(v___x_2773_, 0);
                            leanh::lean_inc(v_a_2774_);
                            leanh::lean_dec_ref_known(v___x_2773_, 1);
                            v___f_2775_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2775_, 0, v_snd_2768_);
                            v___x_2776_ = leanh::lean_box((v___x_2771_) as usize);
                            v___f_2777_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                            leanh::lean_closure_set(v___f_2777_, 0, v___x_2776_);
                            v___x_2806_ = (leanh::lean_unbox(v_a_2774_) as u8);
                            leanh::lean_dec(v_a_2774_);
                            if v___x_2806_ == 0 {
                                leanh::lean_dec_ref(v___x_2772_);
                                v___y_2779_ = v___y_2744_;
                                v___y_2780_ = v___y_2745_;
                                v___y_2781_ = v___y_2746_;
                                v___y_2782_ = v___y_2747_;
                                v___y_2783_ = v___y_2748_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v___f_2777_);
                                leanh::lean_inc_ref(v___f_2775_);
                                v___x_2807_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_2772_, v___f_2775_, v___f_2777_, v___y_2746_);
                                if leanh::lean_obj_tag(v___x_2807_) == 0 {
                                    v_a_2808_ = leanh::lean_ctor_get(v___x_2807_, 0);
                                    leanh::lean_inc(v_a_2808_);
                                    leanh::lean_dec_ref_known(v___x_2807_, 1);
                                    v___x_2809_ = (leanh::lean_unbox(v_a_2808_) as u8);
                                    leanh::lean_dec(v_a_2808_);
                                    if v___x_2809_ == 0 {
                                        v___y_2779_ = v___y_2744_;
                                        v___y_2780_ = v___y_2745_;
                                        v___y_2781_ = v___y_2746_;
                                        v___y_2782_ = v___y_2747_;
                                        v___y_2783_ = v___y_2748_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___x_2770_);
                                        v___x_2810_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2770_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
                                        if leanh::lean_obj_tag(v___x_2810_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2810_, 1);
                                            v___y_2779_ = v___y_2744_;
                                            v___y_2780_ = v___y_2745_;
                                            v___y_2781_ = v___y_2746_;
                                            v___y_2782_ = v___y_2747_;
                                            v___y_2783_ = v___y_2748_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v___f_2777_);
                                            leanh::lean_dec_ref(v___f_2775_);
                                            leanh::lean_dec(v___x_2770_);
                                            leanh::lean_del_object(v___x_2754_);
                                            v_a_2811_ = leanh::lean_ctor_get(v___x_2810_, 0);
                                            v_isSharedCheck_2818_ =
                                                (!leanh::lean_is_exclusive(v___x_2810_))
                                                    as u8;
                                            if v_isSharedCheck_2818_ == 0 {
                                                v___x_2813_ = v___x_2810_;
                                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2811_);
                                                leanh::lean_dec(v___x_2810_);
                                                v___x_2813_ = leanh::lean_box(0);
                                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___f_2777_);
                                    leanh::lean_dec_ref(v___f_2775_);
                                    leanh::lean_dec(v___x_2770_);
                                    leanh::lean_del_object(v___x_2754_);
                                    v_a_2819_ = leanh::lean_ctor_get(v___x_2807_, 0);
                                    v_isSharedCheck_2826_ =
                                        (!leanh::lean_is_exclusive(v___x_2807_)) as u8;
                                    if v_isSharedCheck_2826_ == 0 {
                                        v___x_2821_ = v___x_2807_;
                                        v_isShared_2822_ = v_isSharedCheck_2826_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2819_);
                                        leanh::lean_dec(v___x_2807_);
                                        v___x_2821_ = leanh::lean_box(0);
                                        v_isShared_2822_ = v_isSharedCheck_2826_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2772_);
                            leanh::lean_dec(v___x_2770_);
                            leanh::lean_dec(v_snd_2768_);
                            leanh::lean_del_object(v___x_2754_);
                            v_a_2827_ = leanh::lean_ctor_get(v___x_2773_, 0);
                            v_isSharedCheck_2834_ =
                                (!leanh::lean_is_exclusive(v___x_2773_)) as u8;
                            if v_isSharedCheck_2834_ == 0 {
                                v___x_2829_ = v___x_2773_;
                                v_isShared_2830_ = v_isSharedCheck_2834_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2827_);
                                leanh::lean_dec(v___x_2773_);
                                v___x_2829_ = leanh::lean_box(0);
                                v_isShared_2830_ = v_isSharedCheck_2834_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2770_);
                        leanh::lean_dec(v_snd_2768_);
                        v_a_2758_ = v___x_2769_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2755_ == 0 {
                    leanh::lean_ctor_set(v___x_2754_, 1, v_a_2758_);
                    leanh::lean_ctor_set(v___x_2754_, 0, v___x_2756_);
                    v___x_2760_ = v___x_2754_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_a_2758_);
                    v___x_2760_ = v_reuseFailAlloc_2764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2761_ = 1usize;
                v___x_2762_ = lean_usize_add(v_i_2742_, v___x_2761_);
                v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_2740_, v_sz_2741_, v___x_2762_, v___x_2760_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
                return v___x_2763_;
            }
            4 => {
                v___x_2784_ = l_Lean_LocalDecl_value_x3f(v_val_2766_, v___x_2771_);
                if leanh::lean_obj_tag(v___x_2784_) == 1 {
                    v_val_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    leanh::lean_inc(v_val_2785_);
                    leanh::lean_dec_ref_known(v___x_2784_, 1);
                    v___x_2786_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_2785_, v___f_2775_, v___f_2777_, v___y_2781_);
                    if leanh::lean_obj_tag(v___x_2786_) == 0 {
                        v_a_2787_ = leanh::lean_ctor_get(v___x_2786_, 0);
                        leanh::lean_inc(v_a_2787_);
                        leanh::lean_dec_ref_known(v___x_2786_, 1);
                        v___x_2788_ = (leanh::lean_unbox(v_a_2787_) as u8);
                        leanh::lean_dec(v_a_2787_);
                        if v___x_2788_ == 0 {
                            leanh::lean_dec(v___x_2770_);
                            v_a_2758_ = v___x_2769_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2789_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_2770_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
                            if leanh::lean_obj_tag(v___x_2789_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2789_, 1);
                                v_a_2758_ = v___x_2769_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_2754_);
                                v_a_2790_ = leanh::lean_ctor_get(v___x_2789_, 0);
                                v_isSharedCheck_2797_ =
                                    (!leanh::lean_is_exclusive(v___x_2789_)) as u8;
                                if v_isSharedCheck_2797_ == 0 {
                                    v___x_2792_ = v___x_2789_;
                                    v_isShared_2793_ = v_isSharedCheck_2797_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2790_);
                                    leanh::lean_dec(v___x_2789_);
                                    v___x_2792_ = leanh::lean_box(0);
                                    v_isShared_2793_ = v_isSharedCheck_2797_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2770_);
                        leanh::lean_del_object(v___x_2754_);
                        v_a_2798_ = leanh::lean_ctor_get(v___x_2786_, 0);
                        v_isSharedCheck_2805_ =
                            (!leanh::lean_is_exclusive(v___x_2786_)) as u8;
                        if v_isSharedCheck_2805_ == 0 {
                            v___x_2800_ = v___x_2786_;
                            v_isShared_2801_ = v_isSharedCheck_2805_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2798_);
                            leanh::lean_dec(v___x_2786_);
                            v___x_2800_ = leanh::lean_box(0);
                            v_isShared_2801_ = v_isSharedCheck_2805_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2784_);
                    leanh::lean_dec_ref(v___f_2777_);
                    leanh::lean_dec_ref(v___f_2775_);
                    leanh::lean_dec(v___x_2770_);
                    v_a_2758_ = v___x_2769_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2793_ == 0 {
                    v___x_2795_ = v___x_2792_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2795_;
            }
            7 => {
                if v_isShared_2801_ == 0 {
                    v___x_2803_ = v___x_2800_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2803_;
            }
            9 => {
                if v_isShared_2814_ == 0 {
                    v___x_2816_ = v___x_2813_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2816_;
            }
            11 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2824_;
            }
            13 => {
                if v_isShared_2830_ == 0 {
                    v___x_2832_ = v___x_2829_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
                    v___x_2832_ = v_reuseFailAlloc_2833_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(
    mut v_as_2837_: *mut leanh::LeanObject,
    mut v_sz_2838_: *mut leanh::LeanObject,
    mut v_i_2839_: *mut leanh::LeanObject,
    mut v_b_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
    mut v___y_2845_: *mut leanh::LeanObject,
    mut v___y_2846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2847_: usize = 0;
    let mut v_i_boxed_2848_: usize = 0;
    let mut v_res_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2847_ = leanh::lean_unbox_usize(v_sz_2838_);
    leanh::lean_dec(v_sz_2838_);
    v_i_boxed_2848_ = leanh::lean_unbox_usize(v_i_2839_);
    leanh::lean_dec(v_i_2839_);
    v_res_2849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_2837_, v_sz_boxed_2847_, v_i_boxed_2848_, v_b_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
    leanh::lean_dec(v___y_2845_);
    leanh::lean_dec_ref(v___y_2844_);
    leanh::lean_dec(v___y_2843_);
    leanh::lean_dec_ref(v___y_2842_);
    leanh::lean_dec(v___y_2841_);
    leanh::lean_dec_ref(v_as_2837_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(
    mut v_init_2850_: *mut leanh::LeanObject,
    mut v_n_2851_: *mut leanh::LeanObject,
    mut v_b_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v_fst_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_a_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_vs_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2891_: usize = 0;
    let mut v___x_2892_: usize = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v_fst_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut v_a_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_2851_) == 0 {
                    v_cs_2859_ = leanh::lean_ctor_get(v_n_2851_, 0);
                    v___x_2860_ = leanh::lean_box(0);
                    v___x_2861_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2861_, 0, v___x_2860_);
                    leanh::lean_ctor_set(v___x_2861_, 1, v_b_2852_);
                    v_sz_2862_ = lean_array_size(v_cs_2859_);
                    v___x_2863_ = 0usize;
                    v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_2850_, v_cs_2859_, v_sz_2862_, v___x_2863_, v___x_2861_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
                    if leanh::lean_obj_tag(v___x_2864_) == 0 {
                        v_a_2865_ = leanh::lean_ctor_get(v___x_2864_, 0);
                        v_isSharedCheck_2879_ =
                            (!leanh::lean_is_exclusive(v___x_2864_)) as u8;
                        if v_isSharedCheck_2879_ == 0 {
                            v___x_2867_ = v___x_2864_;
                            v_isShared_2868_ = v_isSharedCheck_2879_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2865_);
                            leanh::lean_dec(v___x_2864_);
                            v___x_2867_ = leanh::lean_box(0);
                            v_isShared_2868_ = v_isSharedCheck_2879_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2880_ = leanh::lean_ctor_get(v___x_2864_, 0);
                        v_isSharedCheck_2887_ =
                            (!leanh::lean_is_exclusive(v___x_2864_)) as u8;
                        if v_isSharedCheck_2887_ == 0 {
                            v___x_2882_ = v___x_2864_;
                            v_isShared_2883_ = v_isSharedCheck_2887_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2880_);
                            leanh::lean_dec(v___x_2864_);
                            v___x_2882_ = leanh::lean_box(0);
                            v_isShared_2883_ = v_isSharedCheck_2887_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2888_ = leanh::lean_ctor_get(v_n_2851_, 0);
                    v___x_2889_ = leanh::lean_box(0);
                    v___x_2890_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2890_, 0, v___x_2889_);
                    leanh::lean_ctor_set(v___x_2890_, 1, v_b_2852_);
                    v_sz_2891_ = lean_array_size(v_vs_2888_);
                    v___x_2892_ = 0usize;
                    v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_2888_, v_sz_2891_, v___x_2892_, v___x_2890_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
                    if leanh::lean_obj_tag(v___x_2893_) == 0 {
                        v_a_2894_ = leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2908_ =
                            (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2908_ == 0 {
                            v___x_2896_ = v___x_2893_;
                            v_isShared_2897_ = v_isSharedCheck_2908_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2894_);
                            leanh::lean_dec(v___x_2893_);
                            v___x_2896_ = leanh::lean_box(0);
                            v_isShared_2897_ = v_isSharedCheck_2908_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2909_ = leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2916_ =
                            (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2916_ == 0 {
                            v___x_2911_ = v___x_2893_;
                            v_isShared_2912_ = v_isSharedCheck_2916_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2909_);
                            leanh::lean_dec(v___x_2893_);
                            v___x_2911_ = leanh::lean_box(0);
                            v_isShared_2912_ = v_isSharedCheck_2916_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2869_ = leanh::lean_ctor_get(v_a_2865_, 0);
                if leanh::lean_obj_tag(v_fst_2869_) == 0 {
                    v_snd_2870_ = leanh::lean_ctor_get(v_a_2865_, 1);
                    leanh::lean_inc(v_snd_2870_);
                    leanh::lean_dec(v_a_2865_);
                    v___x_2871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2871_, 0, v_snd_2870_);
                    if v_isShared_2868_ == 0 {
                        leanh::lean_ctor_set(v___x_2867_, 0, v___x_2871_);
                        v___x_2873_ = v___x_2867_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
                        v___x_2873_ = v_reuseFailAlloc_2874_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2869_);
                    leanh::lean_dec(v_a_2865_);
                    v_val_2875_ = leanh::lean_ctor_get(v_fst_2869_, 0);
                    leanh::lean_inc(v_val_2875_);
                    leanh::lean_dec_ref_known(v_fst_2869_, 1);
                    if v_isShared_2868_ == 0 {
                        leanh::lean_ctor_set(v___x_2867_, 0, v_val_2875_);
                        v___x_2877_ = v___x_2867_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_val_2875_);
                        v___x_2877_ = v_reuseFailAlloc_2878_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2873_;
            }
            3 => {
                return v___x_2877_;
            }
            4 => {
                if v_isShared_2883_ == 0 {
                    v___x_2885_ = v___x_2882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2886_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
                    v___x_2885_ = v_reuseFailAlloc_2886_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2885_;
            }
            6 => {
                v_fst_2898_ = leanh::lean_ctor_get(v_a_2894_, 0);
                if leanh::lean_obj_tag(v_fst_2898_) == 0 {
                    v_snd_2899_ = leanh::lean_ctor_get(v_a_2894_, 1);
                    leanh::lean_inc(v_snd_2899_);
                    leanh::lean_dec(v_a_2894_);
                    v___x_2900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2900_, 0, v_snd_2899_);
                    if v_isShared_2897_ == 0 {
                        leanh::lean_ctor_set(v___x_2896_, 0, v___x_2900_);
                        v___x_2902_ = v___x_2896_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
                        v___x_2902_ = v_reuseFailAlloc_2903_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2898_);
                    leanh::lean_dec(v_a_2894_);
                    v_val_2904_ = leanh::lean_ctor_get(v_fst_2898_, 0);
                    leanh::lean_inc(v_val_2904_);
                    leanh::lean_dec_ref_known(v_fst_2898_, 1);
                    if v_isShared_2897_ == 0 {
                        leanh::lean_ctor_set(v___x_2896_, 0, v_val_2904_);
                        v___x_2906_ = v___x_2896_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_val_2904_);
                        v___x_2906_ = v_reuseFailAlloc_2907_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2902_;
            }
            8 => {
                return v___x_2906_;
            }
            9 => {
                if v_isShared_2912_ == 0 {
                    v___x_2914_ = v___x_2911_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
                    v___x_2914_ = v_reuseFailAlloc_2915_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(
    mut v_init_2917_: *mut leanh::LeanObject,
    mut v_as_2918_: *mut leanh::LeanObject,
    mut v_sz_2919_: usize,
    mut v_i_2920_: usize,
    mut v_b_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
    mut v___y_2925_: *mut leanh::LeanObject,
    mut v___y_2926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2928_: u8 = 0;
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2933_: u8 = 0;
    let mut v_a_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: usize = 0;
    let mut v___x_2952_: usize = 0;
    let mut v_reuseFailAlloc_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_a_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_unused_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2928_ = lean_usize_dec_lt(v_i_2920_, v_sz_2919_);
                if v___x_2928_ == 0 {
                    v___x_2929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2929_, 0, v_b_2921_);
                    return v___x_2929_;
                } else {
                    v_snd_2930_ = leanh::lean_ctor_get(v_b_2921_, 1);
                    v_isSharedCheck_2964_ = (!leanh::lean_is_exclusive(v_b_2921_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v_unused_2965_ = leanh::lean_ctor_get(v_b_2921_, 0);
                        leanh::lean_dec(v_unused_2965_);
                        v___x_2932_ = v_b_2921_;
                        v_isShared_2933_ = v_isSharedCheck_2964_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2930_);
                        leanh::lean_dec(v_b_2921_);
                        v___x_2932_ = leanh::lean_box(0);
                        v_isShared_2933_ = v_isSharedCheck_2964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2934_ = lean_array_uget_borrowed(v_as_2918_, v_i_2920_);
                leanh::lean_inc(v_snd_2930_);
                v___x_2935_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_2917_, v_a_2934_, v_snd_2930_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
                if leanh::lean_obj_tag(v___x_2935_) == 0 {
                    v_a_2936_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2955_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2955_ == 0 {
                        v___x_2938_ = v___x_2935_;
                        v_isShared_2939_ = v_isSharedCheck_2955_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2936_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2938_ = leanh::lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2955_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2932_);
                    leanh::lean_dec(v_snd_2930_);
                    v_a_2956_ = leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2963_ = (!leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2963_ == 0 {
                        v___x_2958_ = v___x_2935_;
                        v_isShared_2959_ = v_isSharedCheck_2963_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2956_);
                        leanh::lean_dec(v___x_2935_);
                        v___x_2958_ = leanh::lean_box(0);
                        v_isShared_2959_ = v_isSharedCheck_2963_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2936_) == 0 {
                    v___x_2940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2940_, 0, v_a_2936_);
                    if v_isShared_2933_ == 0 {
                        leanh::lean_ctor_set(v___x_2932_, 0, v___x_2940_);
                        v___x_2942_ = v___x_2932_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_snd_2930_);
                        v___x_2942_ = v_reuseFailAlloc_2946_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2938_);
                    leanh::lean_dec(v_snd_2930_);
                    v_a_2947_ = leanh::lean_ctor_get(v_a_2936_, 0);
                    leanh::lean_inc(v_a_2947_);
                    leanh::lean_dec_ref_known(v_a_2936_, 1);
                    v___x_2948_ = leanh::lean_box(0);
                    if v_isShared_2933_ == 0 {
                        leanh::lean_ctor_set(v___x_2932_, 1, v_a_2947_);
                        leanh::lean_ctor_set(v___x_2932_, 0, v___x_2948_);
                        v___x_2950_ = v___x_2932_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2948_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_a_2947_);
                        v___x_2950_ = v_reuseFailAlloc_2954_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2939_ == 0 {
                    leanh::lean_ctor_set(v___x_2938_, 0, v___x_2942_);
                    v___x_2944_ = v___x_2938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
                    v___x_2944_ = v_reuseFailAlloc_2945_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2944_;
            }
            5 => {
                v___x_2951_ = 1usize;
                v___x_2952_ = lean_usize_add(v_i_2920_, v___x_2951_);
                v_i_2920_ = v___x_2952_;
                v_b_2921_ = v___x_2950_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2959_ == 0 {
                    v___x_2961_ = v___x_2958_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
                    v___x_2961_ = v_reuseFailAlloc_2962_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(
    mut v_init_2966_: *mut leanh::LeanObject,
    mut v_as_2967_: *mut leanh::LeanObject,
    mut v_sz_2968_: *mut leanh::LeanObject,
    mut v_i_2969_: *mut leanh::LeanObject,
    mut v_b_2970_: *mut leanh::LeanObject,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2977_: usize = 0;
    let mut v_i_boxed_2978_: usize = 0;
    let mut v_res_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2977_ = leanh::lean_unbox_usize(v_sz_2968_);
    leanh::lean_dec(v_sz_2968_);
    v_i_boxed_2978_ = leanh::lean_unbox_usize(v_i_2969_);
    leanh::lean_dec(v_i_2969_);
    v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_2966_, v_as_2967_, v_sz_boxed_2977_, v_i_boxed_2978_, v_b_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
    leanh::lean_dec(v___y_2975_);
    leanh::lean_dec_ref(v___y_2974_);
    leanh::lean_dec(v___y_2973_);
    leanh::lean_dec_ref(v___y_2972_);
    leanh::lean_dec(v___y_2971_);
    leanh::lean_dec_ref(v_as_2967_);
    return v_res_2979_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(
    mut v_init_2980_: *mut leanh::LeanObject,
    mut v_n_2981_: *mut leanh::LeanObject,
    mut v_b_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
    mut v___y_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2989_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_2980_, v_n_2981_, v_b_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    leanh::lean_dec(v___y_2987_);
    leanh::lean_dec_ref(v___y_2986_);
    leanh::lean_dec(v___y_2985_);
    leanh::lean_dec_ref(v___y_2984_);
    leanh::lean_dec(v___y_2983_);
    leanh::lean_dec_ref(v_n_2981_);
    return v_res_2989_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(
    mut v_t_2990_: *mut leanh::LeanObject,
    mut v_init_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
    mut v___y_2994_: *mut leanh::LeanObject,
    mut v___y_2995_: *mut leanh::LeanObject,
    mut v___y_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3004_: u8 = 0;
    let mut v_a_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3012_: usize = 0;
    let mut v___x_3013_: usize = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v_fst_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut v_a_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3032_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2998_ = leanh::lean_ctor_get(v_t_2990_, 0);
                v_tail_2999_ = leanh::lean_ctor_get(v_t_2990_, 1);
                v___x_3000_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_2991_, v_root_2998_, v_init_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
                if leanh::lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = leanh::lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3003_ = v___x_3000_;
                        v_isShared_3004_ = v_isSharedCheck_3037_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3001_);
                        leanh::lean_dec(v___x_3000_);
                        v___x_3003_ = leanh::lean_box(0);
                        v_isShared_3004_ = v_isSharedCheck_3037_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3038_ = leanh::lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3045_ = (!leanh::lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_3040_ = v___x_3000_;
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3038_);
                        leanh::lean_dec(v___x_3000_);
                        v___x_3040_ = leanh::lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3001_) == 0 {
                    v_a_3005_ = leanh::lean_ctor_get(v_a_3001_, 0);
                    leanh::lean_inc(v_a_3005_);
                    leanh::lean_dec_ref_known(v_a_3001_, 1);
                    if v_isShared_3004_ == 0 {
                        leanh::lean_ctor_set(v___x_3003_, 0, v_a_3005_);
                        v___x_3007_ = v___x_3003_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3005_);
                        v___x_3007_ = v_reuseFailAlloc_3008_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3003_);
                    v_a_3009_ = leanh::lean_ctor_get(v_a_3001_, 0);
                    leanh::lean_inc(v_a_3009_);
                    leanh::lean_dec_ref_known(v_a_3001_, 1);
                    v___x_3010_ = leanh::lean_box(0);
                    v___x_3011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                    leanh::lean_ctor_set(v___x_3011_, 1, v_a_3009_);
                    v_sz_3012_ = lean_array_size(v_tail_2999_);
                    v___x_3013_ = 0usize;
                    v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_2999_, v_sz_3012_, v___x_3013_, v___x_3011_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
                    if leanh::lean_obj_tag(v___x_3014_) == 0 {
                        v_a_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        v_isSharedCheck_3028_ =
                            (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                        if v_isSharedCheck_3028_ == 0 {
                            v___x_3017_ = v___x_3014_;
                            v_isShared_3018_ = v_isSharedCheck_3028_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3015_);
                            leanh::lean_dec(v___x_3014_);
                            v___x_3017_ = leanh::lean_box(0);
                            v_isShared_3018_ = v_isSharedCheck_3028_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3029_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        v_isSharedCheck_3036_ =
                            (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                        if v_isSharedCheck_3036_ == 0 {
                            v___x_3031_ = v___x_3014_;
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3029_);
                            leanh::lean_dec(v___x_3014_);
                            v___x_3031_ = leanh::lean_box(0);
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3007_;
            }
            3 => {
                v_fst_3019_ = leanh::lean_ctor_get(v_a_3015_, 0);
                if leanh::lean_obj_tag(v_fst_3019_) == 0 {
                    v_snd_3020_ = leanh::lean_ctor_get(v_a_3015_, 1);
                    leanh::lean_inc(v_snd_3020_);
                    leanh::lean_dec(v_a_3015_);
                    if v_isShared_3018_ == 0 {
                        leanh::lean_ctor_set(v___x_3017_, 0, v_snd_3020_);
                        v___x_3022_ = v___x_3017_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_snd_3020_);
                        v___x_3022_ = v_reuseFailAlloc_3023_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3019_);
                    leanh::lean_dec(v_a_3015_);
                    v_val_3024_ = leanh::lean_ctor_get(v_fst_3019_, 0);
                    leanh::lean_inc(v_val_3024_);
                    leanh::lean_dec_ref_known(v_fst_3019_, 1);
                    if v_isShared_3018_ == 0 {
                        leanh::lean_ctor_set(v___x_3017_, 0, v_val_3024_);
                        v___x_3026_ = v___x_3017_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_val_3024_);
                        v___x_3026_ = v_reuseFailAlloc_3027_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3022_;
            }
            5 => {
                return v___x_3026_;
            }
            6 => {
                if v_isShared_3032_ == 0 {
                    v___x_3034_ = v___x_3031_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3034_;
            }
            8 => {
                if v_isShared_3041_ == 0 {
                    v___x_3043_ = v___x_3040_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
                    v___x_3043_ = v_reuseFailAlloc_3044_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(
    mut v_t_3046_: *mut leanh::LeanObject,
    mut v_init_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_3046_, v_init_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
    leanh::lean_dec(v___y_3052_);
    leanh::lean_dec_ref(v___y_3051_);
    leanh::lean_dec(v___y_3050_);
    leanh::lean_dec_ref(v___y_3049_);
    leanh::lean_dec(v___y_3048_);
    leanh::lean_dec_ref(v_t_3046_);
    return v_res_3054_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(
    mut v_a_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_a_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_unused_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3061_ = leanh::lean_ctor_get(v_a_3056_, 2);
                v_decls_3062_ = leanh::lean_ctor_get(v_lctx_3061_, 1);
                v___x_3063_ = leanh::lean_box(0);
                v___x_3064_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_3062_, v___x_3063_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
                if leanh::lean_obj_tag(v___x_3064_) == 0 {
                    v_isSharedCheck_3071_ = (!leanh::lean_is_exclusive(v___x_3064_)) as u8;
                    if v_isSharedCheck_3071_ == 0 {
                        v_unused_3072_ = leanh::lean_ctor_get(v___x_3064_, 0);
                        leanh::lean_dec(v_unused_3072_);
                        v___x_3066_ = v___x_3064_;
                        v_isShared_3067_ = v_isSharedCheck_3071_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3064_);
                        v___x_3066_ = leanh::lean_box(0);
                        v_isShared_3067_ = v_isSharedCheck_3071_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3064_;
                }
            }
            1 => {
                if v_isShared_3067_ == 0 {
                    leanh::lean_ctor_set(v___x_3066_, 0, v___x_3063_);
                    v___x_3069_ = v___x_3066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3063_);
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(
    mut v_a_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3079_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(
        v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_,
    );
    leanh::lean_dec(v_a_3077_);
    leanh::lean_dec_ref(v_a_3076_);
    leanh::lean_dec(v_a_3075_);
    leanh::lean_dec_ref(v_a_3074_);
    leanh::lean_dec(v_a_3073_);
    return v_res_3079_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(
    mut v_a_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
    mut v_a_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_unused_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_unused_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3086_ = lean_st_ref_take(v_a_3080_);
                v_snd_3087_ = leanh::lean_ctor_get(v___x_3086_, 1);
                v_isSharedCheck_3111_ = (!leanh::lean_is_exclusive(v___x_3086_)) as u8;
                if v_isSharedCheck_3111_ == 0 {
                    v_unused_3112_ = leanh::lean_ctor_get(v___x_3086_, 0);
                    leanh::lean_dec(v_unused_3112_);
                    v___x_3089_ = v___x_3086_;
                    v_isShared_3090_ = v_isSharedCheck_3111_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3087_);
                    leanh::lean_dec(v___x_3086_);
                    v___x_3089_ = leanh::lean_box(0);
                    v_isShared_3090_ = v_isSharedCheck_3111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3091_ = 0;
                v___x_3092_ = leanh::lean_box((v___x_3091_) as usize);
                if v_isShared_3090_ == 0 {
                    leanh::lean_ctor_set(v___x_3089_, 0, v___x_3092_);
                    v___x_3094_ = v___x_3089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_snd_3087_);
                    v___x_3094_ = v_reuseFailAlloc_3110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3095_ = lean_st_ref_set(v_a_3080_, v___x_3094_);
                v___x_3096_ =
                    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(
                        v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_,
                    );
                if leanh::lean_obj_tag(v___x_3096_) == 0 {
                    v_isSharedCheck_3108_ = (!leanh::lean_is_exclusive(v___x_3096_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v_unused_3109_ = leanh::lean_ctor_get(v___x_3096_, 0);
                        leanh::lean_dec(v_unused_3109_);
                        v___x_3098_ = v___x_3096_;
                        v_isShared_3099_ = v_isSharedCheck_3108_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3096_);
                        v___x_3098_ = leanh::lean_box(0);
                        v_isShared_3099_ = v_isSharedCheck_3108_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3096_;
                }
            }
            3 => {
                v___x_3100_ = lean_st_ref_get(v_a_3080_);
                v_fst_3101_ = leanh::lean_ctor_get(v___x_3100_, 0);
                leanh::lean_inc(v_fst_3101_);
                leanh::lean_dec(v___x_3100_);
                v___x_3102_ = (leanh::lean_unbox(v_fst_3101_) as u8);
                leanh::lean_dec(v_fst_3101_);
                if v___x_3102_ == 0 {
                    v___x_3103_ = leanh::lean_box(0);
                    if v_isShared_3099_ == 0 {
                        leanh::lean_ctor_set(v___x_3098_, 0, v___x_3103_);
                        v___x_3105_ = v___x_3098_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
                        v___x_3105_ = v_reuseFailAlloc_3106_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3098_);
                    state = 0;
                    continue;
                }
            }
            4 => {
                return v___x_3105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(
    mut v_a_3113_: *mut leanh::LeanObject,
    mut v_a_3114_: *mut leanh::LeanObject,
    mut v_a_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
    mut v_a_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(
        v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_,
    );
    leanh::lean_dec(v_a_3117_);
    leanh::lean_dec_ref(v_a_3116_);
    leanh::lean_dec(v_a_3115_);
    leanh::lean_dec_ref(v_a_3114_);
    leanh::lean_dec(v_a_3113_);
    return v_res_3119_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(
    mut v_as_3120_: *mut leanh::LeanObject,
    mut v_i_3121_: usize,
    mut v_stop_3122_: usize,
    mut v_b_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: usize = 0;
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3130_ = lean_usize_dec_eq(v_i_3121_, v_stop_3122_);
                if v___x_3130_ == 0 {
                    v___x_3131_ = lean_array_uget_borrowed(v_as_3120_, v_i_3121_);
                    leanh::lean_inc(v___x_3131_);
                    v___x_3132_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(
                            v___x_3131_,
                            v___y_3124_,
                            v___y_3125_,
                            v___y_3126_,
                            v___y_3127_,
                            v___y_3128_,
                        );
                    if leanh::lean_obj_tag(v___x_3132_) == 0 {
                        v_a_3133_ = leanh::lean_ctor_get(v___x_3132_, 0);
                        leanh::lean_inc(v_a_3133_);
                        leanh::lean_dec_ref_known(v___x_3132_, 1);
                        v___x_3134_ = 1usize;
                        v___x_3135_ = lean_usize_add(v_i_3121_, v___x_3134_);
                        v_i_3121_ = v___x_3135_;
                        v_b_3123_ = v_a_3133_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3132_;
                    }
                } else {
                    v___x_3137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3137_, 0, v_b_3123_);
                    return v___x_3137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(
    mut v_as_3138_: *mut leanh::LeanObject,
    mut v_i_3139_: *mut leanh::LeanObject,
    mut v_stop_3140_: *mut leanh::LeanObject,
    mut v_b_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3148_: usize = 0;
    let mut v_stop_boxed_3149_: usize = 0;
    let mut v_res_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3148_ = leanh::lean_unbox_usize(v_i_3139_);
    leanh::lean_dec(v_i_3139_);
    v_stop_boxed_3149_ = leanh::lean_unbox_usize(v_stop_3140_);
    leanh::lean_dec(v_stop_3140_);
    v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_3138_, v_i_boxed_3148_, v_stop_boxed_3149_, v_b_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
    leanh::lean_dec(v___y_3146_);
    leanh::lean_dec_ref(v___y_3145_);
    leanh::lean_dec(v___y_3144_);
    leanh::lean_dec_ref(v___y_3143_);
    leanh::lean_dec(v___y_3142_);
    leanh::lean_dec_ref(v_as_3138_);
    return v_res_3150_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(
    mut v_mvarId_3151_: *mut leanh::LeanObject,
    mut v_toPreserve_3152_: *mut leanh::LeanObject,
    mut v_indirectProps_3153_: u8,
    mut v_a_3154_: *mut leanh::LeanObject,
    mut v_a_3155_: *mut leanh::LeanObject,
    mut v_a_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut v___y_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: usize = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v_a_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3185_ = l_Lean_MVarId_getType(
                    v_mvarId_3151_,
                    v_a_3155_,
                    v_a_3156_,
                    v_a_3157_,
                    v_a_3158_,
                );
                if leanh::lean_obj_tag(v___x_3185_) == 0 {
                    v_a_3186_ = leanh::lean_ctor_get(v___x_3185_, 0);
                    leanh::lean_inc(v_a_3186_);
                    leanh::lean_dec_ref_known(v___x_3185_, 1);
                    v___x_3187_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_3186_, v_a_3156_);
                    v_a_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                    leanh::lean_inc(v_a_3188_);
                    leanh::lean_dec_ref(v___x_3187_);
                    v___x_3189_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(
                            v_a_3188_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_,
                        );
                    if leanh::lean_obj_tag(v___x_3189_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3189_, 1);
                        v___x_3190_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3191_ = lean_array_get_size(v_toPreserve_3152_);
                        v___x_3192_ = lean_nat_dec_lt(v___x_3190_, v___x_3191_);
                        if v___x_3192_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_3193_ = leanh::lean_box(0);
                            v___x_3194_ = lean_nat_dec_le(v___x_3191_, v___x_3191_);
                            if v___x_3194_ == 0 {
                                if v___x_3192_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3195_ = 0usize;
                                    v___x_3196_ = lean_usize_of_nat(v___x_3191_);
                                    v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_3152_, v___x_3195_, v___x_3196_, v___x_3193_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
                                    v___y_3176_ = v___x_3197_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___x_3198_ = 0usize;
                                v___x_3199_ = lean_usize_of_nat(v___x_3191_);
                                v___x_3200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_3152_, v___x_3198_, v___x_3199_, v___x_3193_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
                                v___y_3176_ = v___x_3200_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_3201_ = leanh::lean_ctor_get(v___x_3189_, 0);
                        v_isSharedCheck_3208_ =
                            (!leanh::lean_is_exclusive(v___x_3189_)) as u8;
                        if v_isSharedCheck_3208_ == 0 {
                            v___x_3203_ = v___x_3189_;
                            v_isShared_3204_ = v_isSharedCheck_3208_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3201_);
                            leanh::lean_dec(v___x_3189_);
                            v___x_3203_ = leanh::lean_box(0);
                            v_isShared_3204_ = v_isSharedCheck_3208_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3209_ = leanh::lean_ctor_get(v___x_3185_, 0);
                    v_isSharedCheck_3216_ = (!leanh::lean_is_exclusive(v___x_3185_)) as u8;
                    if v_isSharedCheck_3216_ == 0 {
                        v___x_3211_ = v___x_3185_;
                        v_isShared_3212_ = v_isSharedCheck_3216_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3209_);
                        leanh::lean_dec(v___x_3185_);
                        v___x_3211_ = leanh::lean_box(0);
                        v_isShared_3212_ = v_isSharedCheck_3216_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3162_ = lean_st_ref_get(v___y_3161_);
                v_snd_3163_ = leanh::lean_ctor_get(v___x_3162_, 1);
                leanh::lean_inc(v_snd_3163_);
                leanh::lean_dec(v___x_3162_);
                v___x_3164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3164_, 0, v_snd_3163_);
                return v___x_3164_;
            }
            2 => {
                if v_indirectProps_3153_ == 0 {
                    v___y_3161_ = v_a_3154_;
                    state = 1;
                    continue;
                } else {
                    v___x_3166_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(
                            v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_,
                        );
                    if leanh::lean_obj_tag(v___x_3166_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3166_, 1);
                        v___y_3161_ = v_a_3154_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3167_ = leanh::lean_ctor_get(v___x_3166_, 0);
                        v_isSharedCheck_3174_ =
                            (!leanh::lean_is_exclusive(v___x_3166_)) as u8;
                        if v_isSharedCheck_3174_ == 0 {
                            v___x_3169_ = v___x_3166_;
                            v_isShared_3170_ = v_isSharedCheck_3174_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3167_);
                            leanh::lean_dec(v___x_3166_);
                            v___x_3169_ = leanh::lean_box(0);
                            v_isShared_3170_ = v_isSharedCheck_3174_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3170_ == 0 {
                    v___x_3172_ = v___x_3169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
                    v___x_3172_ = v_reuseFailAlloc_3173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3172_;
            }
            5 => {
                if leanh::lean_obj_tag(v___y_3176_) == 0 {
                    leanh::lean_dec_ref_known(v___y_3176_, 1);
                    state = 2;
                    continue;
                } else {
                    v_a_3177_ = leanh::lean_ctor_get(v___y_3176_, 0);
                    v_isSharedCheck_3184_ = (!leanh::lean_is_exclusive(v___y_3176_)) as u8;
                    if v_isSharedCheck_3184_ == 0 {
                        v___x_3179_ = v___y_3176_;
                        v_isShared_3180_ = v_isSharedCheck_3184_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3177_);
                        leanh::lean_dec(v___y_3176_);
                        v___x_3179_ = leanh::lean_box(0);
                        v_isShared_3180_ = v_isSharedCheck_3184_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3180_ == 0 {
                    v___x_3182_ = v___x_3179_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
                    v___x_3182_ = v_reuseFailAlloc_3183_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3182_;
            }
            8 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3206_;
            }
            10 => {
                if v_isShared_3212_ == 0 {
                    v___x_3214_ = v___x_3211_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3215_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
                    v___x_3214_ = v_reuseFailAlloc_3215_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(
    mut v_mvarId_3217_: *mut leanh::LeanObject,
    mut v_toPreserve_3218_: *mut leanh::LeanObject,
    mut v_indirectProps_3219_: *mut leanh::LeanObject,
    mut v_a_3220_: *mut leanh::LeanObject,
    mut v_a_3221_: *mut leanh::LeanObject,
    mut v_a_3222_: *mut leanh::LeanObject,
    mut v_a_3223_: *mut leanh::LeanObject,
    mut v_a_3224_: *mut leanh::LeanObject,
    mut v_a_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indirectProps_boxed_3226_: u8 = 0;
    let mut v_res_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indirectProps_boxed_3226_ = (leanh::lean_unbox(v_indirectProps_3219_) as u8);
    v_res_3227_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(
        v_mvarId_3217_,
        v_toPreserve_3218_,
        v_indirectProps_boxed_3226_,
        v_a_3220_,
        v_a_3221_,
        v_a_3222_,
        v_a_3223_,
        v_a_3224_,
    );
    leanh::lean_dec(v_a_3224_);
    leanh::lean_dec_ref(v_a_3223_);
    leanh::lean_dec(v_a_3222_);
    leanh::lean_dec_ref(v_a_3221_);
    leanh::lean_dec(v_a_3220_);
    leanh::lean_dec_ref(v_toPreserve_3218_);
    return v_res_3227_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(
    mut v_e_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_unused_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3231_ = l_Lean_Expr_hasMVar(v_e_3228_);
                if v___x_3231_ == 0 {
                    v___x_3232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3232_, 0, v_e_3228_);
                    return v___x_3232_;
                } else {
                    v___x_3233_ = lean_st_ref_get(v___y_3229_);
                    v_mctx_3234_ = leanh::lean_ctor_get(v___x_3233_, 0);
                    leanh::lean_inc_ref(v_mctx_3234_);
                    leanh::lean_dec(v___x_3233_);
                    v___x_3235_ = l_Lean_instantiateMVarsCore(v_mctx_3234_, v_e_3228_);
                    v_fst_3236_ = leanh::lean_ctor_get(v___x_3235_, 0);
                    leanh::lean_inc(v_fst_3236_);
                    v_snd_3237_ = leanh::lean_ctor_get(v___x_3235_, 1);
                    leanh::lean_inc(v_snd_3237_);
                    leanh::lean_dec_ref(v___x_3235_);
                    v___x_3238_ = lean_st_ref_take(v___y_3229_);
                    v_cache_3239_ = leanh::lean_ctor_get(v___x_3238_, 1);
                    v_zetaDeltaFVarIds_3240_ = leanh::lean_ctor_get(v___x_3238_, 2);
                    v_postponed_3241_ = leanh::lean_ctor_get(v___x_3238_, 3);
                    v_diag_3242_ = leanh::lean_ctor_get(v___x_3238_, 4);
                    v_isSharedCheck_3251_ = (!leanh::lean_is_exclusive(v___x_3238_)) as u8;
                    if v_isSharedCheck_3251_ == 0 {
                        v_unused_3252_ = leanh::lean_ctor_get(v___x_3238_, 0);
                        leanh::lean_dec(v_unused_3252_);
                        v___x_3244_ = v___x_3238_;
                        v_isShared_3245_ = v_isSharedCheck_3251_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3242_);
                        leanh::lean_inc(v_postponed_3241_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3240_);
                        leanh::lean_inc(v_cache_3239_);
                        leanh::lean_dec(v___x_3238_);
                        v___x_3244_ = leanh::lean_box(0);
                        v_isShared_3245_ = v_isSharedCheck_3251_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3245_ == 0 {
                    leanh::lean_ctor_set(v___x_3244_, 0, v_snd_3237_);
                    v___x_3247_ = v___x_3244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3250_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_snd_3237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_cache_3239_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3250_,
                        2,
                        v_zetaDeltaFVarIds_3240_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 3, v_postponed_3241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 4, v_diag_3242_);
                    v___x_3247_ = v_reuseFailAlloc_3250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3248_ = lean_st_ref_set(v___y_3229_, v___x_3247_);
                v___x_3249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3249_, 0, v_fst_3236_);
                return v___x_3249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(
    mut v_e_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_3253_, v___y_3254_);
    leanh::lean_dec(v___y_3254_);
    return v_res_3256_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(
    mut v_e_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_3257_, v___y_3259_);
    return v___x_3263_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(
    mut v_e_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
    mut v___y_3266_: *mut leanh::LeanObject,
    mut v___y_3267_: *mut leanh::LeanObject,
    mut v___y_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
    leanh::lean_dec(v___y_3268_);
    leanh::lean_dec_ref(v___y_3267_);
    leanh::lean_dec(v___y_3266_);
    leanh::lean_dec_ref(v___y_3265_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(
    mut v_mvarId_3271_: *mut leanh::LeanObject,
    mut v_x_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3282_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3271_,
                    v_x_3272_,
                    v___y_3273_,
                    v___y_3274_,
                    v___y_3275_,
                    v___y_3276_,
                );
                if leanh::lean_obj_tag(v___x_3278_) == 0 {
                    v_a_3279_ = leanh::lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3286_ = (!leanh::lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3286_ == 0 {
                        v___x_3281_ = v___x_3278_;
                        v_isShared_3282_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3279_);
                        leanh::lean_dec(v___x_3278_);
                        v___x_3281_ = leanh::lean_box(0);
                        v_isShared_3282_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3287_ = leanh::lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3294_ = (!leanh::lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3278_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3287_);
                        leanh::lean_dec(v___x_3278_);
                        v___x_3289_ = leanh::lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3282_ == 0 {
                    v___x_3284_ = v___x_3281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
                    v___x_3284_ = v_reuseFailAlloc_3285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3284_;
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    v___x_3292_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(
    mut v_mvarId_3295_: *mut leanh::LeanObject,
    mut v_x_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
    mut v___y_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_3295_, v_x_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    leanh::lean_dec(v___y_3300_);
    leanh::lean_dec_ref(v___y_3299_);
    leanh::lean_dec(v___y_3298_);
    leanh::lean_dec_ref(v___y_3297_);
    return v_res_3302_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(
    mut v_00_u03b1_3303_: *mut leanh::LeanObject,
    mut v_mvarId_3304_: *mut leanh::LeanObject,
    mut v_x_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
    mut v___y_3309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_3304_, v_x_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(
    mut v_00_u03b1_3312_: *mut leanh::LeanObject,
    mut v_mvarId_3313_: *mut leanh::LeanObject,
    mut v_x_3314_: *mut leanh::LeanObject,
    mut v___y_3315_: *mut leanh::LeanObject,
    mut v___y_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_3312_, v_mvarId_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
    leanh::lean_dec(v___y_3318_);
    leanh::lean_dec_ref(v___y_3317_);
    leanh::lean_dec(v___y_3316_);
    leanh::lean_dec_ref(v___y_3315_);
    return v_res_3320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(
    mut v_a_3321_: *mut leanh::LeanObject,
    mut v_as_3322_: *mut leanh::LeanObject,
    mut v_i_3323_: usize,
    mut v_stop_3324_: usize,
    mut v_b_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: usize = 0;
    let mut v___x_3329_: usize = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvar_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3331_ = lean_usize_dec_eq(v_i_3323_, v_stop_3324_);
                if v___x_3331_ == 0 {
                    v___x_3332_ = lean_array_uget_borrowed(v_as_3322_, v_i_3323_);
                    v_fvar_3333_ = leanh::lean_ctor_get(v___x_3332_, 1);
                    v___x_3334_ = l_Lean_Expr_fvarId_x21(v_fvar_3333_);
                    v___x_3335_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_3334_, v_a_3321_);
                    leanh::lean_dec(v___x_3334_);
                    if v___x_3335_ == 0 {
                        v___y_3327_ = v_b_3325_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_3332_);
                        v___x_3336_ = lean_array_push(v_b_3325_, v___x_3332_);
                        v___y_3327_ = v___x_3336_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3325_;
                }
            }
            1 => {
                v___x_3328_ = 1usize;
                v___x_3329_ = lean_usize_add(v_i_3323_, v___x_3328_);
                v_i_3323_ = v___x_3329_;
                v_b_3325_ = v___y_3327_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(
    mut v_a_3337_: *mut leanh::LeanObject,
    mut v_as_3338_: *mut leanh::LeanObject,
    mut v_i_3339_: *mut leanh::LeanObject,
    mut v_stop_3340_: *mut leanh::LeanObject,
    mut v_b_3341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3342_: usize = 0;
    let mut v_stop_boxed_3343_: usize = 0;
    let mut v_res_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3342_ = leanh::lean_unbox_usize(v_i_3339_);
    leanh::lean_dec(v_i_3339_);
    v_stop_boxed_3343_ = leanh::lean_unbox_usize(v_stop_3340_);
    leanh::lean_dec(v_stop_3340_);
    v_res_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_3337_, v_as_3338_, v_i_boxed_3342_, v_stop_boxed_3343_, v_b_3341_);
    leanh::lean_dec_ref(v_as_3338_);
    leanh::lean_dec(v_a_3337_);
    return v_res_3344_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(
    mut v_x_3345_: *mut leanh::LeanObject,
    mut v_x_3346_: *mut leanh::LeanObject,
    mut v_x_3347_: *mut leanh::LeanObject,
    mut v_x_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: u8 = 0;
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3349_ = leanh::lean_ctor_get(v_x_3345_, 0);
                v_vs_3350_ = leanh::lean_ctor_get(v_x_3345_, 1);
                v_isSharedCheck_3374_ = (!leanh::lean_is_exclusive(v_x_3345_)) as u8;
                if v_isSharedCheck_3374_ == 0 {
                    v___x_3352_ = v_x_3345_;
                    v_isShared_3353_ = v_isSharedCheck_3374_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3350_);
                    leanh::lean_inc(v_ks_3349_);
                    leanh::lean_dec(v_x_3345_);
                    v___x_3352_ = leanh::lean_box(0);
                    v_isShared_3353_ = v_isSharedCheck_3374_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3354_ = lean_array_get_size(v_ks_3349_);
                v___x_3355_ = lean_nat_dec_lt(v_x_3346_, v___x_3354_);
                if v___x_3355_ == 0 {
                    leanh::lean_dec(v_x_3346_);
                    v___x_3356_ = lean_array_push(v_ks_3349_, v_x_3347_);
                    v___x_3357_ = lean_array_push(v_vs_3350_, v_x_3348_);
                    if v_isShared_3353_ == 0 {
                        leanh::lean_ctor_set(v___x_3352_, 1, v___x_3357_);
                        leanh::lean_ctor_set(v___x_3352_, 0, v___x_3356_);
                        v___x_3359_ = v___x_3352_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3360_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3356_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3357_);
                        v___x_3359_ = v_reuseFailAlloc_3360_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3361_ = lean_array_fget_borrowed(v_ks_3349_, v_x_3346_);
                    v___x_3362_ = l_Lean_instBEqMVarId_beq(v_x_3347_, v_k_x27_3361_);
                    if v___x_3362_ == 0 {
                        if v_isShared_3353_ == 0 {
                            v___x_3364_ = v___x_3352_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3368_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_ks_3349_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_vs_3350_);
                            v___x_3364_ = v_reuseFailAlloc_3368_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3369_ = lean_array_fset(v_ks_3349_, v_x_3346_, v_x_3347_);
                        v___x_3370_ = lean_array_fset(v_vs_3350_, v_x_3346_, v_x_3348_);
                        leanh::lean_dec(v_x_3346_);
                        if v_isShared_3353_ == 0 {
                            leanh::lean_ctor_set(v___x_3352_, 1, v___x_3370_);
                            leanh::lean_ctor_set(v___x_3352_, 0, v___x_3369_);
                            v___x_3372_ = v___x_3352_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3373_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3369_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3370_);
                            v___x_3372_ = v_reuseFailAlloc_3373_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3359_;
            }
            3 => {
                v___x_3365_ = leanh::lean_unsigned_to_nat(1);
                v___x_3366_ = lean_nat_add(v_x_3346_, v___x_3365_);
                leanh::lean_dec(v_x_3346_);
                v_x_3345_ = v___x_3364_;
                v_x_3346_ = v___x_3366_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(
    mut v_n_3375_: *mut leanh::LeanObject,
    mut v_k_3376_: *mut leanh::LeanObject,
    mut v_v_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = leanh::lean_unsigned_to_nat(0);
    v___x_3379_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_3375_, v___x_3378_, v_k_3376_, v_v_3377_);
    return v___x_3379_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0()
-> usize {
    let mut v___x_3380_: usize = 0;
    let mut v___x_3381_: usize = 0;
    let mut v___x_3382_: usize = 0;
    v___x_3380_ = 5usize;
    v___x_3381_ = 1usize;
    v___x_3382_ = lean_usize_shift_left(v___x_3381_, v___x_3380_);
    return v___x_3382_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1()
-> usize {
    let mut v___x_3383_: usize = 0;
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    v___x_3383_ = 1usize;
    v___x_3384_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
    v___x_3385_ = lean_usize_sub(v___x_3384_, v___x_3383_);
    return v___x_3385_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3386_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3386_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(
    mut v_x_3387_: *mut leanh::LeanObject,
    mut v_x_3388_: usize,
    mut v_x_3389_: usize,
    mut v_x_3390_: *mut leanh::LeanObject,
    mut v_x_3391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: usize = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: usize = 0;
    let mut v___x_3396_: usize = 0;
    let mut v_j_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v_v_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_node_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_unused_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: u8 = 0;
    let mut v_ks_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: usize = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: u8 = 0;
    let mut v_reuseFailAlloc_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3387_) == 0 {
                    v_es_3392_ = leanh::lean_ctor_get(v_x_3387_, 0);
                    v___x_3393_ = 5usize;
                    v___x_3394_ = 1usize;
                    v___x_3395_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1);
                    v___x_3396_ = lean_usize_land(v_x_3388_, v___x_3395_);
                    v_j_3397_ = lean_usize_to_nat(v___x_3396_);
                    v___x_3398_ = lean_array_get_size(v_es_3392_);
                    v___x_3399_ = lean_nat_dec_lt(v_j_3397_, v___x_3398_);
                    if v___x_3399_ == 0 {
                        leanh::lean_dec(v_j_3397_);
                        leanh::lean_dec(v_x_3391_);
                        leanh::lean_dec(v_x_3390_);
                        return v_x_3387_;
                    } else {
                        leanh::lean_inc_ref(v_es_3392_);
                        v_isSharedCheck_3436_ = (!leanh::lean_is_exclusive(v_x_3387_)) as u8;
                        if v_isSharedCheck_3436_ == 0 {
                            v_unused_3437_ = leanh::lean_ctor_get(v_x_3387_, 0);
                            leanh::lean_dec(v_unused_3437_);
                            v___x_3401_ = v_x_3387_;
                            v_isShared_3402_ = v_isSharedCheck_3436_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3387_);
                            v___x_3401_ = leanh::lean_box(0);
                            v_isShared_3402_ = v_isSharedCheck_3436_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3438_ = leanh::lean_ctor_get(v_x_3387_, 0);
                    v_vs_3439_ = leanh::lean_ctor_get(v_x_3387_, 1);
                    v_isSharedCheck_3459_ = (!leanh::lean_is_exclusive(v_x_3387_)) as u8;
                    if v_isSharedCheck_3459_ == 0 {
                        v___x_3441_ = v_x_3387_;
                        v_isShared_3442_ = v_isSharedCheck_3459_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3439_);
                        leanh::lean_inc(v_ks_3438_);
                        leanh::lean_dec(v_x_3387_);
                        v___x_3441_ = leanh::lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3459_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3403_ = lean_array_fget(v_es_3392_, v_j_3397_);
                v___x_3404_ = leanh::lean_box(0);
                v_xs_x27_3405_ = lean_array_fset(v_es_3392_, v_j_3397_, v___x_3404_);
                match leanh::lean_obj_tag(v_v_3403_) {
                    0 => {
                        v_key_3412_ = leanh::lean_ctor_get(v_v_3403_, 0);
                        v_val_3413_ = leanh::lean_ctor_get(v_v_3403_, 1);
                        v_isSharedCheck_3423_ = (!leanh::lean_is_exclusive(v_v_3403_)) as u8;
                        if v_isSharedCheck_3423_ == 0 {
                            v___x_3415_ = v_v_3403_;
                            v_isShared_3416_ = v_isSharedCheck_3423_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3413_);
                            leanh::lean_inc(v_key_3412_);
                            leanh::lean_dec(v_v_3403_);
                            v___x_3415_ = leanh::lean_box(0);
                            v_isShared_3416_ = v_isSharedCheck_3423_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3424_ = leanh::lean_ctor_get(v_v_3403_, 0);
                        v_isSharedCheck_3434_ = (!leanh::lean_is_exclusive(v_v_3403_)) as u8;
                        if v_isSharedCheck_3434_ == 0 {
                            v___x_3426_ = v_v_3403_;
                            v_isShared_3427_ = v_isSharedCheck_3434_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3424_);
                            leanh::lean_dec(v_v_3403_);
                            v___x_3426_ = leanh::lean_box(0);
                            v_isShared_3427_ = v_isSharedCheck_3434_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3435_, 0, v_x_3390_);
                        leanh::lean_ctor_set(v___x_3435_, 1, v_x_3391_);
                        v___y_3407_ = v___x_3435_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3408_ = lean_array_fset(v_xs_x27_3405_, v_j_3397_, v___y_3407_);
                leanh::lean_dec(v_j_3397_);
                if v_isShared_3402_ == 0 {
                    leanh::lean_ctor_set(v___x_3401_, 0, v___x_3408_);
                    v___x_3410_ = v___x_3401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
                    v___x_3410_ = v_reuseFailAlloc_3411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3410_;
            }
            4 => {
                v___x_3417_ = l_Lean_instBEqMVarId_beq(v_x_3390_, v_key_3412_);
                if v___x_3417_ == 0 {
                    leanh::lean_del_object(v___x_3415_);
                    v___x_3418_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3412_,
                        v_val_3413_,
                        v_x_3390_,
                        v_x_3391_,
                    );
                    v___x_3419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3419_, 0, v___x_3418_);
                    v___y_3407_ = v___x_3419_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3413_);
                    leanh::lean_dec(v_key_3412_);
                    if v_isShared_3416_ == 0 {
                        leanh::lean_ctor_set(v___x_3415_, 1, v_x_3391_);
                        leanh::lean_ctor_set(v___x_3415_, 0, v_x_3390_);
                        v___x_3421_ = v___x_3415_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_x_3390_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_x_3391_);
                        v___x_3421_ = v_reuseFailAlloc_3422_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3407_ = v___x_3421_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3428_ = lean_usize_shift_right(v_x_3388_, v___x_3393_);
                v___x_3429_ = lean_usize_add(v_x_3389_, v___x_3394_);
                v___x_3430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_3424_, v___x_3428_, v___x_3429_, v_x_3390_, v_x_3391_);
                if v_isShared_3427_ == 0 {
                    leanh::lean_ctor_set(v___x_3426_, 0, v___x_3430_);
                    v___x_3432_ = v___x_3426_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
                    v___x_3432_ = v_reuseFailAlloc_3433_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3407_ = v___x_3432_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3442_ == 0 {
                    v___x_3444_ = v___x_3441_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_ks_3438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_vs_3439_);
                    v___x_3444_ = v_reuseFailAlloc_3458_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_3444_, v_x_3390_, v_x_3391_);
                v___x_3453_ = 7usize;
                v___x_3454_ = lean_usize_dec_le(v___x_3453_, v_x_3389_);
                if v___x_3454_ == 0 {
                    v___x_3455_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3445_);
                    v___x_3456_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3457_ = lean_nat_dec_lt(v___x_3455_, v___x_3456_);
                    leanh::lean_dec(v___x_3455_);
                    v___y_3447_ = v___x_3457_;
                    state = 10;
                    continue;
                } else {
                    v___y_3447_ = v___x_3454_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3447_ == 0 {
                    v_ks_3448_ = leanh::lean_ctor_get(v_newNode_3445_, 0);
                    leanh::lean_inc_ref(v_ks_3448_);
                    v_vs_3449_ = leanh::lean_ctor_get(v_newNode_3445_, 1);
                    leanh::lean_inc_ref(v_vs_3449_);
                    leanh::lean_dec_ref(v_newNode_3445_);
                    v___x_3450_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3451_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2);
                    v___x_3452_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_3389_, v_ks_3448_, v_vs_3449_, v___x_3450_, v___x_3451_);
                    leanh::lean_dec_ref(v_vs_3449_);
                    leanh::lean_dec_ref(v_ks_3448_);
                    return v___x_3452_;
                } else {
                    return v_newNode_3445_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(
    mut v_depth_3460_: usize,
    mut v_keys_3461_: *mut leanh::LeanObject,
    mut v_vals_3462_: *mut leanh::LeanObject,
    mut v_i_3463_: *mut leanh::LeanObject,
    mut v_entries_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: u8 = 0;
    let mut v_k_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u64 = 0;
    let mut v_h_3470_: usize = 0;
    let mut v___x_3471_: usize = 0;
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: usize = 0;
    let mut v___x_3475_: usize = 0;
    let mut v_h_3476_: usize = 0;
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3465_ = lean_array_get_size(v_keys_3461_);
                v___x_3466_ = lean_nat_dec_lt(v_i_3463_, v___x_3465_);
                if v___x_3466_ == 0 {
                    leanh::lean_dec(v_i_3463_);
                    return v_entries_3464_;
                } else {
                    v_k_3467_ = lean_array_fget_borrowed(v_keys_3461_, v_i_3463_);
                    v_v_3468_ = lean_array_fget_borrowed(v_vals_3462_, v_i_3463_);
                    v___x_3469_ = l_Lean_instHashableMVarId_hash(v_k_3467_);
                    v_h_3470_ = lean_uint64_to_usize(v___x_3469_);
                    v___x_3471_ = 5usize;
                    v___x_3472_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3473_ = 1usize;
                    v___x_3474_ = lean_usize_sub(v_depth_3460_, v___x_3473_);
                    v___x_3475_ = lean_usize_mul(v___x_3471_, v___x_3474_);
                    v_h_3476_ = lean_usize_shift_right(v_h_3470_, v___x_3475_);
                    v___x_3477_ = lean_nat_add(v_i_3463_, v___x_3472_);
                    leanh::lean_dec(v_i_3463_);
                    leanh::lean_inc(v_v_3468_);
                    leanh::lean_inc(v_k_3467_);
                    v___x_3478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_3464_, v_h_3476_, v_depth_3460_, v_k_3467_, v_v_3468_);
                    v_i_3463_ = v___x_3477_;
                    v_entries_3464_ = v___x_3478_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(
    mut v_depth_3480_: *mut leanh::LeanObject,
    mut v_keys_3481_: *mut leanh::LeanObject,
    mut v_vals_3482_: *mut leanh::LeanObject,
    mut v_i_3483_: *mut leanh::LeanObject,
    mut v_entries_3484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3485_: usize = 0;
    let mut v_res_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3485_ = leanh::lean_unbox_usize(v_depth_3480_);
    leanh::lean_dec(v_depth_3480_);
    v_res_3486_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_3485_, v_keys_3481_, v_vals_3482_, v_i_3483_, v_entries_3484_);
    leanh::lean_dec_ref(v_vals_3482_);
    leanh::lean_dec_ref(v_keys_3481_);
    return v_res_3486_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(
    mut v_x_3487_: *mut leanh::LeanObject,
    mut v_x_3488_: *mut leanh::LeanObject,
    mut v_x_3489_: *mut leanh::LeanObject,
    mut v_x_3490_: *mut leanh::LeanObject,
    mut v_x_3491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7488__boxed_3492_: usize = 0;
    let mut v_x_7489__boxed_3493_: usize = 0;
    let mut v_res_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7488__boxed_3492_ = leanh::lean_unbox_usize(v_x_3488_);
    leanh::lean_dec(v_x_3488_);
    v_x_7489__boxed_3493_ = leanh::lean_unbox_usize(v_x_3489_);
    leanh::lean_dec(v_x_3489_);
    v_res_3494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_3487_, v_x_7488__boxed_3492_, v_x_7489__boxed_3493_, v_x_3490_, v_x_3491_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(
    mut v_x_3495_: *mut leanh::LeanObject,
    mut v_x_3496_: *mut leanh::LeanObject,
    mut v_x_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3498_: u64 = 0;
    let mut v___x_3499_: usize = 0;
    let mut v___x_3500_: usize = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = l_Lean_instHashableMVarId_hash(v_x_3496_);
    v___x_3499_ = lean_uint64_to_usize(v___x_3498_);
    v___x_3500_ = 1usize;
    v___x_3501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_3495_, v___x_3499_, v___x_3500_, v_x_3496_, v_x_3497_);
    return v___x_3501_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(
    mut v_mvarId_3502_: *mut leanh::LeanObject,
    mut v_val_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v_depth_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3538_: u8 = 0;
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3506_ = lean_st_ref_take(v___y_3504_);
                v_mctx_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                v_cache_3508_ = leanh::lean_ctor_get(v___x_3506_, 1);
                v_zetaDeltaFVarIds_3509_ = leanh::lean_ctor_get(v___x_3506_, 2);
                v_postponed_3510_ = leanh::lean_ctor_get(v___x_3506_, 3);
                v_diag_3511_ = leanh::lean_ctor_get(v___x_3506_, 4);
                v_isSharedCheck_3539_ = (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                if v_isSharedCheck_3539_ == 0 {
                    v___x_3513_ = v___x_3506_;
                    v_isShared_3514_ = v_isSharedCheck_3539_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3511_);
                    leanh::lean_inc(v_postponed_3510_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3509_);
                    leanh::lean_inc(v_cache_3508_);
                    leanh::lean_inc(v_mctx_3507_);
                    leanh::lean_dec(v___x_3506_);
                    v___x_3513_ = leanh::lean_box(0);
                    v_isShared_3514_ = v_isSharedCheck_3539_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3515_ = leanh::lean_ctor_get(v_mctx_3507_, 0);
                v_levelAssignDepth_3516_ = leanh::lean_ctor_get(v_mctx_3507_, 1);
                v_lmvarCounter_3517_ = leanh::lean_ctor_get(v_mctx_3507_, 2);
                v_mvarCounter_3518_ = leanh::lean_ctor_get(v_mctx_3507_, 3);
                v_lDecls_3519_ = leanh::lean_ctor_get(v_mctx_3507_, 4);
                v_decls_3520_ = leanh::lean_ctor_get(v_mctx_3507_, 5);
                v_userNames_3521_ = leanh::lean_ctor_get(v_mctx_3507_, 6);
                v_lAssignment_3522_ = leanh::lean_ctor_get(v_mctx_3507_, 7);
                v_eAssignment_3523_ = leanh::lean_ctor_get(v_mctx_3507_, 8);
                v_dAssignment_3524_ = leanh::lean_ctor_get(v_mctx_3507_, 9);
                v_isSharedCheck_3538_ = (!leanh::lean_is_exclusive(v_mctx_3507_)) as u8;
                if v_isSharedCheck_3538_ == 0 {
                    v___x_3526_ = v_mctx_3507_;
                    v_isShared_3527_ = v_isSharedCheck_3538_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3524_);
                    leanh::lean_inc(v_eAssignment_3523_);
                    leanh::lean_inc(v_lAssignment_3522_);
                    leanh::lean_inc(v_userNames_3521_);
                    leanh::lean_inc(v_decls_3520_);
                    leanh::lean_inc(v_lDecls_3519_);
                    leanh::lean_inc(v_mvarCounter_3518_);
                    leanh::lean_inc(v_lmvarCounter_3517_);
                    leanh::lean_inc(v_levelAssignDepth_3516_);
                    leanh::lean_inc(v_depth_3515_);
                    leanh::lean_dec(v_mctx_3507_);
                    v___x_3526_ = leanh::lean_box(0);
                    v_isShared_3527_ = v_isSharedCheck_3538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3528_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_3523_, v_mvarId_3502_, v_val_3503_);
                if v_isShared_3527_ == 0 {
                    leanh::lean_ctor_set(v___x_3526_, 8, v___x_3528_);
                    v___x_3530_ = v___x_3526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3537_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_depth_3515_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3537_,
                        1,
                        v_levelAssignDepth_3516_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_lmvarCounter_3517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_mvarCounter_3518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_lDecls_3519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 5, v_decls_3520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 6, v_userNames_3521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 7, v_lAssignment_3522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 8, v___x_3528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 9, v_dAssignment_3524_);
                    v___x_3530_ = v_reuseFailAlloc_3537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3514_ == 0 {
                    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_cache_3508_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3536_,
                        2,
                        v_zetaDeltaFVarIds_3509_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 3, v_postponed_3510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_diag_3511_);
                    v___x_3532_ = v_reuseFailAlloc_3536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3533_ = lean_st_ref_set(v___y_3504_, v___x_3532_);
                v___x_3534_ = leanh::lean_box(0);
                v___x_3535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3535_, 0, v___x_3534_);
                return v___x_3535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(
    mut v_mvarId_3540_: *mut leanh::LeanObject,
    mut v_val_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3544_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_3540_, v_val_3541_, v___y_3542_);
    leanh::lean_dec(v___y_3542_);
    return v_res_3544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(
    mut v_a_3545_: *mut leanh::LeanObject,
    mut v_as_3546_: *mut leanh::LeanObject,
    mut v_sz_3547_: usize,
    mut v_i_3548_: usize,
    mut v_b_3549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: usize = 0;
    let mut v___x_3563_: usize = 0;
    let mut v_reuseFailAlloc_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_unused_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ = lean_usize_dec_lt(v_i_3548_, v_sz_3547_);
                if v___x_3551_ == 0 {
                    v___x_3552_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3552_, 0, v_b_3549_);
                    return v___x_3552_;
                } else {
                    v_snd_3553_ = leanh::lean_ctor_get(v_b_3549_, 1);
                    v_isSharedCheck_3571_ = (!leanh::lean_is_exclusive(v_b_3549_)) as u8;
                    if v_isSharedCheck_3571_ == 0 {
                        v_unused_3572_ = leanh::lean_ctor_get(v_b_3549_, 0);
                        leanh::lean_dec(v_unused_3572_);
                        v___x_3555_ = v_b_3549_;
                        v_isShared_3556_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3553_);
                        leanh::lean_dec(v_b_3549_);
                        v___x_3555_ = leanh::lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3557_ = leanh::lean_box(0);
                v_a_3566_ = lean_array_uget_borrowed(v_as_3546_, v_i_3548_);
                if leanh::lean_obj_tag(v_a_3566_) == 0 {
                    v_a_3559_ = v_snd_3553_;
                    state = 2;
                    continue;
                } else {
                    v_val_3567_ = leanh::lean_ctor_get(v_a_3566_, 0);
                    v___x_3568_ = l_Lean_LocalDecl_fvarId(v_val_3567_);
                    v___x_3569_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_3568_, v_a_3545_);
                    if v___x_3569_ == 0 {
                        v___x_3570_ = lean_local_ctx_erase(v_snd_3553_, v___x_3568_);
                        v_a_3559_ = v___x_3570_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3568_);
                        v_a_3559_ = v_snd_3553_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3556_ == 0 {
                    leanh::lean_ctor_set(v___x_3555_, 1, v_a_3559_);
                    leanh::lean_ctor_set(v___x_3555_, 0, v___x_3557_);
                    v___x_3561_ = v___x_3555_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_a_3559_);
                    v___x_3561_ = v_reuseFailAlloc_3565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3562_ = 1usize;
                v___x_3563_ = lean_usize_add(v_i_3548_, v___x_3562_);
                v_i_3548_ = v___x_3563_;
                v_b_3549_ = v___x_3561_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(
    mut v_a_3573_: *mut leanh::LeanObject,
    mut v_as_3574_: *mut leanh::LeanObject,
    mut v_sz_3575_: *mut leanh::LeanObject,
    mut v_i_3576_: *mut leanh::LeanObject,
    mut v_b_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3579_: usize = 0;
    let mut v_i_boxed_3580_: usize = 0;
    let mut v_res_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3579_ = leanh::lean_unbox_usize(v_sz_3575_);
    leanh::lean_dec(v_sz_3575_);
    v_i_boxed_3580_ = leanh::lean_unbox_usize(v_i_3576_);
    leanh::lean_dec(v_i_3576_);
    v_res_3581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_3573_, v_as_3574_, v_sz_boxed_3579_, v_i_boxed_3580_, v_b_3577_);
    leanh::lean_dec_ref(v_as_3574_);
    leanh::lean_dec(v_a_3573_);
    return v_res_3581_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_as_3583_: *mut leanh::LeanObject,
    mut v_sz_3584_: usize,
    mut v_i_3585_: usize,
    mut v_b_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3612_: u8 = 0;
    let mut v_unused_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3592_ = lean_usize_dec_lt(v_i_3585_, v_sz_3584_);
                if v___x_3592_ == 0 {
                    v___x_3593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3593_, 0, v_b_3586_);
                    return v___x_3593_;
                } else {
                    v_snd_3594_ = leanh::lean_ctor_get(v_b_3586_, 1);
                    v_isSharedCheck_3612_ = (!leanh::lean_is_exclusive(v_b_3586_)) as u8;
                    if v_isSharedCheck_3612_ == 0 {
                        v_unused_3613_ = leanh::lean_ctor_get(v_b_3586_, 0);
                        leanh::lean_dec(v_unused_3613_);
                        v___x_3596_ = v_b_3586_;
                        v_isShared_3597_ = v_isSharedCheck_3612_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3594_);
                        leanh::lean_dec(v_b_3586_);
                        v___x_3596_ = leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3612_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3598_ = leanh::lean_box(0);
                v_a_3607_ = lean_array_uget_borrowed(v_as_3583_, v_i_3585_);
                if leanh::lean_obj_tag(v_a_3607_) == 0 {
                    v_a_3600_ = v_snd_3594_;
                    state = 2;
                    continue;
                } else {
                    v_val_3608_ = leanh::lean_ctor_get(v_a_3607_, 0);
                    v___x_3609_ = l_Lean_LocalDecl_fvarId(v_val_3608_);
                    v___x_3610_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_3609_, v_a_3582_);
                    if v___x_3610_ == 0 {
                        v___x_3611_ = lean_local_ctx_erase(v_snd_3594_, v___x_3609_);
                        v_a_3600_ = v___x_3611_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3609_);
                        v_a_3600_ = v_snd_3594_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3597_ == 0 {
                    leanh::lean_ctor_set(v___x_3596_, 1, v_a_3600_);
                    leanh::lean_ctor_set(v___x_3596_, 0, v___x_3598_);
                    v___x_3602_ = v___x_3596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3598_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_a_3600_);
                    v___x_3602_ = v_reuseFailAlloc_3606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3603_ = 1usize;
                v___x_3604_ = lean_usize_add(v_i_3585_, v___x_3603_);
                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_3582_, v_as_3583_, v_sz_3584_, v___x_3604_, v___x_3602_);
                return v___x_3605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(
    mut v_a_3614_: *mut leanh::LeanObject,
    mut v_as_3615_: *mut leanh::LeanObject,
    mut v_sz_3616_: *mut leanh::LeanObject,
    mut v_i_3617_: *mut leanh::LeanObject,
    mut v_b_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
    mut v___y_3622_: *mut leanh::LeanObject,
    mut v___y_3623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3624_: usize = 0;
    let mut v_i_boxed_3625_: usize = 0;
    let mut v_res_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3624_ = leanh::lean_unbox_usize(v_sz_3616_);
    leanh::lean_dec(v_sz_3616_);
    v_i_boxed_3625_ = leanh::lean_unbox_usize(v_i_3617_);
    leanh::lean_dec(v_i_3617_);
    v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_3614_, v_as_3615_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
    leanh::lean_dec(v___y_3622_);
    leanh::lean_dec_ref(v___y_3621_);
    leanh::lean_dec(v___y_3620_);
    leanh::lean_dec_ref(v___y_3619_);
    leanh::lean_dec_ref(v_as_3615_);
    leanh::lean_dec(v_a_3614_);
    return v_res_3626_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(
    mut v_init_3627_: *mut leanh::LeanObject,
    mut v_a_3628_: *mut leanh::LeanObject,
    mut v_n_3629_: *mut leanh::LeanObject,
    mut v_b_3630_: *mut leanh::LeanObject,
    mut v___y_3631_: *mut leanh::LeanObject,
    mut v___y_3632_: *mut leanh::LeanObject,
    mut v___y_3633_: *mut leanh::LeanObject,
    mut v___y_3634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3639_: usize = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3645_: u8 = 0;
    let mut v_fst_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut v_a_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v_vs_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3668_: usize = 0;
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v_fst_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_a_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_3629_) == 0 {
                    v_cs_3636_ = leanh::lean_ctor_get(v_n_3629_, 0);
                    v___x_3637_ = leanh::lean_box(0);
                    v___x_3638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3638_, 0, v___x_3637_);
                    leanh::lean_ctor_set(v___x_3638_, 1, v_b_3630_);
                    v_sz_3639_ = lean_array_size(v_cs_3636_);
                    v___x_3640_ = 0usize;
                    v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_3627_, v_a_3628_, v_cs_3636_, v_sz_3639_, v___x_3640_, v___x_3638_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
                    if leanh::lean_obj_tag(v___x_3641_) == 0 {
                        v_a_3642_ = leanh::lean_ctor_get(v___x_3641_, 0);
                        v_isSharedCheck_3656_ =
                            (!leanh::lean_is_exclusive(v___x_3641_)) as u8;
                        if v_isSharedCheck_3656_ == 0 {
                            v___x_3644_ = v___x_3641_;
                            v_isShared_3645_ = v_isSharedCheck_3656_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3642_);
                            leanh::lean_dec(v___x_3641_);
                            v___x_3644_ = leanh::lean_box(0);
                            v_isShared_3645_ = v_isSharedCheck_3656_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3657_ = leanh::lean_ctor_get(v___x_3641_, 0);
                        v_isSharedCheck_3664_ =
                            (!leanh::lean_is_exclusive(v___x_3641_)) as u8;
                        if v_isSharedCheck_3664_ == 0 {
                            v___x_3659_ = v___x_3641_;
                            v_isShared_3660_ = v_isSharedCheck_3664_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3657_);
                            leanh::lean_dec(v___x_3641_);
                            v___x_3659_ = leanh::lean_box(0);
                            v_isShared_3660_ = v_isSharedCheck_3664_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3665_ = leanh::lean_ctor_get(v_n_3629_, 0);
                    v___x_3666_ = leanh::lean_box(0);
                    v___x_3667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3667_, 0, v___x_3666_);
                    leanh::lean_ctor_set(v___x_3667_, 1, v_b_3630_);
                    v_sz_3668_ = lean_array_size(v_vs_3665_);
                    v___x_3669_ = 0usize;
                    v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_3628_, v_vs_3665_, v_sz_3668_, v___x_3669_, v___x_3667_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
                    if leanh::lean_obj_tag(v___x_3670_) == 0 {
                        v_a_3671_ = leanh::lean_ctor_get(v___x_3670_, 0);
                        v_isSharedCheck_3685_ =
                            (!leanh::lean_is_exclusive(v___x_3670_)) as u8;
                        if v_isSharedCheck_3685_ == 0 {
                            v___x_3673_ = v___x_3670_;
                            v_isShared_3674_ = v_isSharedCheck_3685_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3671_);
                            leanh::lean_dec(v___x_3670_);
                            v___x_3673_ = leanh::lean_box(0);
                            v_isShared_3674_ = v_isSharedCheck_3685_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3686_ = leanh::lean_ctor_get(v___x_3670_, 0);
                        v_isSharedCheck_3693_ =
                            (!leanh::lean_is_exclusive(v___x_3670_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3670_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3686_);
                            leanh::lean_dec(v___x_3670_);
                            v___x_3688_ = leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3646_ = leanh::lean_ctor_get(v_a_3642_, 0);
                if leanh::lean_obj_tag(v_fst_3646_) == 0 {
                    v_snd_3647_ = leanh::lean_ctor_get(v_a_3642_, 1);
                    leanh::lean_inc(v_snd_3647_);
                    leanh::lean_dec(v_a_3642_);
                    v___x_3648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3648_, 0, v_snd_3647_);
                    if v_isShared_3645_ == 0 {
                        leanh::lean_ctor_set(v___x_3644_, 0, v___x_3648_);
                        v___x_3650_ = v___x_3644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3651_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
                        v___x_3650_ = v_reuseFailAlloc_3651_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3646_);
                    leanh::lean_dec(v_a_3642_);
                    v_val_3652_ = leanh::lean_ctor_get(v_fst_3646_, 0);
                    leanh::lean_inc(v_val_3652_);
                    leanh::lean_dec_ref_known(v_fst_3646_, 1);
                    if v_isShared_3645_ == 0 {
                        leanh::lean_ctor_set(v___x_3644_, 0, v_val_3652_);
                        v___x_3654_ = v___x_3644_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_val_3652_);
                        v___x_3654_ = v_reuseFailAlloc_3655_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3650_;
            }
            3 => {
                return v___x_3654_;
            }
            4 => {
                if v_isShared_3660_ == 0 {
                    v___x_3662_ = v___x_3659_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3662_;
            }
            6 => {
                v_fst_3675_ = leanh::lean_ctor_get(v_a_3671_, 0);
                if leanh::lean_obj_tag(v_fst_3675_) == 0 {
                    v_snd_3676_ = leanh::lean_ctor_get(v_a_3671_, 1);
                    leanh::lean_inc(v_snd_3676_);
                    leanh::lean_dec(v_a_3671_);
                    v___x_3677_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3677_, 0, v_snd_3676_);
                    if v_isShared_3674_ == 0 {
                        leanh::lean_ctor_set(v___x_3673_, 0, v___x_3677_);
                        v___x_3679_ = v___x_3673_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
                        v___x_3679_ = v_reuseFailAlloc_3680_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3675_);
                    leanh::lean_dec(v_a_3671_);
                    v_val_3681_ = leanh::lean_ctor_get(v_fst_3675_, 0);
                    leanh::lean_inc(v_val_3681_);
                    leanh::lean_dec_ref_known(v_fst_3675_, 1);
                    if v_isShared_3674_ == 0 {
                        leanh::lean_ctor_set(v___x_3673_, 0, v_val_3681_);
                        v___x_3683_ = v___x_3673_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_val_3681_);
                        v___x_3683_ = v_reuseFailAlloc_3684_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3679_;
            }
            8 => {
                return v___x_3683_;
            }
            9 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(
    mut v_init_3694_: *mut leanh::LeanObject,
    mut v_a_3695_: *mut leanh::LeanObject,
    mut v_as_3696_: *mut leanh::LeanObject,
    mut v_sz_3697_: usize,
    mut v_i_3698_: usize,
    mut v_b_3699_: *mut leanh::LeanObject,
    mut v___y_3700_: *mut leanh::LeanObject,
    mut v___y_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3705_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v_a_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: usize = 0;
    let mut v___x_3729_: usize = 0;
    let mut v_reuseFailAlloc_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut v_a_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_unused_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3705_ = lean_usize_dec_lt(v_i_3698_, v_sz_3697_);
                if v___x_3705_ == 0 {
                    v___x_3706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3706_, 0, v_b_3699_);
                    return v___x_3706_;
                } else {
                    v_snd_3707_ = leanh::lean_ctor_get(v_b_3699_, 1);
                    v_isSharedCheck_3741_ = (!leanh::lean_is_exclusive(v_b_3699_)) as u8;
                    if v_isSharedCheck_3741_ == 0 {
                        v_unused_3742_ = leanh::lean_ctor_get(v_b_3699_, 0);
                        leanh::lean_dec(v_unused_3742_);
                        v___x_3709_ = v_b_3699_;
                        v_isShared_3710_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3707_);
                        leanh::lean_dec(v_b_3699_);
                        v___x_3709_ = leanh::lean_box(0);
                        v_isShared_3710_ = v_isSharedCheck_3741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3711_ = lean_array_uget_borrowed(v_as_3696_, v_i_3698_);
                leanh::lean_inc(v_snd_3707_);
                v___x_3712_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_3694_, v_a_3695_, v_a_3711_, v_snd_3707_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
                if leanh::lean_obj_tag(v___x_3712_) == 0 {
                    v_a_3713_ = leanh::lean_ctor_get(v___x_3712_, 0);
                    v_isSharedCheck_3732_ = (!leanh::lean_is_exclusive(v___x_3712_)) as u8;
                    if v_isSharedCheck_3732_ == 0 {
                        v___x_3715_ = v___x_3712_;
                        v_isShared_3716_ = v_isSharedCheck_3732_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3713_);
                        leanh::lean_dec(v___x_3712_);
                        v___x_3715_ = leanh::lean_box(0);
                        v_isShared_3716_ = v_isSharedCheck_3732_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3709_);
                    leanh::lean_dec(v_snd_3707_);
                    v_a_3733_ = leanh::lean_ctor_get(v___x_3712_, 0);
                    v_isSharedCheck_3740_ = (!leanh::lean_is_exclusive(v___x_3712_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3735_ = v___x_3712_;
                        v_isShared_3736_ = v_isSharedCheck_3740_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3733_);
                        leanh::lean_dec(v___x_3712_);
                        v___x_3735_ = leanh::lean_box(0);
                        v_isShared_3736_ = v_isSharedCheck_3740_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3713_) == 0 {
                    v___x_3717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3717_, 0, v_a_3713_);
                    if v_isShared_3710_ == 0 {
                        leanh::lean_ctor_set(v___x_3709_, 0, v___x_3717_);
                        v___x_3719_ = v___x_3709_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3717_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_snd_3707_);
                        v___x_3719_ = v_reuseFailAlloc_3723_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3715_);
                    leanh::lean_dec(v_snd_3707_);
                    v_a_3724_ = leanh::lean_ctor_get(v_a_3713_, 0);
                    leanh::lean_inc(v_a_3724_);
                    leanh::lean_dec_ref_known(v_a_3713_, 1);
                    v___x_3725_ = leanh::lean_box(0);
                    if v_isShared_3710_ == 0 {
                        leanh::lean_ctor_set(v___x_3709_, 1, v_a_3724_);
                        leanh::lean_ctor_set(v___x_3709_, 0, v___x_3725_);
                        v___x_3727_ = v___x_3709_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_a_3724_);
                        v___x_3727_ = v_reuseFailAlloc_3731_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3716_ == 0 {
                    leanh::lean_ctor_set(v___x_3715_, 0, v___x_3719_);
                    v___x_3721_ = v___x_3715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
                    v___x_3721_ = v_reuseFailAlloc_3722_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3721_;
            }
            5 => {
                v___x_3728_ = 1usize;
                v___x_3729_ = lean_usize_add(v_i_3698_, v___x_3728_);
                v_i_3698_ = v___x_3729_;
                v_b_3699_ = v___x_3727_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3736_ == 0 {
                    v___x_3738_ = v___x_3735_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
                    v___x_3738_ = v_reuseFailAlloc_3739_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(
    mut v_init_3743_: *mut leanh::LeanObject,
    mut v_a_3744_: *mut leanh::LeanObject,
    mut v_as_3745_: *mut leanh::LeanObject,
    mut v_sz_3746_: *mut leanh::LeanObject,
    mut v_i_3747_: *mut leanh::LeanObject,
    mut v_b_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3754_: usize = 0;
    let mut v_i_boxed_3755_: usize = 0;
    let mut v_res_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3754_ = leanh::lean_unbox_usize(v_sz_3746_);
    leanh::lean_dec(v_sz_3746_);
    v_i_boxed_3755_ = leanh::lean_unbox_usize(v_i_3747_);
    leanh::lean_dec(v_i_3747_);
    v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_3743_, v_a_3744_, v_as_3745_, v_sz_boxed_3754_, v_i_boxed_3755_, v_b_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
    leanh::lean_dec(v___y_3752_);
    leanh::lean_dec_ref(v___y_3751_);
    leanh::lean_dec(v___y_3750_);
    leanh::lean_dec_ref(v___y_3749_);
    leanh::lean_dec_ref(v_as_3745_);
    leanh::lean_dec(v_a_3744_);
    leanh::lean_dec_ref(v_init_3743_);
    return v_res_3756_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(
    mut v_init_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_n_3759_: *mut leanh::LeanObject,
    mut v_b_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
    mut v___y_3765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_3757_, v_a_3758_, v_n_3759_, v_b_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
    leanh::lean_dec(v___y_3764_);
    leanh::lean_dec_ref(v___y_3763_);
    leanh::lean_dec(v___y_3762_);
    leanh::lean_dec_ref(v___y_3761_);
    leanh::lean_dec_ref(v_n_3759_);
    leanh::lean_dec(v_a_3758_);
    leanh::lean_dec_ref(v_init_3757_);
    return v_res_3766_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(
    mut v_a_3767_: *mut leanh::LeanObject,
    mut v_as_3768_: *mut leanh::LeanObject,
    mut v_sz_3769_: usize,
    mut v_i_3770_: usize,
    mut v_b_3771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3773_: u8 = 0;
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: usize = 0;
    let mut v___x_3785_: usize = 0;
    let mut v_reuseFailAlloc_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_unused_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3773_ = lean_usize_dec_lt(v_i_3770_, v_sz_3769_);
                if v___x_3773_ == 0 {
                    v___x_3774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3774_, 0, v_b_3771_);
                    return v___x_3774_;
                } else {
                    v_snd_3775_ = leanh::lean_ctor_get(v_b_3771_, 1);
                    v_isSharedCheck_3793_ = (!leanh::lean_is_exclusive(v_b_3771_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v_unused_3794_ = leanh::lean_ctor_get(v_b_3771_, 0);
                        leanh::lean_dec(v_unused_3794_);
                        v___x_3777_ = v_b_3771_;
                        v_isShared_3778_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3775_);
                        leanh::lean_dec(v_b_3771_);
                        v___x_3777_ = leanh::lean_box(0);
                        v_isShared_3778_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3779_ = leanh::lean_box(0);
                v_a_3788_ = lean_array_uget_borrowed(v_as_3768_, v_i_3770_);
                if leanh::lean_obj_tag(v_a_3788_) == 0 {
                    v_a_3781_ = v_snd_3775_;
                    state = 2;
                    continue;
                } else {
                    v_val_3789_ = leanh::lean_ctor_get(v_a_3788_, 0);
                    v___x_3790_ = l_Lean_LocalDecl_fvarId(v_val_3789_);
                    v___x_3791_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_3790_, v_a_3767_);
                    if v___x_3791_ == 0 {
                        v___x_3792_ = lean_local_ctx_erase(v_snd_3775_, v___x_3790_);
                        v_a_3781_ = v___x_3792_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3790_);
                        v_a_3781_ = v_snd_3775_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3778_ == 0 {
                    leanh::lean_ctor_set(v___x_3777_, 1, v_a_3781_);
                    leanh::lean_ctor_set(v___x_3777_, 0, v___x_3779_);
                    v___x_3783_ = v___x_3777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_a_3781_);
                    v___x_3783_ = v_reuseFailAlloc_3787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3784_ = 1usize;
                v___x_3785_ = lean_usize_add(v_i_3770_, v___x_3784_);
                v_i_3770_ = v___x_3785_;
                v_b_3771_ = v___x_3783_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_as_3796_: *mut leanh::LeanObject,
    mut v_sz_3797_: *mut leanh::LeanObject,
    mut v_i_3798_: *mut leanh::LeanObject,
    mut v_b_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3801_: usize = 0;
    let mut v_i_boxed_3802_: usize = 0;
    let mut v_res_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3801_ = leanh::lean_unbox_usize(v_sz_3797_);
    leanh::lean_dec(v_sz_3797_);
    v_i_boxed_3802_ = leanh::lean_unbox_usize(v_i_3798_);
    leanh::lean_dec(v_i_3798_);
    v_res_3803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_3795_, v_as_3796_, v_sz_boxed_3801_, v_i_boxed_3802_, v_b_3799_);
    leanh::lean_dec_ref(v_as_3796_);
    leanh::lean_dec(v_a_3795_);
    return v_res_3803_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(
    mut v_a_3804_: *mut leanh::LeanObject,
    mut v_as_3805_: *mut leanh::LeanObject,
    mut v_sz_3806_: usize,
    mut v_i_3807_: usize,
    mut v_b_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: usize = 0;
    let mut v___x_3826_: usize = 0;
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_unused_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3814_ = lean_usize_dec_lt(v_i_3807_, v_sz_3806_);
                if v___x_3814_ == 0 {
                    v___x_3815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3815_, 0, v_b_3808_);
                    return v___x_3815_;
                } else {
                    v_snd_3816_ = leanh::lean_ctor_get(v_b_3808_, 1);
                    v_isSharedCheck_3834_ = (!leanh::lean_is_exclusive(v_b_3808_)) as u8;
                    if v_isSharedCheck_3834_ == 0 {
                        v_unused_3835_ = leanh::lean_ctor_get(v_b_3808_, 0);
                        leanh::lean_dec(v_unused_3835_);
                        v___x_3818_ = v_b_3808_;
                        v_isShared_3819_ = v_isSharedCheck_3834_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3816_);
                        leanh::lean_dec(v_b_3808_);
                        v___x_3818_ = leanh::lean_box(0);
                        v_isShared_3819_ = v_isSharedCheck_3834_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3820_ = leanh::lean_box(0);
                v_a_3829_ = lean_array_uget_borrowed(v_as_3805_, v_i_3807_);
                if leanh::lean_obj_tag(v_a_3829_) == 0 {
                    v_a_3822_ = v_snd_3816_;
                    state = 2;
                    continue;
                } else {
                    v_val_3830_ = leanh::lean_ctor_get(v_a_3829_, 0);
                    v___x_3831_ = l_Lean_LocalDecl_fvarId(v_val_3830_);
                    v___x_3832_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_3831_, v_a_3804_);
                    if v___x_3832_ == 0 {
                        v___x_3833_ = lean_local_ctx_erase(v_snd_3816_, v___x_3831_);
                        v_a_3822_ = v___x_3833_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3831_);
                        v_a_3822_ = v_snd_3816_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3819_ == 0 {
                    leanh::lean_ctor_set(v___x_3818_, 1, v_a_3822_);
                    leanh::lean_ctor_set(v___x_3818_, 0, v___x_3820_);
                    v___x_3824_ = v___x_3818_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_a_3822_);
                    v___x_3824_ = v_reuseFailAlloc_3828_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3825_ = 1usize;
                v___x_3826_ = lean_usize_add(v_i_3807_, v___x_3825_);
                v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_3804_, v_as_3805_, v_sz_3806_, v___x_3826_, v___x_3824_);
                return v___x_3827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_as_3837_: *mut leanh::LeanObject,
    mut v_sz_3838_: *mut leanh::LeanObject,
    mut v_i_3839_: *mut leanh::LeanObject,
    mut v_b_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3846_: usize = 0;
    let mut v_i_boxed_3847_: usize = 0;
    let mut v_res_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3846_ = leanh::lean_unbox_usize(v_sz_3838_);
    leanh::lean_dec(v_sz_3838_);
    v_i_boxed_3847_ = leanh::lean_unbox_usize(v_i_3839_);
    leanh::lean_dec(v_i_3839_);
    v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_3836_, v_as_3837_, v_sz_boxed_3846_, v_i_boxed_3847_, v_b_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
    leanh::lean_dec(v___y_3844_);
    leanh::lean_dec_ref(v___y_3843_);
    leanh::lean_dec(v___y_3842_);
    leanh::lean_dec_ref(v___y_3841_);
    leanh::lean_dec_ref(v_as_3837_);
    leanh::lean_dec(v_a_3836_);
    return v_res_3848_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_t_3850_: *mut leanh::LeanObject,
    mut v_init_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
    mut v___y_3853_: *mut leanh::LeanObject,
    mut v___y_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3863_: u8 = 0;
    let mut v_a_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3871_: usize = 0;
    let mut v___x_3872_: usize = 0;
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3877_: u8 = 0;
    let mut v_fst_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_a_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3857_ = leanh::lean_ctor_get(v_t_3850_, 0);
                v_tail_3858_ = leanh::lean_ctor_get(v_t_3850_, 1);
                leanh::lean_inc_ref(v_init_3851_);
                v___x_3859_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_3851_, v_a_3849_, v_root_3857_, v_init_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
                leanh::lean_dec_ref(v_init_3851_);
                if leanh::lean_obj_tag(v___x_3859_) == 0 {
                    v_a_3860_ = leanh::lean_ctor_get(v___x_3859_, 0);
                    v_isSharedCheck_3896_ = (!leanh::lean_is_exclusive(v___x_3859_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3862_ = v___x_3859_;
                        v_isShared_3863_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3860_);
                        leanh::lean_dec(v___x_3859_);
                        v___x_3862_ = leanh::lean_box(0);
                        v_isShared_3863_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3897_ = leanh::lean_ctor_get(v___x_3859_, 0);
                    v_isSharedCheck_3904_ = (!leanh::lean_is_exclusive(v___x_3859_)) as u8;
                    if v_isSharedCheck_3904_ == 0 {
                        v___x_3899_ = v___x_3859_;
                        v_isShared_3900_ = v_isSharedCheck_3904_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3897_);
                        leanh::lean_dec(v___x_3859_);
                        v___x_3899_ = leanh::lean_box(0);
                        v_isShared_3900_ = v_isSharedCheck_3904_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3860_) == 0 {
                    v_a_3864_ = leanh::lean_ctor_get(v_a_3860_, 0);
                    leanh::lean_inc(v_a_3864_);
                    leanh::lean_dec_ref_known(v_a_3860_, 1);
                    if v_isShared_3863_ == 0 {
                        leanh::lean_ctor_set(v___x_3862_, 0, v_a_3864_);
                        v___x_3866_ = v___x_3862_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3864_);
                        v___x_3866_ = v_reuseFailAlloc_3867_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3862_);
                    v_a_3868_ = leanh::lean_ctor_get(v_a_3860_, 0);
                    leanh::lean_inc(v_a_3868_);
                    leanh::lean_dec_ref_known(v_a_3860_, 1);
                    v___x_3869_ = leanh::lean_box(0);
                    v___x_3870_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
                    leanh::lean_ctor_set(v___x_3870_, 1, v_a_3868_);
                    v_sz_3871_ = lean_array_size(v_tail_3858_);
                    v___x_3872_ = 0usize;
                    v___x_3873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_3849_, v_tail_3858_, v_sz_3871_, v___x_3872_, v___x_3870_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
                    if leanh::lean_obj_tag(v___x_3873_) == 0 {
                        v_a_3874_ = leanh::lean_ctor_get(v___x_3873_, 0);
                        v_isSharedCheck_3887_ =
                            (!leanh::lean_is_exclusive(v___x_3873_)) as u8;
                        if v_isSharedCheck_3887_ == 0 {
                            v___x_3876_ = v___x_3873_;
                            v_isShared_3877_ = v_isSharedCheck_3887_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3874_);
                            leanh::lean_dec(v___x_3873_);
                            v___x_3876_ = leanh::lean_box(0);
                            v_isShared_3877_ = v_isSharedCheck_3887_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3888_ = leanh::lean_ctor_get(v___x_3873_, 0);
                        v_isSharedCheck_3895_ =
                            (!leanh::lean_is_exclusive(v___x_3873_)) as u8;
                        if v_isSharedCheck_3895_ == 0 {
                            v___x_3890_ = v___x_3873_;
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3888_);
                            leanh::lean_dec(v___x_3873_);
                            v___x_3890_ = leanh::lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3866_;
            }
            3 => {
                v_fst_3878_ = leanh::lean_ctor_get(v_a_3874_, 0);
                if leanh::lean_obj_tag(v_fst_3878_) == 0 {
                    v_snd_3879_ = leanh::lean_ctor_get(v_a_3874_, 1);
                    leanh::lean_inc(v_snd_3879_);
                    leanh::lean_dec(v_a_3874_);
                    if v_isShared_3877_ == 0 {
                        leanh::lean_ctor_set(v___x_3876_, 0, v_snd_3879_);
                        v___x_3881_ = v___x_3876_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_snd_3879_);
                        v___x_3881_ = v_reuseFailAlloc_3882_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3878_);
                    leanh::lean_dec(v_a_3874_);
                    v_val_3883_ = leanh::lean_ctor_get(v_fst_3878_, 0);
                    leanh::lean_inc(v_val_3883_);
                    leanh::lean_dec_ref_known(v_fst_3878_, 1);
                    if v_isShared_3877_ == 0 {
                        leanh::lean_ctor_set(v___x_3876_, 0, v_val_3883_);
                        v___x_3885_ = v___x_3876_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3886_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3883_);
                        v___x_3885_ = v_reuseFailAlloc_3886_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3881_;
            }
            5 => {
                return v___x_3885_;
            }
            6 => {
                if v_isShared_3891_ == 0 {
                    v___x_3893_ = v___x_3890_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3893_;
            }
            8 => {
                if v_isShared_3900_ == 0 {
                    v___x_3902_ = v___x_3899_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(
    mut v_a_3905_: *mut leanh::LeanObject,
    mut v_t_3906_: *mut leanh::LeanObject,
    mut v_init_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
    mut v___y_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
    mut v___y_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_3905_, v_t_3906_, v_init_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    leanh::lean_dec(v___y_3911_);
    leanh::lean_dec_ref(v___y_3910_);
    leanh::lean_dec(v___y_3909_);
    leanh::lean_dec_ref(v___y_3908_);
    leanh::lean_dec_ref(v_t_3906_);
    leanh::lean_dec(v_a_3905_);
    return v_res_3913_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(
    mut v_mvarId_3916_: *mut leanh::LeanObject,
    mut v___x_3917_: *mut leanh::LeanObject,
    mut v___x_3918_: *mut leanh::LeanObject,
    mut v_toPreserve_3919_: *mut leanh::LeanObject,
    mut v_indirectProps_3920_: u8,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3954_: u8 = 0;
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut v_unused_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_a_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: u8 = 0;
    let mut v___x_3988_: u8 = 0;
    let mut v___x_3989_: usize = 0;
    let mut v___x_3990_: usize = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: usize = 0;
    let mut v___x_3993_: usize = 0;
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4002_: u8 = 0;
    let mut v_a_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_a_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3916_);
                v___x_3926_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3916_,
                    v___x_3917_,
                    v___y_3921_,
                    v___y_3922_,
                    v___y_3923_,
                    v___y_3924_,
                );
                if leanh::lean_obj_tag(v___x_3926_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3926_, 1);
                    v___x_3927_ = 0;
                    v___x_3928_ = leanh::lean_box((v___x_3927_) as usize);
                    v___x_3929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                    leanh::lean_ctor_set(v___x_3929_, 1, v___x_3918_);
                    v___x_3930_ = lean_st_mk_ref(v___x_3929_);
                    leanh::lean_inc(v_mvarId_3916_);
                    v___x_3931_ =
                        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(
                            v_mvarId_3916_,
                            v_toPreserve_3919_,
                            v_indirectProps_3920_,
                            v___x_3930_,
                            v___y_3921_,
                            v___y_3922_,
                            v___y_3923_,
                            v___y_3924_,
                        );
                    if leanh::lean_obj_tag(v___x_3931_) == 0 {
                        v_a_3932_ = leanh::lean_ctor_get(v___x_3931_, 0);
                        leanh::lean_inc(v_a_3932_);
                        leanh::lean_dec_ref_known(v___x_3931_, 1);
                        v___x_3933_ = lean_st_ref_get(v___x_3930_);
                        leanh::lean_dec(v___x_3930_);
                        leanh::lean_dec(v___x_3933_);
                        v_lctx_3934_ = leanh::lean_ctor_get(v___y_3921_, 2);
                        v_localInstances_3935_ = leanh::lean_ctor_get(v___y_3921_, 3);
                        v_decls_3936_ = leanh::lean_ctor_get(v_lctx_3934_, 1);
                        leanh::lean_inc_ref(v_lctx_3934_);
                        v___x_3937_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_3932_, v_decls_3936_, v_lctx_3934_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
                        if leanh::lean_obj_tag(v___x_3937_) == 0 {
                            v_a_3938_ = leanh::lean_ctor_get(v___x_3937_, 0);
                            leanh::lean_inc(v_a_3938_);
                            leanh::lean_dec_ref_known(v___x_3937_, 1);
                            v___x_3939_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3985_ = lean_array_get_size(v_localInstances_3935_);
                            v___x_3986_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0;
                            v___x_3987_ = lean_nat_dec_lt(v___x_3939_, v___x_3985_);
                            if v___x_3987_ == 0 {
                                leanh::lean_dec(v_a_3932_);
                                v___y_3941_ = v___x_3986_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3988_ = lean_nat_dec_le(v___x_3985_, v___x_3985_);
                                if v___x_3988_ == 0 {
                                    if v___x_3987_ == 0 {
                                        leanh::lean_dec(v_a_3932_);
                                        v___y_3941_ = v___x_3986_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3989_ = 0usize;
                                        v___x_3990_ = lean_usize_of_nat(v___x_3985_);
                                        v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_3932_, v_localInstances_3935_, v___x_3989_, v___x_3990_, v___x_3986_);
                                        leanh::lean_dec(v_a_3932_);
                                        v___y_3941_ = v___x_3991_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_3992_ = 0usize;
                                    v___x_3993_ = lean_usize_of_nat(v___x_3985_);
                                    v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_3932_, v_localInstances_3935_, v___x_3992_, v___x_3993_, v___x_3986_);
                                    leanh::lean_dec(v_a_3932_);
                                    v___y_3941_ = v___x_3994_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3932_);
                            leanh::lean_dec_ref(v___y_3921_);
                            leanh::lean_dec(v_mvarId_3916_);
                            v_a_3995_ = leanh::lean_ctor_get(v___x_3937_, 0);
                            v_isSharedCheck_4002_ =
                                (!leanh::lean_is_exclusive(v___x_3937_)) as u8;
                            if v_isSharedCheck_4002_ == 0 {
                                v___x_3997_ = v___x_3937_;
                                v_isShared_3998_ = v_isSharedCheck_4002_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3995_);
                                leanh::lean_dec(v___x_3937_);
                                v___x_3997_ = leanh::lean_box(0);
                                v_isShared_3998_ = v_isSharedCheck_4002_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3930_);
                        leanh::lean_dec_ref(v___y_3921_);
                        leanh::lean_dec(v_mvarId_3916_);
                        v_a_4003_ = leanh::lean_ctor_get(v___x_3931_, 0);
                        v_isSharedCheck_4010_ =
                            (!leanh::lean_is_exclusive(v___x_3931_)) as u8;
                        if v_isSharedCheck_4010_ == 0 {
                            v___x_4005_ = v___x_3931_;
                            v_isShared_4006_ = v_isSharedCheck_4010_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4003_);
                            leanh::lean_dec(v___x_3931_);
                            v___x_4005_ = leanh::lean_box(0);
                            v_isShared_4006_ = v_isSharedCheck_4010_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3921_);
                    leanh::lean_dec(v___x_3918_);
                    leanh::lean_dec(v_mvarId_3916_);
                    v_a_4011_ = leanh::lean_ctor_get(v___x_3926_, 0);
                    v_isSharedCheck_4018_ = (!leanh::lean_is_exclusive(v___x_3926_)) as u8;
                    if v_isSharedCheck_4018_ == 0 {
                        v___x_4013_ = v___x_3926_;
                        v_isShared_4014_ = v_isSharedCheck_4018_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4011_);
                        leanh::lean_dec(v___x_3926_);
                        v___x_4013_ = leanh::lean_box(0);
                        v_isShared_4014_ = v_isSharedCheck_4018_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_mvarId_3916_);
                v___x_3942_ = l_Lean_MVarId_getType(
                    v_mvarId_3916_,
                    v___y_3921_,
                    v___y_3922_,
                    v___y_3923_,
                    v___y_3924_,
                );
                if leanh::lean_obj_tag(v___x_3942_) == 0 {
                    v_a_3943_ = leanh::lean_ctor_get(v___x_3942_, 0);
                    leanh::lean_inc(v_a_3943_);
                    leanh::lean_dec_ref_known(v___x_3942_, 1);
                    v___x_3944_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_3943_, v___y_3922_);
                    v_a_3945_ = leanh::lean_ctor_get(v___x_3944_, 0);
                    leanh::lean_inc(v_a_3945_);
                    leanh::lean_dec_ref(v___x_3944_);
                    leanh::lean_inc(v_mvarId_3916_);
                    v___x_3946_ = l_Lean_MVarId_getTag(
                        v_mvarId_3916_,
                        v___y_3921_,
                        v___y_3922_,
                        v___y_3923_,
                        v___y_3924_,
                    );
                    if leanh::lean_obj_tag(v___x_3946_) == 0 {
                        v_a_3947_ = leanh::lean_ctor_get(v___x_3946_, 0);
                        leanh::lean_inc(v_a_3947_);
                        leanh::lean_dec_ref_known(v___x_3946_, 1);
                        v___x_3948_ = 2;
                        v___x_3949_ = l_Lean_Meta_mkFreshExprMVarAt(
                            v_a_3938_,
                            v___y_3941_,
                            v_a_3945_,
                            v___x_3948_,
                            v_a_3947_,
                            v___x_3939_,
                            v___y_3921_,
                            v___y_3922_,
                            v___y_3923_,
                            v___y_3924_,
                        );
                        leanh::lean_dec_ref(v___y_3921_);
                        if leanh::lean_obj_tag(v___x_3949_) == 0 {
                            v_a_3950_ = leanh::lean_ctor_get(v___x_3949_, 0);
                            leanh::lean_inc_n(v_a_3950_, 2);
                            leanh::lean_dec_ref_known(v___x_3949_, 1);
                            v___x_3951_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_3916_, v_a_3950_, v___y_3922_);
                            v_isSharedCheck_3959_ =
                                (!leanh::lean_is_exclusive(v___x_3951_)) as u8;
                            if v_isSharedCheck_3959_ == 0 {
                                v_unused_3960_ = leanh::lean_ctor_get(v___x_3951_, 0);
                                leanh::lean_dec(v_unused_3960_);
                                v___x_3953_ = v___x_3951_;
                                v_isShared_3954_ = v_isSharedCheck_3959_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3951_);
                                v___x_3953_ = leanh::lean_box(0);
                                v_isShared_3954_ = v_isSharedCheck_3959_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_mvarId_3916_);
                            v_a_3961_ = leanh::lean_ctor_get(v___x_3949_, 0);
                            v_isSharedCheck_3968_ =
                                (!leanh::lean_is_exclusive(v___x_3949_)) as u8;
                            if v_isSharedCheck_3968_ == 0 {
                                v___x_3963_ = v___x_3949_;
                                v_isShared_3964_ = v_isSharedCheck_3968_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3961_);
                                leanh::lean_dec(v___x_3949_);
                                v___x_3963_ = leanh::lean_box(0);
                                v_isShared_3964_ = v_isSharedCheck_3968_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3945_);
                        leanh::lean_dec_ref(v___y_3941_);
                        leanh::lean_dec(v_a_3938_);
                        leanh::lean_dec_ref(v___y_3921_);
                        leanh::lean_dec(v_mvarId_3916_);
                        v_a_3969_ = leanh::lean_ctor_get(v___x_3946_, 0);
                        v_isSharedCheck_3976_ =
                            (!leanh::lean_is_exclusive(v___x_3946_)) as u8;
                        if v_isSharedCheck_3976_ == 0 {
                            v___x_3971_ = v___x_3946_;
                            v_isShared_3972_ = v_isSharedCheck_3976_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3969_);
                            leanh::lean_dec(v___x_3946_);
                            v___x_3971_ = leanh::lean_box(0);
                            v_isShared_3972_ = v_isSharedCheck_3976_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3941_);
                    leanh::lean_dec(v_a_3938_);
                    leanh::lean_dec_ref(v___y_3921_);
                    leanh::lean_dec(v_mvarId_3916_);
                    v_a_3977_ = leanh::lean_ctor_get(v___x_3942_, 0);
                    v_isSharedCheck_3984_ = (!leanh::lean_is_exclusive(v___x_3942_)) as u8;
                    if v_isSharedCheck_3984_ == 0 {
                        v___x_3979_ = v___x_3942_;
                        v_isShared_3980_ = v_isSharedCheck_3984_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3977_);
                        leanh::lean_dec(v___x_3942_);
                        v___x_3979_ = leanh::lean_box(0);
                        v_isShared_3980_ = v_isSharedCheck_3984_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3955_ = l_Lean_Expr_mvarId_x21(v_a_3950_);
                leanh::lean_dec(v_a_3950_);
                if v_isShared_3954_ == 0 {
                    leanh::lean_ctor_set(v___x_3953_, 0, v___x_3955_);
                    v___x_3957_ = v___x_3953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3957_;
            }
            4 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3966_;
            }
            6 => {
                if v_isShared_3972_ == 0 {
                    v___x_3974_ = v___x_3971_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3974_;
            }
            8 => {
                if v_isShared_3980_ == 0 {
                    v___x_3982_ = v___x_3979_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
                    v___x_3982_ = v_reuseFailAlloc_3983_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3982_;
            }
            10 => {
                if v_isShared_3998_ == 0 {
                    v___x_4000_ = v___x_3997_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
                    v___x_4000_ = v_reuseFailAlloc_4001_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4000_;
            }
            12 => {
                if v_isShared_4006_ == 0 {
                    v___x_4008_ = v___x_4005_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
                    v___x_4008_ = v_reuseFailAlloc_4009_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4008_;
            }
            14 => {
                if v_isShared_4014_ == 0 {
                    v___x_4016_ = v___x_4013_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
                    v___x_4016_ = v_reuseFailAlloc_4017_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(
    mut v_mvarId_4019_: *mut leanh::LeanObject,
    mut v___x_4020_: *mut leanh::LeanObject,
    mut v___x_4021_: *mut leanh::LeanObject,
    mut v_toPreserve_4022_: *mut leanh::LeanObject,
    mut v_indirectProps_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
    mut v___y_4028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indirectProps_boxed_4029_: u8 = 0;
    let mut v_res_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indirectProps_boxed_4029_ = (leanh::lean_unbox(v_indirectProps_4023_) as u8);
    v_res_4030_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(
        v_mvarId_4019_,
        v___x_4020_,
        v___x_4021_,
        v_toPreserve_4022_,
        v_indirectProps_boxed_4029_,
        v___y_4024_,
        v___y_4025_,
        v___y_4026_,
        v___y_4027_,
    );
    leanh::lean_dec(v___y_4027_);
    leanh::lean_dec_ref(v___y_4026_);
    leanh::lean_dec(v___y_4025_);
    leanh::lean_dec_ref(v_toPreserve_4022_);
    return v_res_4030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(
    mut v_mvarId_4034_: *mut leanh::LeanObject,
    mut v_toPreserve_4035_: *mut leanh::LeanObject,
    mut v_indirectProps_4036_: u8,
    mut v_a_4037_: *mut leanh::LeanObject,
    mut v_a_4038_: *mut leanh::LeanObject,
    mut v_a_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = leanh::lean_box(1);
    v___x_4043_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1;
    v___x_4044_ = leanh::lean_box((v_indirectProps_4036_) as usize);
    leanh::lean_inc(v_mvarId_4034_);
    v___f_4045_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___f_4045_, 0, v_mvarId_4034_);
    leanh::lean_closure_set(v___f_4045_, 1, v___x_4043_);
    leanh::lean_closure_set(v___f_4045_, 2, v___x_4042_);
    leanh::lean_closure_set(v___f_4045_, 3, v_toPreserve_4035_);
    leanh::lean_closure_set(v___f_4045_, 4, v___x_4044_);
    v___x_4046_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_4034_, v___f_4045_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
    return v___x_4046_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(
    mut v_mvarId_4047_: *mut leanh::LeanObject,
    mut v_toPreserve_4048_: *mut leanh::LeanObject,
    mut v_indirectProps_4049_: *mut leanh::LeanObject,
    mut v_a_4050_: *mut leanh::LeanObject,
    mut v_a_4051_: *mut leanh::LeanObject,
    mut v_a_4052_: *mut leanh::LeanObject,
    mut v_a_4053_: *mut leanh::LeanObject,
    mut v_a_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indirectProps_boxed_4055_: u8 = 0;
    let mut v_res_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indirectProps_boxed_4055_ = (leanh::lean_unbox(v_indirectProps_4049_) as u8);
    v_res_4056_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(
        v_mvarId_4047_,
        v_toPreserve_4048_,
        v_indirectProps_boxed_4055_,
        v_a_4050_,
        v_a_4051_,
        v_a_4052_,
        v_a_4053_,
    );
    leanh::lean_dec(v_a_4053_);
    leanh::lean_dec_ref(v_a_4052_);
    leanh::lean_dec(v_a_4051_);
    leanh::lean_dec_ref(v_a_4050_);
    return v_res_4056_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(
    mut v_mvarId_4057_: *mut leanh::LeanObject,
    mut v_val_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4064_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_4057_, v_val_4058_, v___y_4060_);
    return v___x_4064_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(
    mut v_mvarId_4065_: *mut leanh::LeanObject,
    mut v_val_4066_: *mut leanh::LeanObject,
    mut v___y_4067_: *mut leanh::LeanObject,
    mut v___y_4068_: *mut leanh::LeanObject,
    mut v___y_4069_: *mut leanh::LeanObject,
    mut v___y_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4072_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_4065_, v_val_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
    leanh::lean_dec(v___y_4070_);
    leanh::lean_dec_ref(v___y_4069_);
    leanh::lean_dec(v___y_4068_);
    leanh::lean_dec_ref(v___y_4067_);
    return v_res_4072_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(
    mut v_00_u03b2_4073_: *mut leanh::LeanObject,
    mut v_x_4074_: *mut leanh::LeanObject,
    mut v_x_4075_: *mut leanh::LeanObject,
    mut v_x_4076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4077_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_4074_, v_x_4075_, v_x_4076_);
    return v___x_4077_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(
    mut v_a_4078_: *mut leanh::LeanObject,
    mut v_as_4079_: *mut leanh::LeanObject,
    mut v_sz_4080_: usize,
    mut v_i_4081_: usize,
    mut v_b_4082_: *mut leanh::LeanObject,
    mut v___y_4083_: *mut leanh::LeanObject,
    mut v___y_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
    mut v___y_4086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_4078_, v_as_4079_, v_sz_4080_, v_i_4081_, v_b_4082_);
    return v___x_4088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(
    mut v_a_4089_: *mut leanh::LeanObject,
    mut v_as_4090_: *mut leanh::LeanObject,
    mut v_sz_4091_: *mut leanh::LeanObject,
    mut v_i_4092_: *mut leanh::LeanObject,
    mut v_b_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4099_: usize = 0;
    let mut v_i_boxed_4100_: usize = 0;
    let mut v_res_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4099_ = leanh::lean_unbox_usize(v_sz_4091_);
    leanh::lean_dec(v_sz_4091_);
    v_i_boxed_4100_ = leanh::lean_unbox_usize(v_i_4092_);
    leanh::lean_dec(v_i_4092_);
    v_res_4101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_4089_, v_as_4090_, v_sz_boxed_4099_, v_i_boxed_4100_, v_b_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    leanh::lean_dec(v___y_4095_);
    leanh::lean_dec_ref(v___y_4094_);
    leanh::lean_dec_ref(v_as_4090_);
    leanh::lean_dec(v_a_4089_);
    return v_res_4101_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(
    mut v_00_u03b2_4102_: *mut leanh::LeanObject,
    mut v_x_4103_: *mut leanh::LeanObject,
    mut v_x_4104_: usize,
    mut v_x_4105_: usize,
    mut v_x_4106_: *mut leanh::LeanObject,
    mut v_x_4107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_4103_, v_x_4104_, v_x_4105_, v_x_4106_, v_x_4107_);
    return v___x_4108_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(
    mut v_00_u03b2_4109_: *mut leanh::LeanObject,
    mut v_x_4110_: *mut leanh::LeanObject,
    mut v_x_4111_: *mut leanh::LeanObject,
    mut v_x_4112_: *mut leanh::LeanObject,
    mut v_x_4113_: *mut leanh::LeanObject,
    mut v_x_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_8511__boxed_4115_: usize = 0;
    let mut v_x_8512__boxed_4116_: usize = 0;
    let mut v_res_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8511__boxed_4115_ = leanh::lean_unbox_usize(v_x_4111_);
    leanh::lean_dec(v_x_4111_);
    v_x_8512__boxed_4116_ = leanh::lean_unbox_usize(v_x_4112_);
    leanh::lean_dec(v_x_4112_);
    v_res_4117_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_4109_, v_x_4110_, v_x_8511__boxed_4115_, v_x_8512__boxed_4116_, v_x_4113_, v_x_4114_);
    return v_res_4117_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(
    mut v_a_4118_: *mut leanh::LeanObject,
    mut v_as_4119_: *mut leanh::LeanObject,
    mut v_sz_4120_: usize,
    mut v_i_4121_: usize,
    mut v_b_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_4118_, v_as_4119_, v_sz_4120_, v_i_4121_, v_b_4122_);
    return v___x_4128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(
    mut v_a_4129_: *mut leanh::LeanObject,
    mut v_as_4130_: *mut leanh::LeanObject,
    mut v_sz_4131_: *mut leanh::LeanObject,
    mut v_i_4132_: *mut leanh::LeanObject,
    mut v_b_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4139_: usize = 0;
    let mut v_i_boxed_4140_: usize = 0;
    let mut v_res_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4139_ = leanh::lean_unbox_usize(v_sz_4131_);
    leanh::lean_dec(v_sz_4131_);
    v_i_boxed_4140_ = leanh::lean_unbox_usize(v_i_4132_);
    leanh::lean_dec(v_i_4132_);
    v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_4129_, v_as_4130_, v_sz_boxed_4139_, v_i_boxed_4140_, v_b_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
    leanh::lean_dec(v___y_4137_);
    leanh::lean_dec_ref(v___y_4136_);
    leanh::lean_dec(v___y_4135_);
    leanh::lean_dec_ref(v___y_4134_);
    leanh::lean_dec_ref(v_as_4130_);
    leanh::lean_dec(v_a_4129_);
    return v_res_4141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(
    mut v_00_u03b2_4142_: *mut leanh::LeanObject,
    mut v_n_4143_: *mut leanh::LeanObject,
    mut v_k_4144_: *mut leanh::LeanObject,
    mut v_v_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_4143_, v_k_4144_, v_v_4145_);
    return v___x_4146_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(
    mut v_00_u03b2_4147_: *mut leanh::LeanObject,
    mut v_depth_4148_: usize,
    mut v_keys_4149_: *mut leanh::LeanObject,
    mut v_vals_4150_: *mut leanh::LeanObject,
    mut v_heq_4151_: *mut leanh::LeanObject,
    mut v_i_4152_: *mut leanh::LeanObject,
    mut v_entries_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_4148_, v_keys_4149_, v_vals_4150_, v_i_4152_, v_entries_4153_);
    return v___x_4154_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(
    mut v_00_u03b2_4155_: *mut leanh::LeanObject,
    mut v_depth_4156_: *mut leanh::LeanObject,
    mut v_keys_4157_: *mut leanh::LeanObject,
    mut v_vals_4158_: *mut leanh::LeanObject,
    mut v_heq_4159_: *mut leanh::LeanObject,
    mut v_i_4160_: *mut leanh::LeanObject,
    mut v_entries_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4162_: usize = 0;
    let mut v_res_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4162_ = leanh::lean_unbox_usize(v_depth_4156_);
    leanh::lean_dec(v_depth_4156_);
    v_res_4163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_4155_, v_depth_boxed_4162_, v_keys_4157_, v_vals_4158_, v_heq_4159_, v_i_4160_, v_entries_4161_);
    leanh::lean_dec_ref(v_vals_4158_);
    leanh::lean_dec_ref(v_keys_4157_);
    return v_res_4163_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(
    mut v_00_u03b2_4164_: *mut leanh::LeanObject,
    mut v_x_4165_: *mut leanh::LeanObject,
    mut v_x_4166_: *mut leanh::LeanObject,
    mut v_x_4167_: *mut leanh::LeanObject,
    mut v_x_4168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4169_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_4165_, v_x_4166_, v_x_4167_, v_x_4168_);
    return v___x_4169_;
}
pub unsafe fn l_Lean_MVarId_cleanup(
    mut v_mvarId_4170_: *mut leanh::LeanObject,
    mut v_toPreserve_4171_: *mut leanh::LeanObject,
    mut v_indirectProps_4172_: u8,
    mut v_a_4173_: *mut leanh::LeanObject,
    mut v_a_4174_: *mut leanh::LeanObject,
    mut v_a_4175_: *mut leanh::LeanObject,
    mut v_a_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4178_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(
        v_mvarId_4170_,
        v_toPreserve_4171_,
        v_indirectProps_4172_,
        v_a_4173_,
        v_a_4174_,
        v_a_4175_,
        v_a_4176_,
    );
    return v___x_4178_;
}
pub unsafe fn l_Lean_MVarId_cleanup___boxed(
    mut v_mvarId_4179_: *mut leanh::LeanObject,
    mut v_toPreserve_4180_: *mut leanh::LeanObject,
    mut v_indirectProps_4181_: *mut leanh::LeanObject,
    mut v_a_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_a_4184_: *mut leanh::LeanObject,
    mut v_a_4185_: *mut leanh::LeanObject,
    mut v_a_4186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indirectProps_boxed_4187_: u8 = 0;
    let mut v_res_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indirectProps_boxed_4187_ = (leanh::lean_unbox(v_indirectProps_4181_) as u8);
    v_res_4188_ = l_Lean_MVarId_cleanup(
        v_mvarId_4179_,
        v_toPreserve_4180_,
        v_indirectProps_boxed_4187_,
        v_a_4182_,
        v_a_4183_,
        v_a_4184_,
        v_a_4185_,
    );
    leanh::lean_dec(v_a_4185_);
    leanh::lean_dec_ref(v_a_4184_);
    leanh::lean_dec(v_a_4183_);
    leanh::lean_dec_ref(v_a_4182_);
    return v_res_4188_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cleanup(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
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
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cleanup(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cleanup(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cleanup(builtin);
}