// Lean compiler output
// Module: Lean.Compiler.LCNF.LCtx
// Imports: Lean.Compiler.LCNF.Basic
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, l_Lean_Compiler_LCNF_LetValue_toExpr,
    runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_addDecl;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedLCtx_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedLCtx: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = crate::leanh::lean_box(0);
    v___x_860_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_861_ = lean_mk_array(v___x_860_, v___x_859_);
    return v___x_861_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__0,
    );
    v___x_863_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_864_, 0, v___x_863_);
    crate::leanh::lean_ctor_set(v___x_864_, 1, v___x_862_);
    return v___x_864_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__1,
    );
    v___x_866_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 2, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 3, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 4, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_866_, 5, v___x_865_);
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default___closed__2,
    );
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedLCtx() -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Lean_Compiler_LCNF_instInhabitedLCtx_default;
    return v___x_868_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(
    mut v_a_869_: *mut crate::leanh::LeanObject,
    mut v_x_870_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_871_: u8 = 0;
    let mut v_key_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_870_) == 0 {
                    v___x_871_ = 0;
                    return v___x_871_;
                } else {
                    v_key_872_ = crate::leanh::lean_ctor_get(v_x_870_, 0);
                    v_tail_873_ = crate::leanh::lean_ctor_get(v_x_870_, 2);
                    v___x_874_ = l_Lean_instBEqFVarId_beq(v_key_872_, v_a_869_);
                    if v___x_874_ == 0 {
                        v_x_870_ = v_tail_873_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_874_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg___boxed(
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_x_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_878_: u8 = 0;
    let mut v_r_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_876_, v_x_877_);
    crate::leanh::lean_dec(v_x_877_);
    crate::leanh::lean_dec(v_a_876_);
    v_r_879_ = crate::leanh::lean_box((v_res_878_) as usize);
    return v_r_879_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_880_: *mut crate::leanh::LeanObject,
    mut v_x_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: u64 = 0;
    let mut v___x_890_: u64 = 0;
    let mut v___x_891_: u64 = 0;
    let mut v_fold_892_: u64 = 0;
    let mut v___x_893_: u64 = 0;
    let mut v___x_894_: u64 = 0;
    let mut v___x_895_: u64 = 0;
    let mut v___x_896_: usize = 0;
    let mut v___x_897_: usize = 0;
    let mut v___x_898_: usize = 0;
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_881_) == 0 {
                    return v_x_880_;
                } else {
                    v_key_882_ = crate::leanh::lean_ctor_get(v_x_881_, 0);
                    v_value_883_ = crate::leanh::lean_ctor_get(v_x_881_, 1);
                    v_tail_884_ = crate::leanh::lean_ctor_get(v_x_881_, 2);
                    v_isSharedCheck_907_ = (!crate::leanh::lean_is_exclusive(v_x_881_)) as u8;
                    if v_isSharedCheck_907_ == 0 {
                        v___x_886_ = v_x_881_;
                        v_isShared_887_ = v_isSharedCheck_907_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_884_);
                        crate::leanh::lean_inc(v_value_883_);
                        crate::leanh::lean_inc(v_key_882_);
                        crate::leanh::lean_dec(v_x_881_);
                        v___x_886_ = crate::leanh::lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_907_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_888_ = lean_array_get_size(v_x_880_);
                v___x_889_ = l_Lean_instHashableFVarId_hash(v_key_882_);
                v___x_890_ = 32u64;
                v___x_891_ = lean_uint64_shift_right(v___x_889_, v___x_890_);
                v_fold_892_ = lean_uint64_xor(v___x_889_, v___x_891_);
                v___x_893_ = 16u64;
                v___x_894_ = lean_uint64_shift_right(v_fold_892_, v___x_893_);
                v___x_895_ = lean_uint64_xor(v_fold_892_, v___x_894_);
                v___x_896_ = lean_uint64_to_usize(v___x_895_);
                v___x_897_ = lean_usize_of_nat(v___x_888_);
                v___x_898_ = 1usize;
                v___x_899_ = lean_usize_sub(v___x_897_, v___x_898_);
                v___x_900_ = lean_usize_land(v___x_896_, v___x_899_);
                v___x_901_ = lean_array_uget_borrowed(v_x_880_, v___x_900_);
                crate::leanh::lean_inc(v___x_901_);
                if v_isShared_887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_886_, 2, v___x_901_);
                    v___x_903_ = v___x_886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_906_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 0, v_key_882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 1, v_value_883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 2, v___x_901_);
                    v___x_903_ = v_reuseFailAlloc_906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_904_ = lean_array_uset(v_x_880_, v___x_900_, v___x_903_);
                v_x_880_ = v___x_904_;
                v_x_881_ = v_tail_884_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(
    mut v_i_908_: *mut crate::leanh::LeanObject,
    mut v_source_909_: *mut crate::leanh::LeanObject,
    mut v_target_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v_es_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_911_ = lean_array_get_size(v_source_909_);
                v___x_912_ = lean_nat_dec_lt(v_i_908_, v___x_911_);
                if v___x_912_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_909_);
                    crate::leanh::lean_dec(v_i_908_);
                    return v_target_910_;
                } else {
                    v_es_913_ = lean_array_fget(v_source_909_, v_i_908_);
                    v___x_914_ = crate::leanh::lean_box(0);
                    v_source_915_ = lean_array_fset(v_source_909_, v_i_908_, v___x_914_);
                    v_target_916_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_target_910_, v_es_913_);
                    v___x_917_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_918_ = lean_nat_add(v_i_908_, v___x_917_);
                    crate::leanh::lean_dec(v_i_908_);
                    v_i_908_ = v___x_918_;
                    v_source_909_ = v_source_915_;
                    v_target_910_ = v_target_916_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(
    mut v_data_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = lean_array_get_size(v_data_920_);
    v___x_922_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_923_ = lean_nat_mul(v___x_921_, v___x_922_);
    v___x_924_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_925_ = crate::leanh::lean_box(0);
    v___x_926_ = lean_mk_array(v_nbuckets_923_, v___x_925_);
    v___x_927_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v___x_924_, v_data_920_, v___x_926_);
    return v___x_927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_b_929_: *mut crate::leanh::LeanObject,
    mut v_x_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v___x_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_930_) == 0 {
                    crate::leanh::lean_dec(v_b_929_);
                    crate::leanh::lean_dec(v_a_928_);
                    return v_x_930_;
                } else {
                    v_key_931_ = crate::leanh::lean_ctor_get(v_x_930_, 0);
                    v_value_932_ = crate::leanh::lean_ctor_get(v_x_930_, 1);
                    v_tail_933_ = crate::leanh::lean_ctor_get(v_x_930_, 2);
                    v_isSharedCheck_945_ = (!crate::leanh::lean_is_exclusive(v_x_930_)) as u8;
                    if v_isSharedCheck_945_ == 0 {
                        v___x_935_ = v_x_930_;
                        v_isShared_936_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_933_);
                        crate::leanh::lean_inc(v_value_932_);
                        crate::leanh::lean_inc(v_key_931_);
                        crate::leanh::lean_dec(v_x_930_);
                        v___x_935_ = crate::leanh::lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_937_ = l_Lean_instBEqFVarId_beq(v_key_931_, v_a_928_);
                if v___x_937_ == 0 {
                    v___x_938_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_928_, v_b_929_, v_tail_933_);
                    if v_isShared_936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_935_, 2, v___x_938_);
                        v___x_940_ = v___x_935_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v_key_931_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 1, v_value_932_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 2, v___x_938_);
                        v___x_940_ = v_reuseFailAlloc_941_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_932_);
                    crate::leanh::lean_dec(v_key_931_);
                    if v_isShared_936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_935_, 1, v_b_929_);
                        crate::leanh::lean_ctor_set(v___x_935_, 0, v_a_928_);
                        v___x_943_ = v___x_935_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_944_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_928_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_944_, 1, v_b_929_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_944_, 2, v_tail_933_);
                        v___x_943_ = v_reuseFailAlloc_944_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_940_;
            }
            3 => {
                return v___x_943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(
    mut v_m_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_b_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u64 = 0;
    let mut v___x_956_: u64 = 0;
    let mut v___x_957_: u64 = 0;
    let mut v_fold_958_: u64 = 0;
    let mut v___x_959_: u64 = 0;
    let mut v___x_960_: u64 = 0;
    let mut v___x_961_: u64 = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: usize = 0;
    let mut v___x_965_: usize = 0;
    let mut v___x_966_: usize = 0;
    let mut v_bkt_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v_val_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_949_ = crate::leanh::lean_ctor_get(v_m_946_, 0);
                v_buckets_950_ = crate::leanh::lean_ctor_get(v_m_946_, 1);
                v_isSharedCheck_993_ = (!crate::leanh::lean_is_exclusive(v_m_946_)) as u8;
                if v_isSharedCheck_993_ == 0 {
                    v___x_952_ = v_m_946_;
                    v_isShared_953_ = v_isSharedCheck_993_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_950_);
                    crate::leanh::lean_inc(v_size_949_);
                    crate::leanh::lean_dec(v_m_946_);
                    v___x_952_ = crate::leanh::lean_box(0);
                    v_isShared_953_ = v_isSharedCheck_993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_954_ = lean_array_get_size(v_buckets_950_);
                v___x_955_ = l_Lean_instHashableFVarId_hash(v_a_947_);
                v___x_956_ = 32u64;
                v___x_957_ = lean_uint64_shift_right(v___x_955_, v___x_956_);
                v_fold_958_ = lean_uint64_xor(v___x_955_, v___x_957_);
                v___x_959_ = 16u64;
                v___x_960_ = lean_uint64_shift_right(v_fold_958_, v___x_959_);
                v___x_961_ = lean_uint64_xor(v_fold_958_, v___x_960_);
                v___x_962_ = lean_uint64_to_usize(v___x_961_);
                v___x_963_ = lean_usize_of_nat(v___x_954_);
                v___x_964_ = 1usize;
                v___x_965_ = lean_usize_sub(v___x_963_, v___x_964_);
                v___x_966_ = lean_usize_land(v___x_962_, v___x_965_);
                v_bkt_967_ = lean_array_uget_borrowed(v_buckets_950_, v___x_966_);
                v___x_968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_947_, v_bkt_967_);
                if v___x_968_ == 0 {
                    v___x_969_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_970_ = lean_nat_add(v_size_949_, v___x_969_);
                    crate::leanh::lean_dec(v_size_949_);
                    crate::leanh::lean_inc(v_bkt_967_);
                    v___x_971_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_971_, 0, v_a_947_);
                    crate::leanh::lean_ctor_set(v___x_971_, 1, v_b_948_);
                    crate::leanh::lean_ctor_set(v___x_971_, 2, v_bkt_967_);
                    v_buckets_x27_972_ = lean_array_uset(v_buckets_950_, v___x_966_, v___x_971_);
                    v___x_973_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_974_ = lean_nat_mul(v_size_x27_970_, v___x_973_);
                    v___x_975_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_976_ = lean_nat_div(v___x_974_, v___x_975_);
                    crate::leanh::lean_dec(v___x_974_);
                    v___x_977_ = lean_array_get_size(v_buckets_x27_972_);
                    v___x_978_ = lean_nat_dec_le(v___x_976_, v___x_977_);
                    crate::leanh::lean_dec(v___x_976_);
                    if v___x_978_ == 0 {
                        v_val_979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_buckets_x27_972_);
                        if v_isShared_953_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_952_, 1, v_val_979_);
                            crate::leanh::lean_ctor_set(v___x_952_, 0, v_size_x27_970_);
                            v___x_981_ = v___x_952_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 0, v_size_x27_970_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 1, v_val_979_);
                            v___x_981_ = v_reuseFailAlloc_982_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_953_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_952_, 1, v_buckets_x27_972_);
                            crate::leanh::lean_ctor_set(v___x_952_, 0, v_size_x27_970_);
                            v___x_984_ = v___x_952_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_985_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v_size_x27_970_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_985_,
                                1,
                                v_buckets_x27_972_,
                            );
                            v___x_984_ = v_reuseFailAlloc_985_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_967_);
                    v___x_986_ = crate::leanh::lean_box(0);
                    v_buckets_x27_987_ = lean_array_uset(v_buckets_950_, v___x_966_, v___x_986_);
                    v___x_988_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_947_, v_b_948_, v_bkt_967_);
                    v___x_989_ = lean_array_uset(v_buckets_x27_987_, v___x_966_, v___x_988_);
                    if v_isShared_953_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_989_);
                        v___x_991_ = v___x_952_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v_size_949_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
                        v___x_991_ = v_reuseFailAlloc_992_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_981_;
            }
            3 => {
                return v___x_984_;
            }
            4 => {
                return v___x_991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addParam(
    mut v_pu_994_: u8,
    mut v_lctx_995_: *mut crate::leanh::LeanObject,
    mut v_param_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPure_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v_fvarId_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_paramsPure_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1020_: u8 = 0;
    let mut v_fvarId_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_994_ == 0 {
                    v_paramsPure_997_ = crate::leanh::lean_ctor_get(v_lctx_995_, 0);
                    v_paramsImpure_998_ = crate::leanh::lean_ctor_get(v_lctx_995_, 1);
                    v_letDeclsPure_999_ = crate::leanh::lean_ctor_get(v_lctx_995_, 2);
                    v_letDeclsImpure_1000_ = crate::leanh::lean_ctor_get(v_lctx_995_, 3);
                    v_funDeclsPure_1001_ = crate::leanh::lean_ctor_get(v_lctx_995_, 4);
                    v_funDeclsImpure_1002_ = crate::leanh::lean_ctor_get(v_lctx_995_, 5);
                    v_isSharedCheck_1011_ = (!crate::leanh::lean_is_exclusive(v_lctx_995_)) as u8;
                    if v_isSharedCheck_1011_ == 0 {
                        v___x_1004_ = v_lctx_995_;
                        v_isShared_1005_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1002_);
                        crate::leanh::lean_inc(v_funDeclsPure_1001_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1000_);
                        crate::leanh::lean_inc(v_letDeclsPure_999_);
                        crate::leanh::lean_inc(v_paramsImpure_998_);
                        crate::leanh::lean_inc(v_paramsPure_997_);
                        crate::leanh::lean_dec(v_lctx_995_);
                        v___x_1004_ = crate::leanh::lean_box(0);
                        v_isShared_1005_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_paramsPure_1012_ = crate::leanh::lean_ctor_get(v_lctx_995_, 0);
                    v_paramsImpure_1013_ = crate::leanh::lean_ctor_get(v_lctx_995_, 1);
                    v_letDeclsPure_1014_ = crate::leanh::lean_ctor_get(v_lctx_995_, 2);
                    v_letDeclsImpure_1015_ = crate::leanh::lean_ctor_get(v_lctx_995_, 3);
                    v_funDeclsPure_1016_ = crate::leanh::lean_ctor_get(v_lctx_995_, 4);
                    v_funDeclsImpure_1017_ = crate::leanh::lean_ctor_get(v_lctx_995_, 5);
                    v_isSharedCheck_1026_ = (!crate::leanh::lean_is_exclusive(v_lctx_995_)) as u8;
                    if v_isSharedCheck_1026_ == 0 {
                        v___x_1019_ = v_lctx_995_;
                        v_isShared_1020_ = v_isSharedCheck_1026_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1017_);
                        crate::leanh::lean_inc(v_funDeclsPure_1016_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1015_);
                        crate::leanh::lean_inc(v_letDeclsPure_1014_);
                        crate::leanh::lean_inc(v_paramsImpure_1013_);
                        crate::leanh::lean_inc(v_paramsPure_1012_);
                        crate::leanh::lean_dec(v_lctx_995_);
                        v___x_1019_ = crate::leanh::lean_box(0);
                        v_isShared_1020_ = v_isSharedCheck_1026_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_1006_ = crate::leanh::lean_ctor_get(v_param_996_, 0);
                crate::leanh::lean_inc(v_fvarId_1006_);
                v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsPure_997_, v_fvarId_1006_, v_param_996_);
                if v_isShared_1005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1007_);
                    v___x_1009_ = v___x_1004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1010_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_paramsImpure_998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_letDeclsPure_999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_letDeclsImpure_1000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_funDeclsPure_1001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 5, v_funDeclsImpure_1002_);
                    v___x_1009_ = v_reuseFailAlloc_1010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1009_;
            }
            3 => {
                v_fvarId_1021_ = crate::leanh::lean_ctor_get(v_param_996_, 0);
                crate::leanh::lean_inc(v_fvarId_1021_);
                v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_paramsImpure_1013_, v_fvarId_1021_, v_param_996_);
                if v_isShared_1020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1019_, 1, v___x_1022_);
                    v___x_1024_ = v___x_1019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1025_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_paramsPure_1012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_letDeclsPure_1014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_letDeclsImpure_1015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_funDeclsPure_1016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_funDeclsImpure_1017_);
                    v___x_1024_ = v_reuseFailAlloc_1025_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addParam___boxed(
    mut v_pu_1027_: *mut crate::leanh::LeanObject,
    mut v_lctx_1028_: *mut crate::leanh::LeanObject,
    mut v_param_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1030_: u8 = 0;
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1030_ = (crate::leanh::lean_unbox(v_pu_1027_) as u8);
    v_res_1031_ = l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_boxed_1030_, v_lctx_1028_, v_param_1029_);
    return v_res_1031_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0(
    mut v_00_u03b2_1032_: *mut crate::leanh::LeanObject,
    mut v_m_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_b_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_m_1033_, v_a_1034_, v_b_1035_);
    return v___x_1036_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(
    mut v_00_u03b2_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_x_1039_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1040_: u8 = 0;
    v___x_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_1038_, v_x_1039_);
    return v___x_1040_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___boxed(
    mut v_00_u03b2_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_x_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1044_: u8 = 0;
    let mut v_r_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0(v_00_u03b2_1041_, v_a_1042_, v_x_1043_);
    crate::leanh::lean_dec(v_x_1043_);
    crate::leanh::lean_dec(v_a_1042_);
    v_r_1045_ = crate::leanh::lean_box((v_res_1044_) as usize);
    return v_r_1045_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1(
    mut v_00_u03b2_1046_: *mut crate::leanh::LeanObject,
    mut v_data_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1___redArg(v_data_1047_);
    return v___x_1048_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2(
    mut v_00_u03b2_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_b_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__2___redArg(v_a_1050_, v_b_1051_, v_x_1052_);
    return v___x_1053_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1054_: *mut crate::leanh::LeanObject,
    mut v_i_1055_: *mut crate::leanh::LeanObject,
    mut v_source_1056_: *mut crate::leanh::LeanObject,
    mut v_target_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2___redArg(v_i_1055_, v_source_1056_, v_target_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1059_: *mut crate::leanh::LeanObject,
    mut v_x_1060_: *mut crate::leanh::LeanObject,
    mut v_x_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1060_, v_x_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addLetDecl(
    mut v_pu_1063_: u8,
    mut v_lctx_1064_: *mut crate::leanh::LeanObject,
    mut v_letDecl_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPure_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v_fvarId_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_paramsPure_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1089_: u8 = 0;
    let mut v_fvarId_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1063_ == 0 {
                    v_paramsPure_1066_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 0);
                    v_paramsImpure_1067_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 1);
                    v_letDeclsPure_1068_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 2);
                    v_letDeclsImpure_1069_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 3);
                    v_funDeclsPure_1070_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 4);
                    v_funDeclsImpure_1071_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 5);
                    v_isSharedCheck_1080_ = (!crate::leanh::lean_is_exclusive(v_lctx_1064_)) as u8;
                    if v_isSharedCheck_1080_ == 0 {
                        v___x_1073_ = v_lctx_1064_;
                        v_isShared_1074_ = v_isSharedCheck_1080_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1071_);
                        crate::leanh::lean_inc(v_funDeclsPure_1070_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1069_);
                        crate::leanh::lean_inc(v_letDeclsPure_1068_);
                        crate::leanh::lean_inc(v_paramsImpure_1067_);
                        crate::leanh::lean_inc(v_paramsPure_1066_);
                        crate::leanh::lean_dec(v_lctx_1064_);
                        v___x_1073_ = crate::leanh::lean_box(0);
                        v_isShared_1074_ = v_isSharedCheck_1080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_paramsPure_1081_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 0);
                    v_paramsImpure_1082_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 1);
                    v_letDeclsPure_1083_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 2);
                    v_letDeclsImpure_1084_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 3);
                    v_funDeclsPure_1085_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 4);
                    v_funDeclsImpure_1086_ = crate::leanh::lean_ctor_get(v_lctx_1064_, 5);
                    v_isSharedCheck_1095_ = (!crate::leanh::lean_is_exclusive(v_lctx_1064_)) as u8;
                    if v_isSharedCheck_1095_ == 0 {
                        v___x_1088_ = v_lctx_1064_;
                        v_isShared_1089_ = v_isSharedCheck_1095_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1086_);
                        crate::leanh::lean_inc(v_funDeclsPure_1085_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1084_);
                        crate::leanh::lean_inc(v_letDeclsPure_1083_);
                        crate::leanh::lean_inc(v_paramsImpure_1082_);
                        crate::leanh::lean_inc(v_paramsPure_1081_);
                        crate::leanh::lean_dec(v_lctx_1064_);
                        v___x_1088_ = crate::leanh::lean_box(0);
                        v_isShared_1089_ = v_isSharedCheck_1095_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_1075_ = crate::leanh::lean_ctor_get(v_letDecl_1065_, 0);
                crate::leanh::lean_inc(v_fvarId_1075_);
                v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsPure_1068_, v_fvarId_1075_, v_letDecl_1065_);
                if v_isShared_1074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1073_, 2, v___x_1076_);
                    v___x_1078_ = v___x_1073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_paramsPure_1066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_paramsImpure_1067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___x_1076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_letDeclsImpure_1069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_funDeclsPure_1070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_funDeclsImpure_1071_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1078_;
            }
            3 => {
                v_fvarId_1090_ = crate::leanh::lean_ctor_get(v_letDecl_1065_, 0);
                crate::leanh::lean_inc(v_fvarId_1090_);
                v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_letDeclsImpure_1084_, v_fvarId_1090_, v_letDecl_1065_);
                if v_isShared_1089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1088_, 3, v___x_1091_);
                    v___x_1093_ = v___x_1088_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_paramsPure_1081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_paramsImpure_1082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_letDeclsPure_1083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___x_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_funDeclsPure_1085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 5, v_funDeclsImpure_1086_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addLetDecl___boxed(
    mut v_pu_1096_: *mut crate::leanh::LeanObject,
    mut v_lctx_1097_: *mut crate::leanh::LeanObject,
    mut v_letDecl_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1099_: u8 = 0;
    let mut v_res_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1099_ = (crate::leanh::lean_unbox(v_pu_1096_) as u8);
    v_res_1100_ =
        l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_boxed_1099_, v_lctx_1097_, v_letDecl_1098_);
    return v_res_1100_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addFunDecl(
    mut v_pu_1101_: u8,
    mut v_lctx_1102_: *mut crate::leanh::LeanObject,
    mut v_funDecl_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_fvarId_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1101_ == 0 {
                    v_fvarId_1104_ = crate::leanh::lean_ctor_get(v_funDecl_1103_, 0);
                    crate::leanh::lean_inc(v_fvarId_1104_);
                    v_paramsPure_1105_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 0);
                    v_paramsImpure_1106_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 1);
                    v_letDeclsPure_1107_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 2);
                    v_letDeclsImpure_1108_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 3);
                    v_funDeclsPure_1109_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 4);
                    v_funDeclsImpure_1110_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 5);
                    v_isSharedCheck_1118_ = (!crate::leanh::lean_is_exclusive(v_lctx_1102_)) as u8;
                    if v_isSharedCheck_1118_ == 0 {
                        v___x_1112_ = v_lctx_1102_;
                        v_isShared_1113_ = v_isSharedCheck_1118_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1110_);
                        crate::leanh::lean_inc(v_funDeclsPure_1109_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1108_);
                        crate::leanh::lean_inc(v_letDeclsPure_1107_);
                        crate::leanh::lean_inc(v_paramsImpure_1106_);
                        crate::leanh::lean_inc(v_paramsPure_1105_);
                        crate::leanh::lean_dec(v_lctx_1102_);
                        v___x_1112_ = crate::leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1118_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fvarId_1119_ = crate::leanh::lean_ctor_get(v_funDecl_1103_, 0);
                    crate::leanh::lean_inc(v_fvarId_1119_);
                    v_paramsPure_1120_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 0);
                    v_paramsImpure_1121_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 1);
                    v_letDeclsPure_1122_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 2);
                    v_letDeclsImpure_1123_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 3);
                    v_funDeclsPure_1124_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 4);
                    v_funDeclsImpure_1125_ = crate::leanh::lean_ctor_get(v_lctx_1102_, 5);
                    v_isSharedCheck_1133_ = (!crate::leanh::lean_is_exclusive(v_lctx_1102_)) as u8;
                    if v_isSharedCheck_1133_ == 0 {
                        v___x_1127_ = v_lctx_1102_;
                        v_isShared_1128_ = v_isSharedCheck_1133_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1125_);
                        crate::leanh::lean_inc(v_funDeclsPure_1124_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1123_);
                        crate::leanh::lean_inc(v_letDeclsPure_1122_);
                        crate::leanh::lean_inc(v_paramsImpure_1121_);
                        crate::leanh::lean_inc(v_paramsPure_1120_);
                        crate::leanh::lean_dec(v_lctx_1102_);
                        v___x_1127_ = crate::leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1133_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsPure_1109_, v_fvarId_1104_, v_funDecl_1103_);
                if v_isShared_1113_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1112_, 4, v___x_1114_);
                    v___x_1116_ = v___x_1112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_paramsPure_1105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_paramsImpure_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_letDeclsPure_1107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_letDeclsImpure_1108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___x_1114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 5, v_funDeclsImpure_1110_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1116_;
            }
            3 => {
                v___x_1129_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(v_funDeclsImpure_1125_, v_fvarId_1119_, v_funDecl_1103_);
                if v_isShared_1128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1127_, 5, v___x_1129_);
                    v___x_1131_ = v___x_1127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1132_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_paramsPure_1120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_paramsImpure_1121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_letDeclsPure_1122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_letDeclsImpure_1123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_funDeclsPure_1124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1132_, 5, v___x_1129_);
                    v___x_1131_ = v_reuseFailAlloc_1132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_addFunDecl___boxed(
    mut v_pu_1134_: *mut crate::leanh::LeanObject,
    mut v_lctx_1135_: *mut crate::leanh::LeanObject,
    mut v_funDecl_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1137_: u8 = 0;
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1137_ = (crate::leanh::lean_unbox(v_pu_1134_) as u8);
    v_res_1138_ =
        l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_boxed_1137_, v_lctx_1135_, v_funDecl_1136_);
    return v_res_1138_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(
    mut v_a_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1140_) == 0 {
                    return v_x_1140_;
                } else {
                    v_key_1141_ = crate::leanh::lean_ctor_get(v_x_1140_, 0);
                    v_value_1142_ = crate::leanh::lean_ctor_get(v_x_1140_, 1);
                    v_tail_1143_ = crate::leanh::lean_ctor_get(v_x_1140_, 2);
                    v_isSharedCheck_1152_ = (!crate::leanh::lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1152_ == 0 {
                        v___x_1145_ = v_x_1140_;
                        v_isShared_1146_ = v_isSharedCheck_1152_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1143_);
                        crate::leanh::lean_inc(v_value_1142_);
                        crate::leanh::lean_inc(v_key_1141_);
                        crate::leanh::lean_dec(v_x_1140_);
                        v___x_1145_ = crate::leanh::lean_box(0);
                        v_isShared_1146_ = v_isSharedCheck_1152_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1147_ = l_Lean_instBEqFVarId_beq(v_key_1141_, v_a_1139_);
                if v___x_1147_ == 0 {
                    v___x_1148_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_1139_, v_tail_1143_);
                    if v_isShared_1146_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1145_, 2, v___x_1148_);
                        v___x_1150_ = v___x_1145_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1151_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_key_1141_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_value_1142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 2, v___x_1148_);
                        v___x_1150_ = v_reuseFailAlloc_1151_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1145_);
                    crate::leanh::lean_dec(v_value_1142_);
                    crate::leanh::lean_dec(v_key_1141_);
                    return v_tail_1143_;
                }
            }
            2 => {
                return v___x_1150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg___boxed(
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_x_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_1153_, v_x_1154_);
    crate::leanh::lean_dec(v_a_1153_);
    return v_res_1155_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(
    mut v_m_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u64 = 0;
    let mut v___x_1162_: u64 = 0;
    let mut v___x_1163_: u64 = 0;
    let mut v_fold_1164_: u64 = 0;
    let mut v___x_1165_: u64 = 0;
    let mut v___x_1166_: u64 = 0;
    let mut v___x_1167_: u64 = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v_bkt_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_unused_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1158_ = crate::leanh::lean_ctor_get(v_m_1156_, 0);
                v_buckets_1159_ = crate::leanh::lean_ctor_get(v_m_1156_, 1);
                v___x_1160_ = lean_array_get_size(v_buckets_1159_);
                v___x_1161_ = l_Lean_instHashableFVarId_hash(v_a_1157_);
                v___x_1162_ = 32u64;
                v___x_1163_ = lean_uint64_shift_right(v___x_1161_, v___x_1162_);
                v_fold_1164_ = lean_uint64_xor(v___x_1161_, v___x_1163_);
                v___x_1165_ = 16u64;
                v___x_1166_ = lean_uint64_shift_right(v_fold_1164_, v___x_1165_);
                v___x_1167_ = lean_uint64_xor(v_fold_1164_, v___x_1166_);
                v___x_1168_ = lean_uint64_to_usize(v___x_1167_);
                v___x_1169_ = lean_usize_of_nat(v___x_1160_);
                v___x_1170_ = 1usize;
                v___x_1171_ = lean_usize_sub(v___x_1169_, v___x_1170_);
                v___x_1172_ = lean_usize_land(v___x_1168_, v___x_1171_);
                v_bkt_1173_ = lean_array_uget_borrowed(v_buckets_1159_, v___x_1172_);
                v___x_1174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_LCtx_addParam_spec__0_spec__0___redArg(v_a_1157_, v_bkt_1173_);
                if v___x_1174_ == 0 {
                    return v_m_1156_;
                } else {
                    crate::leanh::lean_inc(v_bkt_1173_);
                    crate::leanh::lean_inc_ref(v_buckets_1159_);
                    crate::leanh::lean_inc(v_size_1158_);
                    v_isSharedCheck_1187_ = (!crate::leanh::lean_is_exclusive(v_m_1156_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v_unused_1188_ = crate::leanh::lean_ctor_get(v_m_1156_, 1);
                        crate::leanh::lean_dec(v_unused_1188_);
                        v_unused_1189_ = crate::leanh::lean_ctor_get(v_m_1156_, 0);
                        crate::leanh::lean_dec(v_unused_1189_);
                        v___x_1176_ = v_m_1156_;
                        v_isShared_1177_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1156_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1178_ = crate::leanh::lean_box(0);
                v_buckets_x27_1179_ = lean_array_uset(v_buckets_1159_, v___x_1172_, v___x_1178_);
                v___x_1180_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1181_ = lean_nat_sub(v_size_1158_, v___x_1180_);
                crate::leanh::lean_dec(v_size_1158_);
                v___x_1182_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_1157_, v_bkt_1173_);
                v___x_1183_ = lean_array_uset(v_buckets_x27_1179_, v___x_1172_, v___x_1182_);
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1176_, 1, v___x_1183_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1181_);
                    v___x_1185_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
                    v___x_1185_ = v_reuseFailAlloc_1186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg___boxed(
    mut v_m_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1192_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_1190_, v_a_1191_);
    crate::leanh::lean_dec(v_a_1191_);
    return v_res_1192_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseParam(
    mut v_pu_1193_: u8,
    mut v_lctx_1194_: *mut crate::leanh::LeanObject,
    mut v_param_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPure_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v_fvarId_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_paramsPure_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v_fvarId_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1193_ == 0 {
                    v_paramsPure_1196_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 0);
                    v_paramsImpure_1197_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 1);
                    v_letDeclsPure_1198_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 2);
                    v_letDeclsImpure_1199_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 3);
                    v_funDeclsPure_1200_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 4);
                    v_funDeclsImpure_1201_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 5);
                    v_isSharedCheck_1210_ = (!crate::leanh::lean_is_exclusive(v_lctx_1194_)) as u8;
                    if v_isSharedCheck_1210_ == 0 {
                        v___x_1203_ = v_lctx_1194_;
                        v_isShared_1204_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1201_);
                        crate::leanh::lean_inc(v_funDeclsPure_1200_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1199_);
                        crate::leanh::lean_inc(v_letDeclsPure_1198_);
                        crate::leanh::lean_inc(v_paramsImpure_1197_);
                        crate::leanh::lean_inc(v_paramsPure_1196_);
                        crate::leanh::lean_dec(v_lctx_1194_);
                        v___x_1203_ = crate::leanh::lean_box(0);
                        v_isShared_1204_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_paramsPure_1211_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 0);
                    v_paramsImpure_1212_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 1);
                    v_letDeclsPure_1213_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 2);
                    v_letDeclsImpure_1214_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 3);
                    v_funDeclsPure_1215_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 4);
                    v_funDeclsImpure_1216_ = crate::leanh::lean_ctor_get(v_lctx_1194_, 5);
                    v_isSharedCheck_1225_ = (!crate::leanh::lean_is_exclusive(v_lctx_1194_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1218_ = v_lctx_1194_;
                        v_isShared_1219_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1216_);
                        crate::leanh::lean_inc(v_funDeclsPure_1215_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1214_);
                        crate::leanh::lean_inc(v_letDeclsPure_1213_);
                        crate::leanh::lean_inc(v_paramsImpure_1212_);
                        crate::leanh::lean_inc(v_paramsPure_1211_);
                        crate::leanh::lean_dec(v_lctx_1194_);
                        v___x_1218_ = crate::leanh::lean_box(0);
                        v_isShared_1219_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_1205_ = crate::leanh::lean_ctor_get(v_param_1195_, 0);
                v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsPure_1196_, v_fvarId_1205_);
                if v_isShared_1204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1203_, 0, v___x_1206_);
                    v___x_1208_ = v___x_1203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_paramsImpure_1197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_letDeclsPure_1198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_letDeclsImpure_1199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_funDeclsPure_1200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 5, v_funDeclsImpure_1201_);
                    v___x_1208_ = v_reuseFailAlloc_1209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1208_;
            }
            3 => {
                v_fvarId_1220_ = crate::leanh::lean_ctor_get(v_param_1195_, 0);
                v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_paramsImpure_1212_, v_fvarId_1220_);
                if v_isShared_1219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1218_, 1, v___x_1221_);
                    v___x_1223_ = v___x_1218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_paramsPure_1211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_letDeclsPure_1213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_letDeclsImpure_1214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_funDeclsPure_1215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 5, v_funDeclsImpure_1216_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseParam___boxed(
    mut v_pu_1226_: *mut crate::leanh::LeanObject,
    mut v_lctx_1227_: *mut crate::leanh::LeanObject,
    mut v_param_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1229_: u8 = 0;
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1229_ = (crate::leanh::lean_unbox(v_pu_1226_) as u8);
    v_res_1230_ =
        l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_boxed_1229_, v_lctx_1227_, v_param_1228_);
    crate::leanh::lean_dec_ref(v_param_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(
    mut v_00_u03b2_1231_: *mut crate::leanh::LeanObject,
    mut v_m_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_m_1232_, v_a_1233_);
    return v___x_1234_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___boxed(
    mut v_00_u03b2_1235_: *mut crate::leanh::LeanObject,
    mut v_m_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ =
        l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0(
            v_00_u03b2_1235_,
            v_m_1236_,
            v_a_1237_,
        );
    crate::leanh::lean_dec(v_a_1237_);
    return v_res_1238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(
    mut v_00_u03b2_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_x_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___redArg(v_a_1240_, v_x_1241_);
    return v___x_1242_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0___boxed(
    mut v_00_u03b2_1243_: *mut crate::leanh::LeanObject,
    mut v_a_1244_: *mut crate::leanh::LeanObject,
    mut v_x_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0_spec__0(v_00_u03b2_1243_, v_a_1244_, v_x_1245_);
    crate::leanh::lean_dec(v_a_1244_);
    return v_res_1246_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(
    mut v_as_1247_: *mut crate::leanh::LeanObject,
    mut v_i_1248_: usize,
    mut v_stop_1249_: usize,
    mut v_b_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1251_ = lean_usize_dec_eq(v_i_1248_, v_stop_1249_);
                if v___x_1251_ == 0 {
                    v___x_1252_ = lean_array_uget_borrowed(v_as_1247_, v_i_1248_);
                    v_fvarId_1253_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
                    v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_b_1250_, v_fvarId_1253_);
                    v___x_1255_ = 1usize;
                    v___x_1256_ = lean_usize_add(v_i_1248_, v___x_1255_);
                    v_i_1248_ = v___x_1256_;
                    v_b_1250_ = v___x_1254_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1250_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0___boxed(
    mut v_as_1258_: *mut crate::leanh::LeanObject,
    mut v_i_1259_: *mut crate::leanh::LeanObject,
    mut v_stop_1260_: *mut crate::leanh::LeanObject,
    mut v_b_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1262_: usize = 0;
    let mut v_stop_boxed_1263_: usize = 0;
    let mut v_res_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1262_ = crate::leanh::lean_unbox_usize(v_i_1259_);
    crate::leanh::lean_dec(v_i_1259_);
    v_stop_boxed_1263_ = crate::leanh::lean_unbox_usize(v_stop_1260_);
    crate::leanh::lean_dec(v_stop_1260_);
    v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_as_1258_, v_i_boxed_1262_, v_stop_boxed_1263_, v_b_1261_);
    crate::leanh::lean_dec_ref(v_as_1258_);
    return v_res_1264_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseParams(
    mut v_pu_1265_: u8,
    mut v_lctx_1266_: *mut crate::leanh::LeanObject,
    mut v_ps_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPure_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1280_: u8 = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v_unused_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: usize = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_unused_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1322_: u8 = 0;
    let mut v___x_1323_: usize = 0;
    let mut v___x_1324_: usize = 0;
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_unused_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: usize = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_unused_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1265_ == 0 {
                    v_paramsPure_1268_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                    v_paramsImpure_1269_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                    v_letDeclsPure_1270_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                    v_letDeclsImpure_1271_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                    v_funDeclsPure_1272_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                    v_funDeclsImpure_1273_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                    v___x_1274_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1275_ = lean_array_get_size(v_ps_1267_);
                    v___x_1276_ = lean_nat_dec_lt(v___x_1274_, v___x_1275_);
                    if v___x_1276_ == 0 {
                        return v_lctx_1266_;
                    } else {
                        v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
                        if v___x_1277_ == 0 {
                            if v___x_1276_ == 0 {
                                return v_lctx_1266_;
                            } else {
                                crate::leanh::lean_inc_ref(v_funDeclsImpure_1273_);
                                crate::leanh::lean_inc_ref(v_funDeclsPure_1272_);
                                crate::leanh::lean_inc_ref(v_letDeclsImpure_1271_);
                                crate::leanh::lean_inc_ref(v_letDeclsPure_1270_);
                                crate::leanh::lean_inc_ref(v_paramsImpure_1269_);
                                crate::leanh::lean_inc_ref(v_paramsPure_1268_);
                                v_isSharedCheck_1287_ =
                                    (!crate::leanh::lean_is_exclusive(v_lctx_1266_)) as u8;
                                if v_isSharedCheck_1287_ == 0 {
                                    v_unused_1288_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                                    crate::leanh::lean_dec(v_unused_1288_);
                                    v_unused_1289_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                                    crate::leanh::lean_dec(v_unused_1289_);
                                    v_unused_1290_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                                    crate::leanh::lean_dec(v_unused_1290_);
                                    v_unused_1291_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                                    crate::leanh::lean_dec(v_unused_1291_);
                                    v_unused_1292_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                                    crate::leanh::lean_dec(v_unused_1292_);
                                    v_unused_1293_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                                    crate::leanh::lean_dec(v_unused_1293_);
                                    v___x_1279_ = v_lctx_1266_;
                                    v_isShared_1280_ = v_isSharedCheck_1287_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_lctx_1266_);
                                    v___x_1279_ = crate::leanh::lean_box(0);
                                    v_isShared_1280_ = v_isSharedCheck_1287_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_funDeclsImpure_1273_);
                            crate::leanh::lean_inc_ref(v_funDeclsPure_1272_);
                            crate::leanh::lean_inc_ref(v_letDeclsImpure_1271_);
                            crate::leanh::lean_inc_ref(v_letDeclsPure_1270_);
                            crate::leanh::lean_inc_ref(v_paramsImpure_1269_);
                            crate::leanh::lean_inc_ref(v_paramsPure_1268_);
                            v_isSharedCheck_1303_ =
                                (!crate::leanh::lean_is_exclusive(v_lctx_1266_)) as u8;
                            if v_isSharedCheck_1303_ == 0 {
                                v_unused_1304_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                                crate::leanh::lean_dec(v_unused_1304_);
                                v_unused_1305_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                                crate::leanh::lean_dec(v_unused_1305_);
                                v_unused_1306_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                                crate::leanh::lean_dec(v_unused_1306_);
                                v_unused_1307_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                                crate::leanh::lean_dec(v_unused_1307_);
                                v_unused_1308_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                                crate::leanh::lean_dec(v_unused_1308_);
                                v_unused_1309_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                                crate::leanh::lean_dec(v_unused_1309_);
                                v___x_1295_ = v_lctx_1266_;
                                v_isShared_1296_ = v_isSharedCheck_1303_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_lctx_1266_);
                                v___x_1295_ = crate::leanh::lean_box(0);
                                v_isShared_1296_ = v_isSharedCheck_1303_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_paramsPure_1310_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                    v_paramsImpure_1311_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                    v_letDeclsPure_1312_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                    v_letDeclsImpure_1313_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                    v_funDeclsPure_1314_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                    v_funDeclsImpure_1315_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                    v___x_1316_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1317_ = lean_array_get_size(v_ps_1267_);
                    v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
                    if v___x_1318_ == 0 {
                        return v_lctx_1266_;
                    } else {
                        v___x_1319_ = lean_nat_dec_le(v___x_1317_, v___x_1317_);
                        if v___x_1319_ == 0 {
                            if v___x_1318_ == 0 {
                                return v_lctx_1266_;
                            } else {
                                crate::leanh::lean_inc_ref(v_funDeclsImpure_1315_);
                                crate::leanh::lean_inc_ref(v_funDeclsPure_1314_);
                                crate::leanh::lean_inc_ref(v_letDeclsImpure_1313_);
                                crate::leanh::lean_inc_ref(v_letDeclsPure_1312_);
                                crate::leanh::lean_inc_ref(v_paramsImpure_1311_);
                                crate::leanh::lean_inc_ref(v_paramsPure_1310_);
                                v_isSharedCheck_1329_ =
                                    (!crate::leanh::lean_is_exclusive(v_lctx_1266_)) as u8;
                                if v_isSharedCheck_1329_ == 0 {
                                    v_unused_1330_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                                    crate::leanh::lean_dec(v_unused_1330_);
                                    v_unused_1331_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                                    crate::leanh::lean_dec(v_unused_1331_);
                                    v_unused_1332_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                                    crate::leanh::lean_dec(v_unused_1332_);
                                    v_unused_1333_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                                    crate::leanh::lean_dec(v_unused_1333_);
                                    v_unused_1334_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                                    crate::leanh::lean_dec(v_unused_1334_);
                                    v_unused_1335_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                                    crate::leanh::lean_dec(v_unused_1335_);
                                    v___x_1321_ = v_lctx_1266_;
                                    v_isShared_1322_ = v_isSharedCheck_1329_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_lctx_1266_);
                                    v___x_1321_ = crate::leanh::lean_box(0);
                                    v_isShared_1322_ = v_isSharedCheck_1329_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_funDeclsImpure_1315_);
                            crate::leanh::lean_inc_ref(v_funDeclsPure_1314_);
                            crate::leanh::lean_inc_ref(v_letDeclsImpure_1313_);
                            crate::leanh::lean_inc_ref(v_letDeclsPure_1312_);
                            crate::leanh::lean_inc_ref(v_paramsImpure_1311_);
                            crate::leanh::lean_inc_ref(v_paramsPure_1310_);
                            v_isSharedCheck_1345_ =
                                (!crate::leanh::lean_is_exclusive(v_lctx_1266_)) as u8;
                            if v_isSharedCheck_1345_ == 0 {
                                v_unused_1346_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 5);
                                crate::leanh::lean_dec(v_unused_1346_);
                                v_unused_1347_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 4);
                                crate::leanh::lean_dec(v_unused_1347_);
                                v_unused_1348_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 3);
                                crate::leanh::lean_dec(v_unused_1348_);
                                v_unused_1349_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 2);
                                crate::leanh::lean_dec(v_unused_1349_);
                                v_unused_1350_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 1);
                                crate::leanh::lean_dec(v_unused_1350_);
                                v_unused_1351_ = crate::leanh::lean_ctor_get(v_lctx_1266_, 0);
                                crate::leanh::lean_dec(v_unused_1351_);
                                v___x_1337_ = v_lctx_1266_;
                                v_isShared_1338_ = v_isSharedCheck_1345_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_lctx_1266_);
                                v___x_1337_ = crate::leanh::lean_box(0);
                                v_isShared_1338_ = v_isSharedCheck_1345_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1281_ = 0usize;
                v___x_1282_ = lean_usize_of_nat(v___x_1275_);
                v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_1267_, v___x_1281_, v___x_1282_, v_paramsPure_1268_);
                if v_isShared_1280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1279_, 0, v___x_1283_);
                    v___x_1285_ = v___x_1279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_paramsImpure_1269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_letDeclsPure_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_letDeclsImpure_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_funDeclsPure_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_funDeclsImpure_1273_);
                    v___x_1285_ = v_reuseFailAlloc_1286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1285_;
            }
            3 => {
                v___x_1297_ = 0usize;
                v___x_1298_ = lean_usize_of_nat(v___x_1275_);
                v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_1267_, v___x_1297_, v___x_1298_, v_paramsPure_1268_);
                if v_isShared_1296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1295_, 0, v___x_1299_);
                    v___x_1301_ = v___x_1295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_paramsImpure_1269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_letDeclsPure_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_letDeclsImpure_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_funDeclsPure_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 5, v_funDeclsImpure_1273_);
                    v___x_1301_ = v_reuseFailAlloc_1302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1301_;
            }
            5 => {
                v___x_1323_ = 0usize;
                v___x_1324_ = lean_usize_of_nat(v___x_1317_);
                v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_1267_, v___x_1323_, v___x_1324_, v_paramsImpure_1311_);
                if v_isShared_1322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1321_, 1, v___x_1325_);
                    v___x_1327_ = v___x_1321_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_paramsPure_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_letDeclsPure_1312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_letDeclsImpure_1313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_funDeclsPure_1314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 5, v_funDeclsImpure_1315_);
                    v___x_1327_ = v_reuseFailAlloc_1328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1327_;
            }
            7 => {
                v___x_1339_ = 0usize;
                v___x_1340_ = lean_usize_of_nat(v___x_1317_);
                v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseParams_spec__0(v_ps_1267_, v___x_1339_, v___x_1340_, v_paramsImpure_1311_);
                if v_isShared_1338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1341_);
                    v___x_1343_ = v___x_1337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_paramsPure_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_letDeclsPure_1312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_letDeclsImpure_1313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_funDeclsPure_1314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 5, v_funDeclsImpure_1315_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseParams___boxed(
    mut v_pu_1352_: *mut crate::leanh::LeanObject,
    mut v_lctx_1353_: *mut crate::leanh::LeanObject,
    mut v_ps_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1355_ = (crate::leanh::lean_unbox(v_pu_1352_) as u8);
    v_res_1356_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_boxed_1355_, v_lctx_1353_, v_ps_1354_);
    crate::leanh::lean_dec_ref(v_ps_1354_);
    return v_res_1356_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(
    mut v_pu_1357_: u8,
    mut v_lctx_1358_: *mut crate::leanh::LeanObject,
    mut v_decl_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPure_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v_fvarId_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_paramsPure_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v_fvarId_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1357_ == 0 {
                    v_paramsPure_1360_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 0);
                    v_paramsImpure_1361_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 1);
                    v_letDeclsPure_1362_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 2);
                    v_letDeclsImpure_1363_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 3);
                    v_funDeclsPure_1364_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 4);
                    v_funDeclsImpure_1365_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 5);
                    v_isSharedCheck_1374_ = (!crate::leanh::lean_is_exclusive(v_lctx_1358_)) as u8;
                    if v_isSharedCheck_1374_ == 0 {
                        v___x_1367_ = v_lctx_1358_;
                        v_isShared_1368_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1365_);
                        crate::leanh::lean_inc(v_funDeclsPure_1364_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1363_);
                        crate::leanh::lean_inc(v_letDeclsPure_1362_);
                        crate::leanh::lean_inc(v_paramsImpure_1361_);
                        crate::leanh::lean_inc(v_paramsPure_1360_);
                        crate::leanh::lean_dec(v_lctx_1358_);
                        v___x_1367_ = crate::leanh::lean_box(0);
                        v_isShared_1368_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_paramsPure_1375_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 0);
                    v_paramsImpure_1376_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 1);
                    v_letDeclsPure_1377_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 2);
                    v_letDeclsImpure_1378_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 3);
                    v_funDeclsPure_1379_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 4);
                    v_funDeclsImpure_1380_ = crate::leanh::lean_ctor_get(v_lctx_1358_, 5);
                    v_isSharedCheck_1389_ = (!crate::leanh::lean_is_exclusive(v_lctx_1358_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1382_ = v_lctx_1358_;
                        v_isShared_1383_ = v_isSharedCheck_1389_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1380_);
                        crate::leanh::lean_inc(v_funDeclsPure_1379_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1378_);
                        crate::leanh::lean_inc(v_letDeclsPure_1377_);
                        crate::leanh::lean_inc(v_paramsImpure_1376_);
                        crate::leanh::lean_inc(v_paramsPure_1375_);
                        crate::leanh::lean_dec(v_lctx_1358_);
                        v___x_1382_ = crate::leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_1369_ = crate::leanh::lean_ctor_get(v_decl_1359_, 0);
                v___x_1370_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsPure_1362_, v_fvarId_1369_);
                if v_isShared_1368_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1367_, 2, v___x_1370_);
                    v___x_1372_ = v___x_1367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_paramsPure_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_paramsImpure_1361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 2, v___x_1370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_letDeclsImpure_1363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_funDeclsPure_1364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 5, v_funDeclsImpure_1365_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1372_;
            }
            3 => {
                v_fvarId_1384_ = crate::leanh::lean_ctor_get(v_decl_1359_, 0);
                v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_letDeclsImpure_1378_, v_fvarId_1384_);
                if v_isShared_1383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1382_, 3, v___x_1385_);
                    v___x_1387_ = v___x_1382_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_paramsPure_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_paramsImpure_1376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_letDeclsPure_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___x_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_funDeclsPure_1379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 5, v_funDeclsImpure_1380_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseLetDecl___boxed(
    mut v_pu_1390_: *mut crate::leanh::LeanObject,
    mut v_lctx_1391_: *mut crate::leanh::LeanObject,
    mut v_decl_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1393_: u8 = 0;
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1393_ = (crate::leanh::lean_unbox(v_pu_1390_) as u8);
    v_res_1394_ =
        l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_boxed_1393_, v_lctx_1391_, v_decl_1392_);
    crate::leanh::lean_dec_ref(v_decl_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(
    mut v_pu_1395_: u8,
    mut v_lctx_1396_: *mut crate::leanh::LeanObject,
    mut v_decl_1397_: *mut crate::leanh::LeanObject,
    mut v_recursive_1398_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_fvarId_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_1395_ == 0 {
                    v_fvarId_1405_ = crate::leanh::lean_ctor_get(v_decl_1397_, 0);
                    v_paramsPure_1406_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 0);
                    v_paramsImpure_1407_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 1);
                    v_letDeclsPure_1408_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 2);
                    v_letDeclsImpure_1409_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 3);
                    v_funDeclsPure_1410_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 4);
                    v_funDeclsImpure_1411_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 5);
                    v_isSharedCheck_1419_ = (!crate::leanh::lean_is_exclusive(v_lctx_1396_)) as u8;
                    if v_isSharedCheck_1419_ == 0 {
                        v___x_1413_ = v_lctx_1396_;
                        v_isShared_1414_ = v_isSharedCheck_1419_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1411_);
                        crate::leanh::lean_inc(v_funDeclsPure_1410_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1409_);
                        crate::leanh::lean_inc(v_letDeclsPure_1408_);
                        crate::leanh::lean_inc(v_paramsImpure_1407_);
                        crate::leanh::lean_inc(v_paramsPure_1406_);
                        crate::leanh::lean_dec(v_lctx_1396_);
                        v___x_1413_ = crate::leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1419_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_fvarId_1420_ = crate::leanh::lean_ctor_get(v_decl_1397_, 0);
                    v_paramsPure_1421_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 0);
                    v_paramsImpure_1422_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 1);
                    v_letDeclsPure_1423_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 2);
                    v_letDeclsImpure_1424_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 3);
                    v_funDeclsPure_1425_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 4);
                    v_funDeclsImpure_1426_ = crate::leanh::lean_ctor_get(v_lctx_1396_, 5);
                    v_isSharedCheck_1434_ = (!crate::leanh::lean_is_exclusive(v_lctx_1396_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1428_ = v_lctx_1396_;
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_funDeclsImpure_1426_);
                        crate::leanh::lean_inc(v_funDeclsPure_1425_);
                        crate::leanh::lean_inc(v_letDeclsImpure_1424_);
                        crate::leanh::lean_inc(v_letDeclsPure_1423_);
                        crate::leanh::lean_inc(v_paramsImpure_1422_);
                        crate::leanh::lean_inc(v_paramsPure_1421_);
                        crate::leanh::lean_dec(v_lctx_1396_);
                        v___x_1428_ = crate::leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1434_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v_recursive_1398_ == 0 {
                    return v___y_1400_;
                } else {
                    v_params_1401_ = crate::leanh::lean_ctor_get(v_decl_1397_, 2);
                    v_value_1402_ = crate::leanh::lean_ctor_get(v_decl_1397_, 4);
                    v___x_1403_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(
                        v_pu_1395_,
                        v___y_1400_,
                        v_params_1401_,
                    );
                    v___x_1404_ =
                        l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_1395_, v_value_1402_, v___x_1403_);
                    return v___x_1404_;
                }
            }
            2 => {
                v___x_1415_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsPure_1410_, v_fvarId_1405_);
                if v_isShared_1414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1413_, 4, v___x_1415_);
                    v___x_1417_ = v___x_1413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_paramsPure_1406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_paramsImpure_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_letDeclsPure_1408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_letDeclsImpure_1409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 4, v___x_1415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 5, v_funDeclsImpure_1411_);
                    v___x_1417_ = v_reuseFailAlloc_1418_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1400_ = v___x_1417_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(v_funDeclsImpure_1426_, v_fvarId_1420_);
                if v_isShared_1429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1428_, 5, v___x_1430_);
                    v___x_1432_ = v___x_1428_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_paramsPure_1421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_paramsImpure_1422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_letDeclsPure_1423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_letDeclsImpure_1424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_funDeclsPure_1425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 5, v___x_1430_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1400_ = v___x_1432_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseCode(
    mut v_pu_1435_: u8,
    mut v_code_1436_: *mut crate::leanh::LeanObject,
    mut v_lctx_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1436_) {
                0 => {
                    v_decl_1438_ = crate::leanh::lean_ctor_get(v_code_1436_, 0);
                    v_k_1439_ = crate::leanh::lean_ctor_get(v_code_1436_, 1);
                    v___x_1440_ = l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(
                        v_pu_1435_,
                        v_lctx_1437_,
                        v_decl_1438_,
                    );
                    v_code_1436_ = v_k_1439_;
                    v_lctx_1437_ = v___x_1440_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_1442_ = crate::leanh::lean_ctor_get(v_code_1436_, 0);
                    v_k_1443_ = crate::leanh::lean_ctor_get(v_code_1436_, 1);
                    v___x_1444_ = 1;
                    v___x_1445_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(
                        v_pu_1435_,
                        v_lctx_1437_,
                        v_decl_1442_,
                        v___x_1444_,
                    );
                    v_code_1436_ = v_k_1443_;
                    v_lctx_1437_ = v___x_1445_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_decl_1447_ = crate::leanh::lean_ctor_get(v_code_1436_, 0);
                    v_k_1448_ = crate::leanh::lean_ctor_get(v_code_1436_, 1);
                    v___x_1449_ = 1;
                    v___x_1450_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(
                        v_pu_1435_,
                        v_lctx_1437_,
                        v_decl_1447_,
                        v___x_1449_,
                    );
                    v_code_1436_ = v_k_1448_;
                    v_lctx_1437_ = v___x_1450_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_1452_ = crate::leanh::lean_ctor_get(v_code_1436_, 0);
                    v_alts_1453_ = crate::leanh::lean_ctor_get(v_cases_1452_, 3);
                    v___x_1454_ =
                        l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_1435_, v_alts_1453_, v_lctx_1437_);
                    return v___x_1454_;
                }
                7 => {
                    v_k_1455_ = crate::leanh::lean_ctor_get(v_code_1436_, 3);
                    v_code_1436_ = v_k_1455_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_k_1457_ = crate::leanh::lean_ctor_get(v_code_1436_, 3);
                    v_code_1436_ = v_k_1457_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_k_1459_ = crate::leanh::lean_ctor_get(v_code_1436_, 5);
                    v_code_1436_ = v_k_1459_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_k_1461_ = crate::leanh::lean_ctor_get(v_code_1436_, 2);
                    v_code_1436_ = v_k_1461_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_k_1463_ = crate::leanh::lean_ctor_get(v_code_1436_, 2);
                    v_code_1436_ = v_k_1463_;
                    state = 0;
                    continue;
                }
                12 => {
                    v_k_1465_ = crate::leanh::lean_ctor_get(v_code_1436_, 3);
                    v_code_1436_ = v_k_1465_;
                    state = 0;
                    continue;
                }
                13 => {
                    v_k_1467_ = crate::leanh::lean_ctor_get(v_code_1436_, 1);
                    v_code_1436_ = v_k_1467_;
                    state = 0;
                    continue;
                }
                _ => {
                    return v_lctx_1437_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(
    mut v_pu_1469_: u8,
    mut v_as_1470_: *mut crate::leanh::LeanObject,
    mut v_i_1471_: usize,
    mut v_stop_1472_: usize,
    mut v_b_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: usize = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = lean_usize_dec_eq(v_i_1471_, v_stop_1472_);
                if v___x_1479_ == 0 {
                    v___x_1480_ = lean_array_uget_borrowed(v_as_1470_, v_i_1471_);
                    match crate::leanh::lean_obj_tag(v___x_1480_) {
                        0 => {
                            v_params_1481_ = crate::leanh::lean_ctor_get(v___x_1480_, 1);
                            v_code_1482_ = crate::leanh::lean_ctor_get(v___x_1480_, 2);
                            v___x_1483_ = l_Lean_Compiler_LCNF_LCtx_eraseParams(
                                v_pu_1469_,
                                v_b_1473_,
                                v_params_1481_,
                            );
                            v___x_1484_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(
                                v_pu_1469_,
                                v_code_1482_,
                                v___x_1483_,
                            );
                            v___y_1475_ = v___x_1484_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1485_ = crate::leanh::lean_ctor_get(v___x_1480_, 1);
                            v___x_1486_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(
                                v_pu_1469_,
                                v_code_1485_,
                                v_b_1473_,
                            );
                            v___y_1475_ = v___x_1486_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1487_ = crate::leanh::lean_ctor_get(v___x_1480_, 0);
                            v___x_1488_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(
                                v_pu_1469_,
                                v_code_1487_,
                                v_b_1473_,
                            );
                            v___y_1475_ = v___x_1488_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1473_;
                }
            }
            1 => {
                v___x_1476_ = 1usize;
                v___x_1477_ = lean_usize_add(v_i_1471_, v___x_1476_);
                v_i_1471_ = v___x_1477_;
                v_b_1473_ = v___y_1475_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseAlts(
    mut v_pu_1489_: u8,
    mut v_alts_1490_: *mut crate::leanh::LeanObject,
    mut v_lctx_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    v___x_1492_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1493_ = lean_array_get_size(v_alts_1490_);
    v___x_1494_ = lean_nat_dec_lt(v___x_1492_, v___x_1493_);
    if v___x_1494_ == 0 {
        return v_lctx_1491_;
    } else {
        let mut v___x_1495_: u8 = 0;
        v___x_1495_ = lean_nat_dec_le(v___x_1493_, v___x_1493_);
        if v___x_1495_ == 0 {
            if v___x_1494_ == 0 {
                return v_lctx_1491_;
            } else {
                let mut v___x_1496_: usize = 0;
                let mut v___x_1497_: usize = 0;
                let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1496_ = 0usize;
                v___x_1497_ = lean_usize_of_nat(v___x_1493_);
                v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_1489_, v_alts_1490_, v___x_1496_, v___x_1497_, v_lctx_1491_);
                return v___x_1498_;
            }
        } else {
            let mut v___x_1499_: usize = 0;
            let mut v___x_1500_: usize = 0;
            let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1499_ = 0usize;
            v___x_1500_ = lean_usize_of_nat(v___x_1493_);
            v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_1489_, v_alts_1490_, v___x_1499_, v___x_1500_, v_lctx_1491_);
            return v___x_1501_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseAlts___boxed(
    mut v_pu_1502_: *mut crate::leanh::LeanObject,
    mut v_alts_1503_: *mut crate::leanh::LeanObject,
    mut v_lctx_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1505_: u8 = 0;
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1505_ = (crate::leanh::lean_unbox(v_pu_1502_) as u8);
    v_res_1506_ = l_Lean_Compiler_LCNF_LCtx_eraseAlts(v_pu_boxed_1505_, v_alts_1503_, v_lctx_1504_);
    crate::leanh::lean_dec_ref(v_alts_1503_);
    return v_res_1506_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2___boxed(
    mut v_pu_1507_: *mut crate::leanh::LeanObject,
    mut v_as_1508_: *mut crate::leanh::LeanObject,
    mut v_i_1509_: *mut crate::leanh::LeanObject,
    mut v_stop_1510_: *mut crate::leanh::LeanObject,
    mut v_b_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1512_: u8 = 0;
    let mut v_i_boxed_1513_: usize = 0;
    let mut v_stop_boxed_1514_: usize = 0;
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1512_ = (crate::leanh::lean_unbox(v_pu_1507_) as u8);
    v_i_boxed_1513_ = crate::leanh::lean_unbox_usize(v_i_1509_);
    crate::leanh::lean_dec(v_i_1509_);
    v_stop_boxed_1514_ = crate::leanh::lean_unbox_usize(v_stop_1510_);
    crate::leanh::lean_dec(v_stop_1510_);
    v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LCtx_eraseAlts_spec__2(v_pu_boxed_1512_, v_as_1508_, v_i_boxed_1513_, v_stop_boxed_1514_, v_b_1511_);
    crate::leanh::lean_dec_ref(v_as_1508_);
    return v_res_1515_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseFunDecl___boxed(
    mut v_pu_1516_: *mut crate::leanh::LeanObject,
    mut v_lctx_1517_: *mut crate::leanh::LeanObject,
    mut v_decl_1518_: *mut crate::leanh::LeanObject,
    mut v_recursive_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1520_: u8 = 0;
    let mut v_recursive_boxed_1521_: u8 = 0;
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1520_ = (crate::leanh::lean_unbox(v_pu_1516_) as u8);
    v_recursive_boxed_1521_ = (crate::leanh::lean_unbox(v_recursive_1519_) as u8);
    v_res_1522_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(
        v_pu_boxed_1520_,
        v_lctx_1517_,
        v_decl_1518_,
        v_recursive_boxed_1521_,
    );
    crate::leanh::lean_dec_ref(v_decl_1518_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_eraseCode___boxed(
    mut v_pu_1523_: *mut crate::leanh::LeanObject,
    mut v_code_1524_: *mut crate::leanh::LeanObject,
    mut v_lctx_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1526_: u8 = 0;
    let mut v_res_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1526_ = (crate::leanh::lean_unbox(v_pu_1523_) as u8);
    v_res_1527_ = l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_boxed_1526_, v_code_1524_, v_lctx_1525_);
    crate::leanh::lean_dec_ref(v_code_1524_);
    return v_res_1527_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_params(
    mut v_lctx_1528_: *mut crate::leanh::LeanObject,
    mut v_pu_1529_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_pu_1529_ == 0 {
        let mut v_paramsPure_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_paramsPure_1530_ = crate::leanh::lean_ctor_get(v_lctx_1528_, 0);
        crate::leanh::lean_inc_ref(v_paramsPure_1530_);
        return v_paramsPure_1530_;
    } else {
        let mut v_paramsImpure_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_paramsImpure_1531_ = crate::leanh::lean_ctor_get(v_lctx_1528_, 1);
        crate::leanh::lean_inc_ref(v_paramsImpure_1531_);
        return v_paramsImpure_1531_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_params___boxed(
    mut v_lctx_1532_: *mut crate::leanh::LeanObject,
    mut v_pu_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1534_: u8 = 0;
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1534_ = (crate::leanh::lean_unbox(v_pu_1533_) as u8);
    v_res_1535_ = l_Lean_Compiler_LCNF_LCtx_params(v_lctx_1532_, v_pu_boxed_1534_);
    crate::leanh::lean_dec_ref(v_lctx_1532_);
    return v_res_1535_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_letDecls(
    mut v_lctx_1536_: *mut crate::leanh::LeanObject,
    mut v_pu_1537_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_pu_1537_ == 0 {
        let mut v_letDeclsPure_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_letDeclsPure_1538_ = crate::leanh::lean_ctor_get(v_lctx_1536_, 2);
        crate::leanh::lean_inc_ref(v_letDeclsPure_1538_);
        return v_letDeclsPure_1538_;
    } else {
        let mut v_letDeclsImpure_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_letDeclsImpure_1539_ = crate::leanh::lean_ctor_get(v_lctx_1536_, 3);
        crate::leanh::lean_inc_ref(v_letDeclsImpure_1539_);
        return v_letDeclsImpure_1539_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_letDecls___boxed(
    mut v_lctx_1540_: *mut crate::leanh::LeanObject,
    mut v_pu_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1542_: u8 = 0;
    let mut v_res_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1542_ = (crate::leanh::lean_unbox(v_pu_1541_) as u8);
    v_res_1543_ = l_Lean_Compiler_LCNF_LCtx_letDecls(v_lctx_1540_, v_pu_boxed_1542_);
    crate::leanh::lean_dec_ref(v_lctx_1540_);
    return v_res_1543_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_funDecls(
    mut v_lctx_1544_: *mut crate::leanh::LeanObject,
    mut v_pu_1545_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_pu_1545_ == 0 {
        let mut v_funDeclsPure_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_funDeclsPure_1546_ = crate::leanh::lean_ctor_get(v_lctx_1544_, 4);
        crate::leanh::lean_inc_ref(v_funDeclsPure_1546_);
        return v_funDeclsPure_1546_;
    } else {
        let mut v_funDeclsImpure_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_funDeclsImpure_1547_ = crate::leanh::lean_ctor_get(v_lctx_1544_, 5);
        crate::leanh::lean_inc_ref(v_funDeclsImpure_1547_);
        return v_funDeclsImpure_1547_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_funDecls___boxed(
    mut v_lctx_1548_: *mut crate::leanh::LeanObject,
    mut v_pu_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1550_: u8 = 0;
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1550_ = (crate::leanh::lean_unbox(v_pu_1549_) as u8);
    v_res_1551_ = l_Lean_Compiler_LCNF_LCtx_funDecls(v_lctx_1548_, v_pu_boxed_1550_);
    crate::leanh::lean_dec_ref(v_lctx_1548_);
    return v_res_1551_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1552_) == 0 {
                    v___x_1554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1554_, 0, v_a_1553_);
                    return v___x_1554_;
                } else {
                    v_value_1555_ = crate::leanh::lean_ctor_get(v_a_1552_, 1);
                    v_tail_1556_ = crate::leanh::lean_ctor_get(v_a_1552_, 2);
                    v_fvarId_1557_ = crate::leanh::lean_ctor_get(v_value_1555_, 0);
                    v_binderName_1558_ = crate::leanh::lean_ctor_get(v_value_1555_, 1);
                    v_type_1559_ = crate::leanh::lean_ctor_get(v_value_1555_, 3);
                    v___x_1560_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1561_ = 0;
                    v___x_1562_ = 0;
                    crate::leanh::lean_inc_ref(v_type_1559_);
                    crate::leanh::lean_inc(v_binderName_1558_);
                    crate::leanh::lean_inc(v_fvarId_1557_);
                    v___x_1563_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v___x_1560_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 1, v_fvarId_1557_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 2, v_binderName_1558_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 3, v_type_1559_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1563_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_1561_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1563_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_1562_,
                    );
                    v___x_1564_ = l_Lean_LocalContext_addDecl(v_a_1553_, v___x_1563_);
                    v_a_1552_ = v_tail_1556_;
                    v_a_1553_ = v___x_1564_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1___boxed(
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_1566_, v_a_1567_);
    crate::leanh::lean_dec(v_a_1566_);
    return v_res_1568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(
    mut v_as_1569_: *mut crate::leanh::LeanObject,
    mut v_sz_1570_: usize,
    mut v_i_1571_: usize,
    mut v_b_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: u8 = 0;
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: usize = 0;
    let mut v___x_1579_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1573_ = lean_usize_dec_lt(v_i_1571_, v_sz_1570_);
                if v___x_1573_ == 0 {
                    return v_b_1572_;
                } else {
                    v_a_1574_ = lean_array_uget_borrowed(v_as_1569_, v_i_1571_);
                    v___x_1575_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__1(v_a_1574_, v_b_1572_);
                    if crate::leanh::lean_obj_tag(v___x_1575_) == 0 {
                        v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                        crate::leanh::lean_inc(v_a_1576_);
                        crate::leanh::lean_dec_ref_known(v___x_1575_, 1);
                        return v_a_1576_;
                    } else {
                        v_a_1577_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                        crate::leanh::lean_inc(v_a_1577_);
                        crate::leanh::lean_dec_ref_known(v___x_1575_, 1);
                        v___x_1578_ = 1usize;
                        v___x_1579_ = lean_usize_add(v_i_1571_, v___x_1578_);
                        v_i_1571_ = v___x_1579_;
                        v_b_1572_ = v_a_1577_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5___boxed(
    mut v_as_1581_: *mut crate::leanh::LeanObject,
    mut v_sz_1582_: *mut crate::leanh::LeanObject,
    mut v_i_1583_: *mut crate::leanh::LeanObject,
    mut v_b_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1585_: usize = 0;
    let mut v_i_boxed_1586_: usize = 0;
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1585_ = crate::leanh::lean_unbox_usize(v_sz_1582_);
    crate::leanh::lean_dec(v_sz_1582_);
    v_i_boxed_1586_ = crate::leanh::lean_unbox_usize(v_i_1583_);
    crate::leanh::lean_dec(v_i_1583_);
    v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_as_1581_, v_sz_boxed_1585_, v_i_boxed_1586_, v_b_1584_);
    crate::leanh::lean_dec_ref(v_as_1581_);
    return v_res_1587_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(
    mut v_pu_1588_: u8,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1589_) == 0 {
                    v___x_1591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1591_, 0, v_a_1590_);
                    return v___x_1591_;
                } else {
                    v_value_1592_ = crate::leanh::lean_ctor_get(v_a_1589_, 1);
                    crate::leanh::lean_inc(v_value_1592_);
                    v_tail_1593_ = crate::leanh::lean_ctor_get(v_a_1589_, 2);
                    crate::leanh::lean_inc(v_tail_1593_);
                    crate::leanh::lean_dec_ref_known(v_a_1589_, 3);
                    v_fvarId_1594_ = crate::leanh::lean_ctor_get(v_value_1592_, 0);
                    crate::leanh::lean_inc(v_fvarId_1594_);
                    v_binderName_1595_ = crate::leanh::lean_ctor_get(v_value_1592_, 1);
                    crate::leanh::lean_inc(v_binderName_1595_);
                    v_type_1596_ = crate::leanh::lean_ctor_get(v_value_1592_, 2);
                    crate::leanh::lean_inc_ref(v_type_1596_);
                    v_value_1597_ = crate::leanh::lean_ctor_get(v_value_1592_, 3);
                    crate::leanh::lean_inc(v_value_1597_);
                    crate::leanh::lean_dec(v_value_1592_);
                    v___x_1598_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1599_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v_pu_1588_, v_value_1597_);
                    v___x_1600_ = 1;
                    v___x_1601_ = 0;
                    v___x_1602_ = crate::leanh::lean_alloc_ctor(1, 5, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1602_, 0, v___x_1598_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 1, v_fvarId_1594_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 2, v_binderName_1595_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 3, v_type_1596_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 4, v___x_1599_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1602_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v___x_1600_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1602_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                        v___x_1601_,
                    );
                    v___x_1603_ = l_Lean_LocalContext_addDecl(v_a_1590_, v___x_1602_);
                    v_a_1589_ = v_tail_1593_;
                    v_a_1590_ = v___x_1603_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0___boxed(
    mut v_pu_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1608_: u8 = 0;
    let mut v_res_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1608_ = (crate::leanh::lean_unbox(v_pu_1605_) as u8);
    v_res_1609_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_boxed_1608_, v_a_1606_, v_a_1607_);
    return v_res_1609_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(
    mut v_pu_1610_: u8,
    mut v_as_1611_: *mut crate::leanh::LeanObject,
    mut v_sz_1612_: usize,
    mut v_i_1613_: usize,
    mut v_b_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: u8 = 0;
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: usize = 0;
    let mut v___x_1621_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1615_ = lean_usize_dec_lt(v_i_1613_, v_sz_1612_);
                if v___x_1615_ == 0 {
                    return v_b_1614_;
                } else {
                    v_a_1616_ = lean_array_uget_borrowed(v_as_1611_, v_i_1613_);
                    crate::leanh::lean_inc(v_a_1616_);
                    v___x_1617_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__0(v_pu_1610_, v_a_1616_, v_b_1614_);
                    if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                        v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        crate::leanh::lean_inc(v_a_1618_);
                        crate::leanh::lean_dec_ref_known(v___x_1617_, 1);
                        return v_a_1618_;
                    } else {
                        v_a_1619_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        crate::leanh::lean_inc(v_a_1619_);
                        crate::leanh::lean_dec_ref_known(v___x_1617_, 1);
                        v___x_1620_ = 1usize;
                        v___x_1621_ = lean_usize_add(v_i_1613_, v___x_1620_);
                        v_i_1613_ = v___x_1621_;
                        v_b_1614_ = v_a_1619_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4___boxed(
    mut v_pu_1623_: *mut crate::leanh::LeanObject,
    mut v_as_1624_: *mut crate::leanh::LeanObject,
    mut v_sz_1625_: *mut crate::leanh::LeanObject,
    mut v_i_1626_: *mut crate::leanh::LeanObject,
    mut v_b_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1628_: u8 = 0;
    let mut v_sz_boxed_1629_: usize = 0;
    let mut v_i_boxed_1630_: usize = 0;
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1628_ = (crate::leanh::lean_unbox(v_pu_1623_) as u8);
    v_sz_boxed_1629_ = crate::leanh::lean_unbox_usize(v_sz_1625_);
    crate::leanh::lean_dec(v_sz_1625_);
    v_i_boxed_1630_ = crate::leanh::lean_unbox_usize(v_i_1626_);
    crate::leanh::lean_dec(v_i_1626_);
    v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_boxed_1628_, v_as_1624_, v_sz_boxed_1629_, v_i_boxed_1630_, v_b_1627_);
    crate::leanh::lean_dec_ref(v_as_1624_);
    return v_res_1631_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1632_) == 0 {
                    v___x_1634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1634_, 0, v_a_1633_);
                    return v___x_1634_;
                } else {
                    v_value_1635_ = crate::leanh::lean_ctor_get(v_a_1632_, 1);
                    v_tail_1636_ = crate::leanh::lean_ctor_get(v_a_1632_, 2);
                    v_fvarId_1637_ = crate::leanh::lean_ctor_get(v_value_1635_, 0);
                    v_binderName_1638_ = crate::leanh::lean_ctor_get(v_value_1635_, 1);
                    v_type_1639_ = crate::leanh::lean_ctor_get(v_value_1635_, 2);
                    v___x_1640_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1641_ = 0;
                    v___x_1642_ = 0;
                    crate::leanh::lean_inc_ref(v_type_1639_);
                    crate::leanh::lean_inc(v_binderName_1638_);
                    crate::leanh::lean_inc(v_fvarId_1637_);
                    v___x_1643_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1640_);
                    crate::leanh::lean_ctor_set(v___x_1643_, 1, v_fvarId_1637_);
                    crate::leanh::lean_ctor_set(v___x_1643_, 2, v_binderName_1638_);
                    crate::leanh::lean_ctor_set(v___x_1643_, 3, v_type_1639_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1643_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_1641_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1643_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_1642_,
                    );
                    v___x_1644_ = l_Lean_LocalContext_addDecl(v_a_1633_, v___x_1643_);
                    v_a_1632_ = v_tail_1636_;
                    v_a_1633_ = v___x_1644_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2___boxed(
    mut v_a_1646_: *mut crate::leanh::LeanObject,
    mut v_a_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_1646_, v_a_1647_);
    crate::leanh::lean_dec(v_a_1646_);
    return v_res_1648_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(
    mut v_as_1649_: *mut crate::leanh::LeanObject,
    mut v_sz_1650_: usize,
    mut v_i_1651_: usize,
    mut v_b_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: u8 = 0;
    let mut v_a_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: usize = 0;
    let mut v___x_1659_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1653_ = lean_usize_dec_lt(v_i_1651_, v_sz_1650_);
                if v___x_1653_ == 0 {
                    return v_b_1652_;
                } else {
                    v_a_1654_ = lean_array_uget_borrowed(v_as_1649_, v_i_1651_);
                    v___x_1655_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__2(v_a_1654_, v_b_1652_);
                    if crate::leanh::lean_obj_tag(v___x_1655_) == 0 {
                        v_a_1656_ = crate::leanh::lean_ctor_get(v___x_1655_, 0);
                        crate::leanh::lean_inc(v_a_1656_);
                        crate::leanh::lean_dec_ref_known(v___x_1655_, 1);
                        return v_a_1656_;
                    } else {
                        v_a_1657_ = crate::leanh::lean_ctor_get(v___x_1655_, 0);
                        crate::leanh::lean_inc(v_a_1657_);
                        crate::leanh::lean_dec_ref_known(v___x_1655_, 1);
                        v___x_1658_ = 1usize;
                        v___x_1659_ = lean_usize_add(v_i_1651_, v___x_1658_);
                        v_i_1651_ = v___x_1659_;
                        v_b_1652_ = v_a_1657_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3___boxed(
    mut v_as_1661_: *mut crate::leanh::LeanObject,
    mut v_sz_1662_: *mut crate::leanh::LeanObject,
    mut v_i_1663_: *mut crate::leanh::LeanObject,
    mut v_b_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1665_: usize = 0;
    let mut v_i_boxed_1666_: usize = 0;
    let mut v_res_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1665_ = crate::leanh::lean_unbox_usize(v_sz_1662_);
    crate::leanh::lean_dec(v_sz_1662_);
    v_i_boxed_1666_ = crate::leanh::lean_unbox_usize(v_i_1663_);
    crate::leanh::lean_dec(v_i_1663_);
    v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_as_1661_, v_sz_boxed_1665_, v_i_boxed_1666_, v_b_1664_);
    crate::leanh::lean_dec_ref(v_as_1661_);
    return v_res_1667_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1668_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0_once),
        _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__0,
    );
    v___x_1670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1672_ = lean_mk_empty_array_with_capacity(v___x_1671_);
    v___x_1673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1673_, 0, v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = 5usize;
    v___x_1675_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1676_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1677_ = lean_mk_empty_array_with_capacity(v___x_1676_);
    v___x_1678_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2_once),
        _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__2,
    );
    v___x_1679_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1678_);
    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1677_);
    crate::leanh::lean_ctor_set(v___x_1679_, 2, v___x_1675_);
    crate::leanh::lean_ctor_set(v___x_1679_, 3, v___x_1675_);
    crate::leanh::lean_ctor_set_usize(v___x_1679_, 4, v___x_1674_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = crate::leanh::lean_box(1);
    v___x_1681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3_once),
        _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__3,
    );
    v___x_1682_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1_once),
        _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__1,
    );
    v_result_1683_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v_result_1683_, 0, v___x_1682_);
    crate::leanh::lean_ctor_set(v_result_1683_, 1, v___x_1681_);
    crate::leanh::lean_ctor_set(v_result_1683_, 2, v___x_1680_);
    return v_result_1683_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_toLocalContext(
    mut v_lctx_1684_: *mut crate::leanh::LeanObject,
    mut v_pu_1685_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: usize = 0;
    let mut v___y_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1691_: usize = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1695_: usize = 0;
    let mut v___y_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1698_: usize = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1706_: usize = 0;
    let mut v___x_1707_: usize = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_1702_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4_once
                    ),
                    _init_l_Lean_Compiler_LCNF_LCtx_toLocalContext___closed__4,
                );
                if v_pu_1685_ == 0 {
                    v_paramsPure_1711_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 0);
                    v___y_1704_ = v_paramsPure_1711_;
                    state = 3;
                    continue;
                } else {
                    v_paramsImpure_1712_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 1);
                    v___y_1704_ = v_paramsImpure_1712_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_buckets_1690_ = crate::leanh::lean_ctor_get(v___y_1689_, 1);
                v_sz_1691_ = lean_array_size(v_buckets_1690_);
                v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__5(v_buckets_1690_, v_sz_1691_, v___y_1688_, v___y_1687_);
                return v___x_1692_;
            }
            2 => {
                v_buckets_1697_ = crate::leanh::lean_ctor_get(v___y_1696_, 1);
                v_sz_1698_ = lean_array_size(v_buckets_1697_);
                v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__4(v_pu_1685_, v_buckets_1697_, v_sz_1698_, v___y_1695_, v___y_1694_);
                if v_pu_1685_ == 0 {
                    v_funDeclsPure_1700_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 4);
                    v___y_1687_ = v___x_1699_;
                    v___y_1688_ = v___y_1695_;
                    v___y_1689_ = v_funDeclsPure_1700_;
                    state = 1;
                    continue;
                } else {
                    v_funDeclsImpure_1701_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 5);
                    v___y_1687_ = v___x_1699_;
                    v___y_1688_ = v___y_1695_;
                    v___y_1689_ = v_funDeclsImpure_1701_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_buckets_1705_ = crate::leanh::lean_ctor_get(v___y_1704_, 1);
                v_sz_1706_ = lean_array_size(v_buckets_1705_);
                v___x_1707_ = 0usize;
                v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_LCtx_toLocalContext_spec__3(v_buckets_1705_, v_sz_1706_, v___x_1707_, v_result_1702_);
                if v_pu_1685_ == 0 {
                    v_letDeclsPure_1709_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 2);
                    v___y_1694_ = v___x_1708_;
                    v___y_1695_ = v___x_1707_;
                    v___y_1696_ = v_letDeclsPure_1709_;
                    state = 2;
                    continue;
                } else {
                    v_letDeclsImpure_1710_ = crate::leanh::lean_ctor_get(v_lctx_1684_, 3);
                    v___y_1694_ = v___x_1708_;
                    v___y_1695_ = v___x_1707_;
                    v___y_1696_ = v_letDeclsImpure_1710_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LCtx_toLocalContext___boxed(
    mut v_lctx_1713_: *mut crate::leanh::LeanObject,
    mut v_pu_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1715_: u8 = 0;
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1715_ = (crate::leanh::lean_unbox(v_pu_1714_) as u8);
    v_res_1716_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1713_, v_pu_boxed_1715_);
    crate::leanh::lean_dec_ref(v_lctx_1713_);
    return v_res_1716_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_LCtx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedLCtx_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedLCtx_default();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLCtx_default);
    l_Lean_Compiler_LCNF_instInhabitedLCtx = _init_l_Lean_Compiler_LCNF_instInhabitedLCtx();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLCtx);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_LCtx(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_LCtx(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_LCtx(builtin);
}
