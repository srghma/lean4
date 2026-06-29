// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.TheoremsLookup
// Imports: Lean.Meta.Sym.Simp.Theorems Lean.Meta.Match.MatchEqsExt Lean.Meta.Eqns
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_getEqnsFor_x3f, l_Lean_Meta_getUnfoldEqnFor_x3f,
    runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::Match::MatchEqsExt::{
    initialize_Lean_Meta_Match_MatchEqsExt, runtime_initialize_Lean_Meta_Match_MatchEqsExt,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems, l_Lean_Meta_Sym_Simp_Theorems_insert,
    l_Lean_Meta_Sym_Simp_mkTheoremFromDecl, runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_get_match_equations_for;
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(
    mut v_as_761_: *mut crate::leanh::LeanObject,
    mut v_i_762_: usize,
    mut v_stop_763_: usize,
    mut v_b_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_765_ = lean_usize_dec_eq(v_i_762_, v_stop_763_);
                if v___x_765_ == 0 {
                    v___x_766_ = lean_array_uget_borrowed(v_as_761_, v_i_762_);
                    crate::leanh::lean_inc(v___x_766_);
                    v___x_767_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_764_, v___x_766_);
                    v___x_768_ = 1usize;
                    v___x_769_ = lean_usize_add(v_i_762_, v___x_768_);
                    v_i_762_ = v___x_769_;
                    v_b_764_ = v___x_767_;
                    state = 0;
                    continue;
                } else {
                    return v_b_764_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0___boxed(
    mut v_as_771_: *mut crate::leanh::LeanObject,
    mut v_i_772_: *mut crate::leanh::LeanObject,
    mut v_stop_773_: *mut crate::leanh::LeanObject,
    mut v_b_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_775_: usize = 0;
    let mut v_stop_boxed_776_: usize = 0;
    let mut v_res_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_775_ = crate::leanh::lean_unbox_usize(v_i_772_);
    crate::leanh::lean_dec(v_i_772_);
    v_stop_boxed_776_ = crate::leanh::lean_unbox_usize(v_stop_773_);
    crate::leanh::lean_dec(v_stop_773_);
    v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_as_771_, v_i_boxed_775_, v_stop_boxed_776_, v_b_774_);
    crate::leanh::lean_dec_ref(v_as_771_);
    return v_res_777_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(
    mut v_thms_778_: *mut crate::leanh::LeanObject,
    mut v_toInsert_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    v___x_780_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_781_ = lean_array_get_size(v_toInsert_779_);
    v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
    if v___x_782_ == 0 {
        return v_thms_778_;
    } else {
        let mut v___x_783_: u8 = 0;
        v___x_783_ = lean_nat_dec_le(v___x_781_, v___x_781_);
        if v___x_783_ == 0 {
            if v___x_782_ == 0 {
                return v_thms_778_;
            } else {
                let mut v___x_784_: usize = 0;
                let mut v___x_785_: usize = 0;
                let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_784_ = 0usize;
                v___x_785_ = lean_usize_of_nat(v___x_781_);
                v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_toInsert_779_, v___x_784_, v___x_785_, v_thms_778_);
                return v___x_786_;
            }
        } else {
            let mut v___x_787_: usize = 0;
            let mut v___x_788_: usize = 0;
            let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_787_ = 0usize;
            v___x_788_ = lean_usize_of_nat(v___x_781_);
            v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_toInsert_779_, v___x_787_, v___x_788_, v_thms_778_);
            return v___x_789_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany___boxed(
    mut v_thms_790_: *mut crate::leanh::LeanObject,
    mut v_toInsert_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_792_ =
        l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(
            v_thms_790_,
            v_toInsert_791_,
        );
    crate::leanh::lean_dec_ref(v_toInsert_791_);
    return v_res_792_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_793_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0,
    );
    v___x_795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_795_, 0, v___x_794_);
    return v___x_795_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1,
    );
    v___x_797_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
    crate::leanh::lean_ctor_set(v___x_797_, 1, v___x_796_);
    crate::leanh::lean_ctor_set(v___x_797_, 2, v___x_796_);
    return v___x_797_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2,
    );
    return v___x_798_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(
    mut v___x_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_802_, 0, v___x_800_);
    return v___x_802_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(
    mut v___x_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(v___x_803_);
    return v_res_805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2,
    );
    v___f_807_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_807_, 0, v___x_806_);
    return v___f_807_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_);
    v___x_810_ = crate::leanh::lean_box(0);
    v___x_811_ = crate::leanh::lean_box(1);
    v___x_812_ = l_Lean_registerEnvExtension___redArg(v___f_809_, v___x_810_, v___x_811_);
    return v___x_812_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(
    mut v_a_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_();
    return v_res_814_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(
    mut v_x_815_: *mut crate::leanh::LeanObject,
    mut v_x_816_: *mut crate::leanh::LeanObject,
    mut v_x_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_819_ = crate::leanh::lean_ctor_get(v_x_815_, 0);
                v_vs_820_ = crate::leanh::lean_ctor_get(v_x_815_, 1);
                v_isSharedCheck_844_ = (!crate::leanh::lean_is_exclusive(v_x_815_)) as u8;
                if v_isSharedCheck_844_ == 0 {
                    v___x_822_ = v_x_815_;
                    v_isShared_823_ = v_isSharedCheck_844_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_820_);
                    crate::leanh::lean_inc(v_ks_819_);
                    crate::leanh::lean_dec(v_x_815_);
                    v___x_822_ = crate::leanh::lean_box(0);
                    v_isShared_823_ = v_isSharedCheck_844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_824_ = lean_array_get_size(v_ks_819_);
                v___x_825_ = lean_nat_dec_lt(v_x_816_, v___x_824_);
                if v___x_825_ == 0 {
                    crate::leanh::lean_dec(v_x_816_);
                    v___x_826_ = lean_array_push(v_ks_819_, v_x_817_);
                    v___x_827_ = lean_array_push(v_vs_820_, v_x_818_);
                    if v_isShared_823_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_822_, 1, v___x_827_);
                        crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_826_);
                        v___x_829_ = v___x_822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_830_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_827_);
                        v___x_829_ = v_reuseFailAlloc_830_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_831_ = lean_array_fget_borrowed(v_ks_819_, v_x_816_);
                    v___x_832_ = lean_name_eq(v_x_817_, v_k_x27_831_);
                    if v___x_832_ == 0 {
                        if v_isShared_823_ == 0 {
                            v___x_834_ = v___x_822_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_ks_819_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 1, v_vs_820_);
                            v___x_834_ = v_reuseFailAlloc_838_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_839_ = lean_array_fset(v_ks_819_, v_x_816_, v_x_817_);
                        v___x_840_ = lean_array_fset(v_vs_820_, v_x_816_, v_x_818_);
                        crate::leanh::lean_dec(v_x_816_);
                        if v_isShared_823_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_822_, 1, v___x_840_);
                            crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_839_);
                            v___x_842_ = v___x_822_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_843_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_839_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_840_);
                            v___x_842_ = v_reuseFailAlloc_843_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_829_;
            }
            3 => {
                v___x_835_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_836_ = lean_nat_add(v_x_816_, v___x_835_);
                crate::leanh::lean_dec(v_x_816_);
                v_x_815_ = v___x_834_;
                v_x_816_ = v___x_836_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(
    mut v_n_845_: *mut crate::leanh::LeanObject,
    mut v_k_846_: *mut crate::leanh::LeanObject,
    mut v_v_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_849_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_n_845_, v___x_848_, v_k_846_, v_v_847_);
    return v___x_849_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u64 = 0;
    v___x_850_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_851_ = lean_uint64_of_nat(v___x_850_);
    return v___x_851_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_852_: usize = 0;
    let mut v___x_853_: usize = 0;
    let mut v___x_854_: usize = 0;
    v___x_852_ = 5usize;
    v___x_853_ = 1usize;
    v___x_854_ = lean_usize_shift_left(v___x_853_, v___x_852_);
    return v___x_854_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_855_: usize = 0;
    let mut v___x_856_: usize = 0;
    let mut v___x_857_: usize = 0;
    v___x_855_ = 1usize;
    v___x_856_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0);
    v___x_857_ = lean_usize_sub(v___x_856_, v___x_855_);
    return v___x_857_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_858_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(
    mut v_x_859_: *mut crate::leanh::LeanObject,
    mut v_x_860_: usize,
    mut v_x_861_: usize,
    mut v_x_862_: *mut crate::leanh::LeanObject,
    mut v_x_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: usize = 0;
    let mut v___x_866_: usize = 0;
    let mut v___x_867_: usize = 0;
    let mut v___x_868_: usize = 0;
    let mut v_j_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v_v_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_node_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_901_: usize = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_906_: u8 = 0;
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_919_: u8 = 0;
    let mut v_ks_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: u8 = 0;
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v_reuseFailAlloc_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_859_) == 0 {
                    v_es_864_ = crate::leanh::lean_ctor_get(v_x_859_, 0);
                    v___x_865_ = 5usize;
                    v___x_866_ = 1usize;
                    v___x_867_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1);
                    v___x_868_ = lean_usize_land(v_x_860_, v___x_867_);
                    v_j_869_ = lean_usize_to_nat(v___x_868_);
                    v___x_870_ = lean_array_get_size(v_es_864_);
                    v___x_871_ = lean_nat_dec_lt(v_j_869_, v___x_870_);
                    if v___x_871_ == 0 {
                        crate::leanh::lean_dec(v_j_869_);
                        crate::leanh::lean_dec(v_x_863_);
                        crate::leanh::lean_dec(v_x_862_);
                        return v_x_859_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_864_);
                        v_isSharedCheck_908_ = (!crate::leanh::lean_is_exclusive(v_x_859_)) as u8;
                        if v_isSharedCheck_908_ == 0 {
                            v_unused_909_ = crate::leanh::lean_ctor_get(v_x_859_, 0);
                            crate::leanh::lean_dec(v_unused_909_);
                            v___x_873_ = v_x_859_;
                            v_isShared_874_ = v_isSharedCheck_908_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_859_);
                            v___x_873_ = crate::leanh::lean_box(0);
                            v_isShared_874_ = v_isSharedCheck_908_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_910_ = crate::leanh::lean_ctor_get(v_x_859_, 0);
                    v_vs_911_ = crate::leanh::lean_ctor_get(v_x_859_, 1);
                    v_isSharedCheck_931_ = (!crate::leanh::lean_is_exclusive(v_x_859_)) as u8;
                    if v_isSharedCheck_931_ == 0 {
                        v___x_913_ = v_x_859_;
                        v_isShared_914_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_911_);
                        crate::leanh::lean_inc(v_ks_910_);
                        crate::leanh::lean_dec(v_x_859_);
                        v___x_913_ = crate::leanh::lean_box(0);
                        v_isShared_914_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_875_ = lean_array_fget(v_es_864_, v_j_869_);
                v___x_876_ = crate::leanh::lean_box(0);
                v_xs_x27_877_ = lean_array_fset(v_es_864_, v_j_869_, v___x_876_);
                match crate::leanh::lean_obj_tag(v_v_875_) {
                    0 => {
                        v_key_884_ = crate::leanh::lean_ctor_get(v_v_875_, 0);
                        v_val_885_ = crate::leanh::lean_ctor_get(v_v_875_, 1);
                        v_isSharedCheck_895_ = (!crate::leanh::lean_is_exclusive(v_v_875_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_887_ = v_v_875_;
                            v_isShared_888_ = v_isSharedCheck_895_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_885_);
                            crate::leanh::lean_inc(v_key_884_);
                            crate::leanh::lean_dec(v_v_875_);
                            v___x_887_ = crate::leanh::lean_box(0);
                            v_isShared_888_ = v_isSharedCheck_895_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_896_ = crate::leanh::lean_ctor_get(v_v_875_, 0);
                        v_isSharedCheck_906_ = (!crate::leanh::lean_is_exclusive(v_v_875_)) as u8;
                        if v_isSharedCheck_906_ == 0 {
                            v___x_898_ = v_v_875_;
                            v_isShared_899_ = v_isSharedCheck_906_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_896_);
                            crate::leanh::lean_dec(v_v_875_);
                            v___x_898_ = crate::leanh::lean_box(0);
                            v_isShared_899_ = v_isSharedCheck_906_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_907_, 0, v_x_862_);
                        crate::leanh::lean_ctor_set(v___x_907_, 1, v_x_863_);
                        v___y_879_ = v___x_907_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_880_ = lean_array_fset(v_xs_x27_877_, v_j_869_, v___y_879_);
                crate::leanh::lean_dec(v_j_869_);
                if v_isShared_874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_880_);
                    v___x_882_ = v___x_873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_882_;
            }
            4 => {
                v___x_889_ = lean_name_eq(v_x_862_, v_key_884_);
                if v___x_889_ == 0 {
                    crate::leanh::lean_del_object(v___x_887_);
                    v___x_890_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_884_, v_val_885_, v_x_862_, v_x_863_,
                    );
                    v___x_891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_891_, 0, v___x_890_);
                    v___y_879_ = v___x_891_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_885_);
                    crate::leanh::lean_dec(v_key_884_);
                    if v_isShared_888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_887_, 1, v_x_863_);
                        crate::leanh::lean_ctor_set(v___x_887_, 0, v_x_862_);
                        v___x_893_ = v___x_887_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_894_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_x_862_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 1, v_x_863_);
                        v___x_893_ = v_reuseFailAlloc_894_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_879_ = v___x_893_;
                state = 2;
                continue;
            }
            6 => {
                v___x_900_ = lean_usize_shift_right(v_x_860_, v___x_865_);
                v___x_901_ = lean_usize_add(v_x_861_, v___x_866_);
                v___x_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_node_896_, v___x_900_, v___x_901_, v_x_862_, v_x_863_);
                if v_isShared_899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_898_, 0, v___x_902_);
                    v___x_904_ = v___x_898_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
                    v___x_904_ = v_reuseFailAlloc_905_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_879_ = v___x_904_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_914_ == 0 {
                    v___x_916_ = v___x_913_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_930_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_930_, 0, v_ks_910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_930_, 1, v_vs_911_);
                    v___x_916_ = v_reuseFailAlloc_930_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_917_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v___x_916_, v_x_862_, v_x_863_);
                v___x_925_ = 7usize;
                v___x_926_ = lean_usize_dec_le(v___x_925_, v_x_861_);
                if v___x_926_ == 0 {
                    v___x_927_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_917_);
                    v___x_928_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
                    crate::leanh::lean_dec(v___x_927_);
                    v___y_919_ = v___x_929_;
                    state = 10;
                    continue;
                } else {
                    v___y_919_ = v___x_926_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_919_ == 0 {
                    v_ks_920_ = crate::leanh::lean_ctor_get(v_newNode_917_, 0);
                    crate::leanh::lean_inc_ref(v_ks_920_);
                    v_vs_921_ = crate::leanh::lean_ctor_get(v_newNode_917_, 1);
                    crate::leanh::lean_inc_ref(v_vs_921_);
                    crate::leanh::lean_dec_ref(v_newNode_917_);
                    v___x_922_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2);
                    v___x_924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_x_861_, v_ks_920_, v_vs_921_, v___x_922_, v___x_923_);
                    crate::leanh::lean_dec_ref(v_vs_921_);
                    crate::leanh::lean_dec_ref(v_ks_920_);
                    return v___x_924_;
                } else {
                    return v_newNode_917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(
    mut v_depth_932_: usize,
    mut v_keys_933_: *mut crate::leanh::LeanObject,
    mut v_vals_934_: *mut crate::leanh::LeanObject,
    mut v_i_935_: *mut crate::leanh::LeanObject,
    mut v_entries_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut v_k_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_942_: u64 = 0;
    let mut v_h_943_: usize = 0;
    let mut v___x_944_: usize = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: usize = 0;
    let mut v___x_947_: usize = 0;
    let mut v___x_948_: usize = 0;
    let mut v_h_949_: usize = 0;
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: u64 = 0;
    let mut v_hash_954_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_937_ = lean_array_get_size(v_keys_933_);
                v___x_938_ = lean_nat_dec_lt(v_i_935_, v___x_937_);
                if v___x_938_ == 0 {
                    crate::leanh::lean_dec(v_i_935_);
                    return v_entries_936_;
                } else {
                    v_k_939_ = lean_array_fget_borrowed(v_keys_933_, v_i_935_);
                    v_v_940_ = lean_array_fget_borrowed(v_vals_934_, v_i_935_);
                    if crate::leanh::lean_obj_tag(v_k_939_) == 0 {
                        v___x_953_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
                        v___y_942_ = v___x_953_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_954_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_939_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_942_ = v_hash_954_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_943_ = lean_uint64_to_usize(v___y_942_);
                v___x_944_ = 5usize;
                v___x_945_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_946_ = 1usize;
                v___x_947_ = lean_usize_sub(v_depth_932_, v___x_946_);
                v___x_948_ = lean_usize_mul(v___x_944_, v___x_947_);
                v_h_949_ = lean_usize_shift_right(v_h_943_, v___x_948_);
                v___x_950_ = lean_nat_add(v_i_935_, v___x_945_);
                crate::leanh::lean_dec(v_i_935_);
                crate::leanh::lean_inc(v_v_940_);
                crate::leanh::lean_inc(v_k_939_);
                v___x_951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_entries_936_, v_h_949_, v_depth_932_, v_k_939_, v_v_940_);
                v_i_935_ = v___x_950_;
                v_entries_936_ = v___x_951_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_depth_955_: *mut crate::leanh::LeanObject,
    mut v_keys_956_: *mut crate::leanh::LeanObject,
    mut v_vals_957_: *mut crate::leanh::LeanObject,
    mut v_i_958_: *mut crate::leanh::LeanObject,
    mut v_entries_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_960_: usize = 0;
    let mut v_res_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_960_ = crate::leanh::lean_unbox_usize(v_depth_955_);
    crate::leanh::lean_dec(v_depth_955_);
    v_res_961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_boxed_960_, v_keys_956_, v_vals_957_, v_i_958_, v_entries_959_);
    crate::leanh::lean_dec_ref(v_vals_957_);
    crate::leanh::lean_dec_ref(v_keys_956_);
    return v_res_961_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___boxed(
    mut v_x_962_: *mut crate::leanh::LeanObject,
    mut v_x_963_: *mut crate::leanh::LeanObject,
    mut v_x_964_: *mut crate::leanh::LeanObject,
    mut v_x_965_: *mut crate::leanh::LeanObject,
    mut v_x_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2201__boxed_967_: usize = 0;
    let mut v_x_2202__boxed_968_: usize = 0;
    let mut v_res_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2201__boxed_967_ = crate::leanh::lean_unbox_usize(v_x_963_);
    crate::leanh::lean_dec(v_x_963_);
    v_x_2202__boxed_968_ = crate::leanh::lean_unbox_usize(v_x_964_);
    crate::leanh::lean_dec(v_x_964_);
    v_res_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_962_, v_x_2201__boxed_967_, v_x_2202__boxed_968_, v_x_965_, v_x_966_);
    return v_res_969_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(
    mut v_x_970_: *mut crate::leanh::LeanObject,
    mut v_x_971_: *mut crate::leanh::LeanObject,
    mut v_x_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_974_: u64 = 0;
    let mut v___x_975_: usize = 0;
    let mut v___x_976_: usize = 0;
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u64 = 0;
    let mut v_hash_979_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_971_) == 0 {
                    v___x_978_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
                    v___y_974_ = v___x_978_;
                    state = 1;
                    continue;
                } else {
                    v_hash_979_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_971_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_974_ = v_hash_979_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_975_ = lean_uint64_to_usize(v___y_974_);
                v___x_976_ = 1usize;
                v___x_977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_970_, v___x_975_, v___x_976_, v_x_971_, v_x_972_);
                return v___x_977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0(
    mut v_fnName_980_: *mut crate::leanh::LeanObject,
    mut v___x_981_: *mut crate::leanh::LeanObject,
    mut v_cache_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eqnTheorems_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldTheorems_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchTheorems_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eqnTheorems_983_ = crate::leanh::lean_ctor_get(v_cache_982_, 0);
                v_unfoldTheorems_984_ = crate::leanh::lean_ctor_get(v_cache_982_, 1);
                v_matchTheorems_985_ = crate::leanh::lean_ctor_get(v_cache_982_, 2);
                v_isSharedCheck_993_ = (!crate::leanh::lean_is_exclusive(v_cache_982_)) as u8;
                if v_isSharedCheck_993_ == 0 {
                    v___x_987_ = v_cache_982_;
                    v_isShared_988_ = v_isSharedCheck_993_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_matchTheorems_985_);
                    crate::leanh::lean_inc(v_unfoldTheorems_984_);
                    crate::leanh::lean_inc(v_eqnTheorems_983_);
                    crate::leanh::lean_dec(v_cache_982_);
                    v___x_987_ = crate::leanh::lean_box(0);
                    v_isShared_988_ = v_isSharedCheck_993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_989_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_eqnTheorems_983_, v_fnName_980_, v___x_981_);
                if v_isShared_988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_989_);
                    v___x_991_ = v___x_987_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_992_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 1, v_unfoldTheorems_984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 2, v_matchTheorems_985_);
                    v___x_991_ = v_reuseFailAlloc_992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(
    mut v_sz_994_: usize,
    mut v_i_995_: usize,
    mut v_bs_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: usize = 0;
    let mut v___x_1010_: usize = 0;
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1016_: u8 = 0;
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1002_ = lean_usize_dec_lt(v_i_995_, v_sz_994_);
                if v___x_1002_ == 0 {
                    v___x_1003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1003_, 0, v_bs_996_);
                    return v___x_1003_;
                } else {
                    v_v_1004_ = lean_array_uget_borrowed(v_bs_996_, v_i_995_);
                    crate::leanh::lean_inc(v_v_1004_);
                    v___x_1005_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                        v_v_1004_,
                        v___y_997_,
                        v___y_998_,
                        v___y_999_,
                        v___y_1000_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1005_) == 0 {
                        v_a_1006_ = crate::leanh::lean_ctor_get(v___x_1005_, 0);
                        crate::leanh::lean_inc(v_a_1006_);
                        crate::leanh::lean_dec_ref_known(v___x_1005_, 1);
                        v___x_1007_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1008_ = lean_array_uset(v_bs_996_, v_i_995_, v___x_1007_);
                        v___x_1009_ = 1usize;
                        v___x_1010_ = lean_usize_add(v_i_995_, v___x_1009_);
                        v___x_1011_ = lean_array_uset(v_bs_x27_1008_, v_i_995_, v_a_1006_);
                        v_i_995_ = v___x_1010_;
                        v_bs_996_ = v___x_1011_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_996_);
                        v_a_1013_ = crate::leanh::lean_ctor_get(v___x_1005_, 0);
                        v_isSharedCheck_1020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1005_)) as u8;
                        if v_isSharedCheck_1020_ == 0 {
                            v___x_1015_ = v___x_1005_;
                            v_isShared_1016_ = v_isSharedCheck_1020_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1013_);
                            crate::leanh::lean_dec(v___x_1005_);
                            v___x_1015_ = crate::leanh::lean_box(0);
                            v_isShared_1016_ = v_isSharedCheck_1020_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1016_ == 0 {
                    v___x_1018_ = v___x_1015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
                    v___x_1018_ = v_reuseFailAlloc_1019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1___boxed(
    mut v_sz_1021_: *mut crate::leanh::LeanObject,
    mut v_i_1022_: *mut crate::leanh::LeanObject,
    mut v_bs_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1029_: usize = 0;
    let mut v_i_boxed_1030_: usize = 0;
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1029_ = crate::leanh::lean_unbox_usize(v_sz_1021_);
    crate::leanh::lean_dec(v_sz_1021_);
    v_i_boxed_1030_ = crate::leanh::lean_unbox_usize(v_i_1022_);
    crate::leanh::lean_dec(v_i_1022_);
    v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_boxed_1029_, v_i_boxed_1030_, v_bs_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
    crate::leanh::lean_dec(v___y_1027_);
    crate::leanh::lean_dec_ref(v___y_1026_);
    crate::leanh::lean_dec(v___y_1025_);
    crate::leanh::lean_dec_ref(v___y_1024_);
    return v_res_1031_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1032_: *mut crate::leanh::LeanObject,
    mut v_vals_1033_: *mut crate::leanh::LeanObject,
    mut v_i_1034_: *mut crate::leanh::LeanObject,
    mut v_k_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_array_get_size(v_keys_1032_);
                v___x_1037_ = lean_nat_dec_lt(v_i_1034_, v___x_1036_);
                if v___x_1037_ == 0 {
                    crate::leanh::lean_dec(v_i_1034_);
                    v___x_1038_ = crate::leanh::lean_box(0);
                    return v___x_1038_;
                } else {
                    v_k_x27_1039_ = lean_array_fget_borrowed(v_keys_1032_, v_i_1034_);
                    v___x_1040_ = lean_name_eq(v_k_1035_, v_k_x27_1039_);
                    if v___x_1040_ == 0 {
                        v___x_1041_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1042_ = lean_nat_add(v_i_1034_, v___x_1041_);
                        crate::leanh::lean_dec(v_i_1034_);
                        v_i_1034_ = v___x_1042_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1044_ = lean_array_fget_borrowed(v_vals_1033_, v_i_1034_);
                        crate::leanh::lean_dec(v_i_1034_);
                        crate::leanh::lean_inc(v___x_1044_);
                        v___x_1045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1045_, 0, v___x_1044_);
                        return v___x_1045_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1046_: *mut crate::leanh::LeanObject,
    mut v_vals_1047_: *mut crate::leanh::LeanObject,
    mut v_i_1048_: *mut crate::leanh::LeanObject,
    mut v_k_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_1046_, v_vals_1047_, v_i_1048_, v_k_1049_);
    crate::leanh::lean_dec(v_k_1049_);
    crate::leanh::lean_dec_ref(v_vals_1047_);
    crate::leanh::lean_dec_ref(v_keys_1046_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(
    mut v_x_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: usize,
    mut v_x_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: usize = 0;
    let mut v___x_1057_: usize = 0;
    let mut v___x_1058_: usize = 0;
    let mut v_j_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: usize = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1051_) == 0 {
                    v_es_1054_ = crate::leanh::lean_ctor_get(v_x_1051_, 0);
                    v___x_1055_ = crate::leanh::lean_box(2);
                    v___x_1056_ = 5usize;
                    v___x_1057_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1);
                    v___x_1058_ = lean_usize_land(v_x_1052_, v___x_1057_);
                    v_j_1059_ = lean_usize_to_nat(v___x_1058_);
                    v___x_1060_ = lean_array_get_borrowed(v___x_1055_, v_es_1054_, v_j_1059_);
                    crate::leanh::lean_dec(v_j_1059_);
                    match crate::leanh::lean_obj_tag(v___x_1060_) {
                        0 => {
                            v_key_1061_ = crate::leanh::lean_ctor_get(v___x_1060_, 0);
                            v_val_1062_ = crate::leanh::lean_ctor_get(v___x_1060_, 1);
                            v___x_1063_ = lean_name_eq(v_x_1053_, v_key_1061_);
                            if v___x_1063_ == 0 {
                                v___x_1064_ = crate::leanh::lean_box(0);
                                return v___x_1064_;
                            } else {
                                crate::leanh::lean_inc(v_val_1062_);
                                v___x_1065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1065_, 0, v_val_1062_);
                                return v___x_1065_;
                            }
                        }
                        1 => {
                            v_node_1066_ = crate::leanh::lean_ctor_get(v___x_1060_, 0);
                            v___x_1067_ = lean_usize_shift_right(v_x_1052_, v___x_1056_);
                            v_x_1051_ = v_node_1066_;
                            v_x_1052_ = v___x_1067_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1069_ = crate::leanh::lean_box(0);
                            return v___x_1069_;
                        }
                    }
                } else {
                    v_ks_1070_ = crate::leanh::lean_ctor_get(v_x_1051_, 0);
                    v_vs_1071_ = crate::leanh::lean_ctor_get(v_x_1051_, 1);
                    v___x_1072_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1073_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_ks_1070_, v_vs_1071_, v___x_1072_, v_x_1053_);
                    return v___x_1073_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg___boxed(
    mut v_x_1074_: *mut crate::leanh::LeanObject,
    mut v_x_1075_: *mut crate::leanh::LeanObject,
    mut v_x_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2479__boxed_1077_: usize = 0;
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2479__boxed_1077_ = crate::leanh::lean_unbox_usize(v_x_1075_);
    crate::leanh::lean_dec(v_x_1075_);
    v_res_1078_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_1074_, v_x_2479__boxed_1077_, v_x_1076_);
    crate::leanh::lean_dec(v_x_1076_);
    crate::leanh::lean_dec_ref(v_x_1074_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(
    mut v_x_1079_: *mut crate::leanh::LeanObject,
    mut v_x_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1082_: u64 = 0;
    let mut v___x_1083_: usize = 0;
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: u64 = 0;
    let mut v_hash_1086_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1080_) == 0 {
                    v___x_1085_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
                    v___y_1082_ = v___x_1085_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1086_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1080_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1082_ = v_hash_1086_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1083_ = lean_uint64_to_usize(v___y_1082_);
                v___x_1084_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_1079_, v___x_1083_, v_x_1080_);
                return v___x_1084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg___boxed(
    mut v_x_1087_: *mut crate::leanh::LeanObject,
    mut v_x_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_1087_, v_x_1088_);
    crate::leanh::lean_dec(v_x_1088_);
    crate::leanh::lean_dec_ref(v_x_1087_);
    return v_res_1089_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1090_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once),
        _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0,
    );
    v___x_1092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
    return v___x_1092_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1,
    );
    v___x_1094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1093_);
    crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1,
    );
    v___x_1096_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1096_, 0, v___x_1095_);
    crate::leanh::lean_ctor_set(v___x_1096_, 1, v___x_1095_);
    crate::leanh::lean_ctor_set(v___x_1096_, 2, v___x_1095_);
    crate::leanh::lean_ctor_set(v___x_1096_, 3, v___x_1095_);
    crate::leanh::lean_ctor_set(v___x_1096_, 4, v___x_1095_);
    crate::leanh::lean_ctor_set(v___x_1096_, 5, v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getEqnTheorems(
    mut v_fnName_1097_: *mut crate::leanh::LeanObject,
    mut v_a_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnTheorems_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v_val_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1126_: usize = 0;
    let mut v___x_1127_: usize = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1160_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v_unused_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut v_unused_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1174_: u8 = 0;
    let mut v_a_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1103_ = lean_st_ref_get(v_a_1101_);
                v_env_1104_ = crate::leanh::lean_ctor_get(v___x_1103_, 0);
                crate::leanh::lean_inc_ref(v_env_1104_);
                crate::leanh::lean_dec(v___x_1103_);
                v___x_1105_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
                v_asyncMode_1106_ = crate::leanh::lean_ctor_get(v___x_1105_, 2);
                v___x_1107_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
                v___x_1108_ = crate::leanh::lean_box(0);
                v___x_1109_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1107_,
                        v___x_1105_,
                        v_env_1104_,
                        v_asyncMode_1106_,
                        v___x_1108_,
                    );
                v_eqnTheorems_1110_ = crate::leanh::lean_ctor_get(v___x_1109_, 0);
                crate::leanh::lean_inc_ref(v_eqnTheorems_1110_);
                crate::leanh::lean_dec(v___x_1109_);
                v___x_1111_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_eqnTheorems_1110_, v_fnName_1097_);
                crate::leanh::lean_dec_ref(v_eqnTheorems_1110_);
                if crate::leanh::lean_obj_tag(v___x_1111_) == 1 {
                    crate::leanh::lean_dec(v_fnName_1097_);
                    v_val_1112_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                    v_isSharedCheck_1119_ = (!crate::leanh::lean_is_exclusive(v___x_1111_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1114_ = v___x_1111_;
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1112_);
                        crate::leanh::lean_dec(v___x_1111_);
                        v___x_1114_ = crate::leanh::lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1111_);
                    crate::leanh::lean_inc(v_fnName_1097_);
                    v___x_1120_ = l_Lean_Meta_getEqnsFor_x3f(
                        v_fnName_1097_,
                        v_a_1098_,
                        v_a_1099_,
                        v_a_1100_,
                        v_a_1101_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1120_) == 0 {
                        v_a_1121_ = crate::leanh::lean_ctor_get(v___x_1120_, 0);
                        v_isSharedCheck_1187_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1120_)) as u8;
                        if v_isSharedCheck_1187_ == 0 {
                            v___x_1123_ = v___x_1120_;
                            v_isShared_1124_ = v_isSharedCheck_1187_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1121_);
                            crate::leanh::lean_dec(v___x_1120_);
                            v___x_1123_ = crate::leanh::lean_box(0);
                            v_isShared_1124_ = v_isSharedCheck_1187_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fnName_1097_);
                        v_a_1188_ = crate::leanh::lean_ctor_get(v___x_1120_, 0);
                        v_isSharedCheck_1195_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1120_)) as u8;
                        if v_isSharedCheck_1195_ == 0 {
                            v___x_1190_ = v___x_1120_;
                            v_isShared_1191_ = v_isSharedCheck_1195_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1188_);
                            crate::leanh::lean_dec(v___x_1120_);
                            v___x_1190_ = crate::leanh::lean_box(0);
                            v_isShared_1191_ = v_isSharedCheck_1195_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1115_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1114_, 0);
                    v___x_1117_ = v___x_1114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_val_1112_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1117_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1121_) == 1 {
                    crate::leanh::lean_del_object(v___x_1123_);
                    v_val_1125_ = crate::leanh::lean_ctor_get(v_a_1121_, 0);
                    crate::leanh::lean_inc(v_val_1125_);
                    crate::leanh::lean_dec_ref_known(v_a_1121_, 1);
                    v_sz_1126_ = lean_array_size(v_val_1125_);
                    v___x_1127_ = 0usize;
                    v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_1126_, v___x_1127_, v_val_1125_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
                    if crate::leanh::lean_obj_tag(v___x_1128_) == 0 {
                        v_a_1129_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                        v_isSharedCheck_1174_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                        if v_isSharedCheck_1174_ == 0 {
                            v___x_1131_ = v___x_1128_;
                            v_isShared_1132_ = v_isSharedCheck_1174_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1129_);
                            crate::leanh::lean_dec(v___x_1128_);
                            v___x_1131_ = crate::leanh::lean_box(0);
                            v_isShared_1132_ = v_isSharedCheck_1174_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fnName_1097_);
                        v_a_1175_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                        v_isSharedCheck_1182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                        if v_isSharedCheck_1182_ == 0 {
                            v___x_1177_ = v___x_1128_;
                            v_isShared_1178_ = v_isSharedCheck_1182_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1175_);
                            crate::leanh::lean_dec(v___x_1128_);
                            v___x_1177_ = crate::leanh::lean_box(0);
                            v_isShared_1178_ = v_isSharedCheck_1182_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1121_);
                    crate::leanh::lean_dec(v_fnName_1097_);
                    v___x_1183_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1,
                    );
                    if v_isShared_1124_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1123_, 0, v___x_1183_);
                        v___x_1185_ = v___x_1123_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
                        v___x_1185_ = v_reuseFailAlloc_1186_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1133_ = lean_st_ref_take(v_a_1101_);
                v_env_1134_ = crate::leanh::lean_ctor_get(v___x_1133_, 0);
                v_nextMacroScope_1135_ = crate::leanh::lean_ctor_get(v___x_1133_, 1);
                v_ngen_1136_ = crate::leanh::lean_ctor_get(v___x_1133_, 2);
                v_auxDeclNGen_1137_ = crate::leanh::lean_ctor_get(v___x_1133_, 3);
                v_traceState_1138_ = crate::leanh::lean_ctor_get(v___x_1133_, 4);
                v_messages_1139_ = crate::leanh::lean_ctor_get(v___x_1133_, 6);
                v_infoState_1140_ = crate::leanh::lean_ctor_get(v___x_1133_, 7);
                v_snapshotTasks_1141_ = crate::leanh::lean_ctor_get(v___x_1133_, 8);
                v_isSharedCheck_1172_ = (!crate::leanh::lean_is_exclusive(v___x_1133_)) as u8;
                if v_isSharedCheck_1172_ == 0 {
                    v_unused_1173_ = crate::leanh::lean_ctor_get(v___x_1133_, 5);
                    crate::leanh::lean_dec(v_unused_1173_);
                    v___x_1143_ = v___x_1133_;
                    v_isShared_1144_ = v_isSharedCheck_1172_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1141_);
                    crate::leanh::lean_inc(v_infoState_1140_);
                    crate::leanh::lean_inc(v_messages_1139_);
                    crate::leanh::lean_inc(v_traceState_1138_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1137_);
                    crate::leanh::lean_inc(v_ngen_1136_);
                    crate::leanh::lean_inc(v_nextMacroScope_1135_);
                    crate::leanh::lean_inc(v_env_1134_);
                    crate::leanh::lean_dec(v___x_1133_);
                    v___x_1143_ = crate::leanh::lean_box(0);
                    v_isShared_1144_ = v_isSharedCheck_1172_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1145_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1,
                );
                v___x_1146_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_1145_, v_a_1129_);
                crate::leanh::lean_dec(v_a_1129_);
                crate::leanh::lean_inc_ref(v___x_1146_);
                v___f_1147_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1147_, 0, v_fnName_1097_);
                crate::leanh::lean_closure_set(v___f_1147_, 1, v___x_1146_);
                v___x_1148_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1105_,
                    v_env_1134_,
                    v___f_1147_,
                    v_asyncMode_1106_,
                    v___x_1108_,
                );
                v___x_1149_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2,
                );
                if v_isShared_1144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1143_, 5, v___x_1149_);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1148_);
                    v___x_1151_ = v___x_1143_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_nextMacroScope_1135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_ngen_1136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_auxDeclNGen_1137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_traceState_1138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 5, v___x_1149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 6, v_messages_1139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 7, v_infoState_1140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 8, v_snapshotTasks_1141_);
                    v___x_1151_ = v_reuseFailAlloc_1171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1152_ = lean_st_ref_set(v_a_1101_, v___x_1151_);
                v___x_1153_ = lean_st_ref_take(v_a_1099_);
                v_mctx_1154_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                v_zetaDeltaFVarIds_1155_ = crate::leanh::lean_ctor_get(v___x_1153_, 2);
                v_postponed_1156_ = crate::leanh::lean_ctor_get(v___x_1153_, 3);
                v_diag_1157_ = crate::leanh::lean_ctor_get(v___x_1153_, 4);
                v_isSharedCheck_1169_ = (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                if v_isSharedCheck_1169_ == 0 {
                    v_unused_1170_ = crate::leanh::lean_ctor_get(v___x_1153_, 1);
                    crate::leanh::lean_dec(v_unused_1170_);
                    v___x_1159_ = v___x_1153_;
                    v_isShared_1160_ = v_isSharedCheck_1169_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1157_);
                    crate::leanh::lean_inc(v_postponed_1156_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1155_);
                    crate::leanh::lean_inc(v_mctx_1154_);
                    crate::leanh::lean_dec(v___x_1153_);
                    v___x_1159_ = crate::leanh::lean_box(0);
                    v_isShared_1160_ = v_isSharedCheck_1169_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1161_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3,
                );
                if v_isShared_1160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1159_, 1, v___x_1161_);
                    v___x_1163_ = v___x_1159_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_mctx_1154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1161_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1168_,
                        2,
                        v_zetaDeltaFVarIds_1155_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_postponed_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_diag_1157_);
                    v___x_1163_ = v_reuseFailAlloc_1168_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1164_ = lean_st_ref_set(v_a_1099_, v___x_1163_);
                if v_isShared_1132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1146_);
                    v___x_1166_ = v___x_1131_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1146_);
                    v___x_1166_ = v_reuseFailAlloc_1167_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1166_;
            }
            10 => {
                if v_isShared_1178_ == 0 {
                    v___x_1180_ = v___x_1177_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
                    v___x_1180_ = v_reuseFailAlloc_1181_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1180_;
            }
            12 => {
                return v___x_1185_;
            }
            13 => {
                if v_isShared_1191_ == 0 {
                    v___x_1193_ = v___x_1190_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getEqnTheorems___boxed(
    mut v_fnName_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1202_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(
        v_fnName_1196_,
        v_a_1197_,
        v_a_1198_,
        v_a_1199_,
        v_a_1200_,
    );
    crate::leanh::lean_dec(v_a_1200_);
    crate::leanh::lean_dec_ref(v_a_1199_);
    crate::leanh::lean_dec(v_a_1198_);
    crate::leanh::lean_dec_ref(v_a_1197_);
    return v_res_1202_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(
    mut v_00_u03b2_1203_: *mut crate::leanh::LeanObject,
    mut v_x_1204_: *mut crate::leanh::LeanObject,
    mut v_x_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_1204_, v_x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___boxed(
    mut v_00_u03b2_1207_: *mut crate::leanh::LeanObject,
    mut v_x_1208_: *mut crate::leanh::LeanObject,
    mut v_x_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(
            v_00_u03b2_1207_,
            v_x_1208_,
            v_x_1209_,
        );
    crate::leanh::lean_dec(v_x_1209_);
    crate::leanh::lean_dec_ref(v_x_1208_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2(
    mut v_00_u03b2_1211_: *mut crate::leanh::LeanObject,
    mut v_x_1212_: *mut crate::leanh::LeanObject,
    mut v_x_1213_: *mut crate::leanh::LeanObject,
    mut v_x_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_x_1212_, v_x_1213_, v_x_1214_);
    return v___x_1215_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(
    mut v_00_u03b2_1216_: *mut crate::leanh::LeanObject,
    mut v_x_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: usize,
    mut v_x_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_1217_, v_x_1218_, v_x_1219_);
    return v___x_1220_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___boxed(
    mut v_00_u03b2_1221_: *mut crate::leanh::LeanObject,
    mut v_x_1222_: *mut crate::leanh::LeanObject,
    mut v_x_1223_: *mut crate::leanh::LeanObject,
    mut v_x_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2756__boxed_1225_: usize = 0;
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2756__boxed_1225_ = crate::leanh::lean_unbox_usize(v_x_1223_);
    crate::leanh::lean_dec(v_x_1223_);
    v_res_1226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(v_00_u03b2_1221_, v_x_1222_, v_x_2756__boxed_1225_, v_x_1224_);
    crate::leanh::lean_dec(v_x_1224_);
    crate::leanh::lean_dec_ref(v_x_1222_);
    return v_res_1226_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(
    mut v_00_u03b2_1227_: *mut crate::leanh::LeanObject,
    mut v_x_1228_: *mut crate::leanh::LeanObject,
    mut v_x_1229_: usize,
    mut v_x_1230_: usize,
    mut v_x_1231_: *mut crate::leanh::LeanObject,
    mut v_x_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_1228_, v_x_1229_, v_x_1230_, v_x_1231_, v_x_1232_);
    return v___x_1233_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___boxed(
    mut v_00_u03b2_1234_: *mut crate::leanh::LeanObject,
    mut v_x_1235_: *mut crate::leanh::LeanObject,
    mut v_x_1236_: *mut crate::leanh::LeanObject,
    mut v_x_1237_: *mut crate::leanh::LeanObject,
    mut v_x_1238_: *mut crate::leanh::LeanObject,
    mut v_x_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2767__boxed_1240_: usize = 0;
    let mut v_x_2768__boxed_1241_: usize = 0;
    let mut v_res_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2767__boxed_1240_ = crate::leanh::lean_unbox_usize(v_x_1236_);
    crate::leanh::lean_dec(v_x_1236_);
    v_x_2768__boxed_1241_ = crate::leanh::lean_unbox_usize(v_x_1237_);
    crate::leanh::lean_dec(v_x_1237_);
    v_res_1242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(v_00_u03b2_1234_, v_x_1235_, v_x_2767__boxed_1240_, v_x_2768__boxed_1241_, v_x_1238_, v_x_1239_);
    return v_res_1242_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1243_: *mut crate::leanh::LeanObject,
    mut v_keys_1244_: *mut crate::leanh::LeanObject,
    mut v_vals_1245_: *mut crate::leanh::LeanObject,
    mut v_heq_1246_: *mut crate::leanh::LeanObject,
    mut v_i_1247_: *mut crate::leanh::LeanObject,
    mut v_k_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_1244_, v_vals_1245_, v_i_1247_, v_k_1248_);
    return v___x_1249_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1250_: *mut crate::leanh::LeanObject,
    mut v_keys_1251_: *mut crate::leanh::LeanObject,
    mut v_vals_1252_: *mut crate::leanh::LeanObject,
    mut v_heq_1253_: *mut crate::leanh::LeanObject,
    mut v_i_1254_: *mut crate::leanh::LeanObject,
    mut v_k_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(v_00_u03b2_1250_, v_keys_1251_, v_vals_1252_, v_heq_1253_, v_i_1254_, v_k_1255_);
    crate::leanh::lean_dec(v_k_1255_);
    crate::leanh::lean_dec_ref(v_vals_1252_);
    crate::leanh::lean_dec_ref(v_keys_1251_);
    return v_res_1256_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1257_: *mut crate::leanh::LeanObject,
    mut v_n_1258_: *mut crate::leanh::LeanObject,
    mut v_k_1259_: *mut crate::leanh::LeanObject,
    mut v_v_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v_n_1258_, v_k_1259_, v_v_1260_);
    return v___x_1261_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(
    mut v_00_u03b2_1262_: *mut crate::leanh::LeanObject,
    mut v_depth_1263_: usize,
    mut v_keys_1264_: *mut crate::leanh::LeanObject,
    mut v_vals_1265_: *mut crate::leanh::LeanObject,
    mut v_heq_1266_: *mut crate::leanh::LeanObject,
    mut v_i_1267_: *mut crate::leanh::LeanObject,
    mut v_entries_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_1263_, v_keys_1264_, v_vals_1265_, v_i_1267_, v_entries_1268_);
    return v___x_1269_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_1270_: *mut crate::leanh::LeanObject,
    mut v_depth_1271_: *mut crate::leanh::LeanObject,
    mut v_keys_1272_: *mut crate::leanh::LeanObject,
    mut v_vals_1273_: *mut crate::leanh::LeanObject,
    mut v_heq_1274_: *mut crate::leanh::LeanObject,
    mut v_i_1275_: *mut crate::leanh::LeanObject,
    mut v_entries_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1277_: usize = 0;
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1277_ = crate::leanh::lean_unbox_usize(v_depth_1271_);
    crate::leanh::lean_dec(v_depth_1271_);
    v_res_1278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(v_00_u03b2_1270_, v_depth_boxed_1277_, v_keys_1272_, v_vals_1273_, v_heq_1274_, v_i_1275_, v_entries_1276_);
    crate::leanh::lean_dec_ref(v_vals_1273_);
    crate::leanh::lean_dec_ref(v_keys_1272_);
    return v_res_1278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6(
    mut v_00_u03b2_1279_: *mut crate::leanh::LeanObject,
    mut v_x_1280_: *mut crate::leanh::LeanObject,
    mut v_x_1281_: *mut crate::leanh::LeanObject,
    mut v_x_1282_: *mut crate::leanh::LeanObject,
    mut v_x_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1280_, v_x_1281_, v_x_1282_, v_x_1283_);
    return v___x_1284_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0(
    mut v_fnName_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_cache_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eqnTheorems_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldTheorems_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchTheorems_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eqnTheorems_1288_ = crate::leanh::lean_ctor_get(v_cache_1287_, 0);
                v_unfoldTheorems_1289_ = crate::leanh::lean_ctor_get(v_cache_1287_, 1);
                v_matchTheorems_1290_ = crate::leanh::lean_ctor_get(v_cache_1287_, 2);
                v_isSharedCheck_1298_ = (!crate::leanh::lean_is_exclusive(v_cache_1287_)) as u8;
                if v_isSharedCheck_1298_ == 0 {
                    v___x_1292_ = v_cache_1287_;
                    v_isShared_1293_ = v_isSharedCheck_1298_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_matchTheorems_1290_);
                    crate::leanh::lean_inc(v_unfoldTheorems_1289_);
                    crate::leanh::lean_inc(v_eqnTheorems_1288_);
                    crate::leanh::lean_dec(v_cache_1287_);
                    v___x_1292_ = crate::leanh::lean_box(0);
                    v_isShared_1293_ = v_isSharedCheck_1298_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1294_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_unfoldTheorems_1289_, v_fnName_1285_, v_a_1286_);
                if v_isShared_1293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1292_, 1, v___x_1294_);
                    v___x_1296_ = v___x_1292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1297_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_eqnTheorems_1288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_matchTheorems_1290_);
                    v___x_1296_ = v_reuseFailAlloc_1297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1299_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once),
        _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0,
    );
    v___x_1301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1300_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1,
    );
    v___x_1303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1303_, 0, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1303_, 1, v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1,
    );
    v___x_1305_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 1, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 2, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 3, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 4, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 5, v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(
    mut v_fnName_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldTheorems_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v_val_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___f_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_unused_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut v_unused_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut v_a_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = lean_st_ref_get(v_a_1310_);
                v_env_1313_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                crate::leanh::lean_inc_ref(v_env_1313_);
                crate::leanh::lean_dec(v___x_1312_);
                v___x_1314_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
                v_asyncMode_1315_ = crate::leanh::lean_ctor_get(v___x_1314_, 2);
                v___x_1316_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
                v___x_1317_ = crate::leanh::lean_box(0);
                v___x_1318_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1316_,
                        v___x_1314_,
                        v_env_1313_,
                        v_asyncMode_1315_,
                        v___x_1317_,
                    );
                v_unfoldTheorems_1319_ = crate::leanh::lean_ctor_get(v___x_1318_, 1);
                crate::leanh::lean_inc_ref(v_unfoldTheorems_1319_);
                crate::leanh::lean_dec(v___x_1318_);
                v___x_1320_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_unfoldTheorems_1319_, v_fnName_1306_);
                crate::leanh::lean_dec_ref(v_unfoldTheorems_1319_);
                if crate::leanh::lean_obj_tag(v___x_1320_) == 1 {
                    crate::leanh::lean_dec(v_fnName_1306_);
                    v___x_1321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
                    return v___x_1321_;
                } else {
                    crate::leanh::lean_dec(v___x_1320_);
                    v___x_1322_ = 1;
                    crate::leanh::lean_inc(v_fnName_1306_);
                    v___x_1323_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                        v_fnName_1306_,
                        v___x_1322_,
                        v_a_1307_,
                        v_a_1308_,
                        v_a_1309_,
                        v_a_1310_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1323_) == 0 {
                        v_a_1324_ = crate::leanh::lean_ctor_get(v___x_1323_, 0);
                        v_isSharedCheck_1393_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1323_)) as u8;
                        if v_isSharedCheck_1393_ == 0 {
                            v___x_1326_ = v___x_1323_;
                            v_isShared_1327_ = v_isSharedCheck_1393_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1324_);
                            crate::leanh::lean_dec(v___x_1323_);
                            v___x_1326_ = crate::leanh::lean_box(0);
                            v_isShared_1327_ = v_isSharedCheck_1393_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fnName_1306_);
                        v_a_1394_ = crate::leanh::lean_ctor_get(v___x_1323_, 0);
                        v_isSharedCheck_1401_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1323_)) as u8;
                        if v_isSharedCheck_1401_ == 0 {
                            v___x_1396_ = v___x_1323_;
                            v_isShared_1397_ = v_isSharedCheck_1401_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1394_);
                            crate::leanh::lean_dec(v___x_1323_);
                            v___x_1396_ = crate::leanh::lean_box(0);
                            v_isShared_1397_ = v_isSharedCheck_1401_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1324_) == 1 {
                    crate::leanh::lean_del_object(v___x_1326_);
                    v_val_1328_ = crate::leanh::lean_ctor_get(v_a_1324_, 0);
                    v_isSharedCheck_1388_ = (!crate::leanh::lean_is_exclusive(v_a_1324_)) as u8;
                    if v_isSharedCheck_1388_ == 0 {
                        v___x_1330_ = v_a_1324_;
                        v_isShared_1331_ = v_isSharedCheck_1388_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1328_);
                        crate::leanh::lean_dec(v_a_1324_);
                        v___x_1330_ = crate::leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1388_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1324_);
                    crate::leanh::lean_dec(v_fnName_1306_);
                    v___x_1389_ = crate::leanh::lean_box(0);
                    if v_isShared_1327_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1389_);
                        v___x_1391_ = v___x_1326_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
                        v___x_1391_ = v_reuseFailAlloc_1392_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1332_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                    v_val_1328_,
                    v_a_1307_,
                    v_a_1308_,
                    v_a_1309_,
                    v_a_1310_,
                );
                if crate::leanh::lean_obj_tag(v___x_1332_) == 0 {
                    v_a_1333_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                    v_isSharedCheck_1379_ = (!crate::leanh::lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1379_ == 0 {
                        v___x_1335_ = v___x_1332_;
                        v_isShared_1336_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1333_);
                        crate::leanh::lean_dec(v___x_1332_);
                        v___x_1335_ = crate::leanh::lean_box(0);
                        v_isShared_1336_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1330_);
                    crate::leanh::lean_dec(v_fnName_1306_);
                    v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                    v_isSharedCheck_1387_ = (!crate::leanh::lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1387_ == 0 {
                        v___x_1382_ = v___x_1332_;
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1380_);
                        crate::leanh::lean_dec(v___x_1332_);
                        v___x_1382_ = crate::leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1337_ = lean_st_ref_take(v_a_1310_);
                v_env_1338_ = crate::leanh::lean_ctor_get(v___x_1337_, 0);
                v_nextMacroScope_1339_ = crate::leanh::lean_ctor_get(v___x_1337_, 1);
                v_ngen_1340_ = crate::leanh::lean_ctor_get(v___x_1337_, 2);
                v_auxDeclNGen_1341_ = crate::leanh::lean_ctor_get(v___x_1337_, 3);
                v_traceState_1342_ = crate::leanh::lean_ctor_get(v___x_1337_, 4);
                v_messages_1343_ = crate::leanh::lean_ctor_get(v___x_1337_, 6);
                v_infoState_1344_ = crate::leanh::lean_ctor_get(v___x_1337_, 7);
                v_snapshotTasks_1345_ = crate::leanh::lean_ctor_get(v___x_1337_, 8);
                v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v___x_1337_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v_unused_1378_ = crate::leanh::lean_ctor_get(v___x_1337_, 5);
                    crate::leanh::lean_dec(v_unused_1378_);
                    v___x_1347_ = v___x_1337_;
                    v_isShared_1348_ = v_isSharedCheck_1377_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1345_);
                    crate::leanh::lean_inc(v_infoState_1344_);
                    crate::leanh::lean_inc(v_messages_1343_);
                    crate::leanh::lean_inc(v_traceState_1342_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1341_);
                    crate::leanh::lean_inc(v_ngen_1340_);
                    crate::leanh::lean_inc(v_nextMacroScope_1339_);
                    crate::leanh::lean_inc(v_env_1338_);
                    crate::leanh::lean_dec(v___x_1337_);
                    v___x_1347_ = crate::leanh::lean_box(0);
                    v_isShared_1348_ = v_isSharedCheck_1377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1333_);
                v___f_1349_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1349_, 0, v_fnName_1306_);
                crate::leanh::lean_closure_set(v___f_1349_, 1, v_a_1333_);
                v___x_1350_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1314_,
                    v_env_1338_,
                    v___f_1349_,
                    v_asyncMode_1315_,
                    v___x_1317_,
                );
                v___x_1351_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2,
                );
                if v_isShared_1348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1347_, 5, v___x_1351_);
                    crate::leanh::lean_ctor_set(v___x_1347_, 0, v___x_1350_);
                    v___x_1353_ = v___x_1347_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_nextMacroScope_1339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_ngen_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_auxDeclNGen_1341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_traceState_1342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 5, v___x_1351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 6, v_messages_1343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 7, v_infoState_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 8, v_snapshotTasks_1345_);
                    v___x_1353_ = v_reuseFailAlloc_1376_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1354_ = lean_st_ref_set(v_a_1310_, v___x_1353_);
                v___x_1355_ = lean_st_ref_take(v_a_1308_);
                v_mctx_1356_ = crate::leanh::lean_ctor_get(v___x_1355_, 0);
                v_zetaDeltaFVarIds_1357_ = crate::leanh::lean_ctor_get(v___x_1355_, 2);
                v_postponed_1358_ = crate::leanh::lean_ctor_get(v___x_1355_, 3);
                v_diag_1359_ = crate::leanh::lean_ctor_get(v___x_1355_, 4);
                v_isSharedCheck_1374_ = (!crate::leanh::lean_is_exclusive(v___x_1355_)) as u8;
                if v_isSharedCheck_1374_ == 0 {
                    v_unused_1375_ = crate::leanh::lean_ctor_get(v___x_1355_, 1);
                    crate::leanh::lean_dec(v_unused_1375_);
                    v___x_1361_ = v___x_1355_;
                    v_isShared_1362_ = v_isSharedCheck_1374_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1359_);
                    crate::leanh::lean_inc(v_postponed_1358_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1357_);
                    crate::leanh::lean_inc(v_mctx_1356_);
                    crate::leanh::lean_dec(v___x_1355_);
                    v___x_1361_ = crate::leanh::lean_box(0);
                    v_isShared_1362_ = v_isSharedCheck_1374_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1363_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3,
                );
                if v_isShared_1362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1361_, 1, v___x_1363_);
                    v___x_1365_ = v___x_1361_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_mctx_1356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1363_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1373_,
                        2,
                        v_zetaDeltaFVarIds_1357_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_postponed_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_diag_1359_);
                    v___x_1365_ = v_reuseFailAlloc_1373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1366_ = lean_st_ref_set(v_a_1308_, v___x_1365_);
                if v_isShared_1331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v_a_1333_);
                    v___x_1368_ = v___x_1330_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1333_);
                    v___x_1368_ = v_reuseFailAlloc_1372_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1368_);
                    v___x_1370_ = v___x_1335_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1370_;
            }
            10 => {
                if v_isShared_1383_ == 0 {
                    v___x_1385_ = v___x_1382_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1385_;
            }
            12 => {
                return v___x_1391_;
            }
            13 => {
                if v_isShared_1397_ == 0 {
                    v___x_1399_ = v___x_1396_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___boxed(
    mut v_fnName_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(
        v_fnName_1402_,
        v_a_1403_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
    );
    crate::leanh::lean_dec(v_a_1406_);
    crate::leanh::lean_dec_ref(v_a_1405_);
    crate::leanh::lean_dec(v_a_1404_);
    crate::leanh::lean_dec_ref(v_a_1403_);
    return v_res_1408_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0(
    mut v_matcherName_1409_: *mut crate::leanh::LeanObject,
    mut v___x_1410_: *mut crate::leanh::LeanObject,
    mut v_cache_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eqnTheorems_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldTheorems_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchTheorems_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eqnTheorems_1412_ = crate::leanh::lean_ctor_get(v_cache_1411_, 0);
                v_unfoldTheorems_1413_ = crate::leanh::lean_ctor_get(v_cache_1411_, 1);
                v_matchTheorems_1414_ = crate::leanh::lean_ctor_get(v_cache_1411_, 2);
                v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v_cache_1411_)) as u8;
                if v_isSharedCheck_1422_ == 0 {
                    v___x_1416_ = v_cache_1411_;
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_matchTheorems_1414_);
                    crate::leanh::lean_inc(v_unfoldTheorems_1413_);
                    crate::leanh::lean_inc(v_eqnTheorems_1412_);
                    crate::leanh::lean_dec(v_cache_1411_);
                    v___x_1416_ = crate::leanh::lean_box(0);
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1418_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_matchTheorems_1414_, v_matcherName_1409_, v___x_1410_);
                if v_isShared_1417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1416_, 2, v___x_1418_);
                    v___x_1420_ = v___x_1416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_eqnTheorems_1412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_unfoldTheorems_1413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 2, v___x_1418_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getMatchTheorems(
    mut v_matcherName_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchTheorems_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1445_: u8 = 0;
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnNames_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut v_unused_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v_a_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1505_: u8 = 0;
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1429_ = lean_st_ref_get(v_a_1427_);
                v_env_1430_ = crate::leanh::lean_ctor_get(v___x_1429_, 0);
                crate::leanh::lean_inc_ref(v_env_1430_);
                crate::leanh::lean_dec(v___x_1429_);
                v___x_1431_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
                v_asyncMode_1432_ = crate::leanh::lean_ctor_get(v___x_1431_, 2);
                v___x_1433_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
                v___x_1434_ = crate::leanh::lean_box(0);
                v___x_1435_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1433_,
                        v___x_1431_,
                        v_env_1430_,
                        v_asyncMode_1432_,
                        v___x_1434_,
                    );
                v_matchTheorems_1436_ = crate::leanh::lean_ctor_get(v___x_1435_, 2);
                crate::leanh::lean_inc_ref(v_matchTheorems_1436_);
                crate::leanh::lean_dec(v___x_1435_);
                v___x_1437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_matchTheorems_1436_, v_matcherName_1423_);
                crate::leanh::lean_dec_ref(v_matchTheorems_1436_);
                if crate::leanh::lean_obj_tag(v___x_1437_) == 1 {
                    crate::leanh::lean_dec(v_matcherName_1423_);
                    v_val_1438_ = crate::leanh::lean_ctor_get(v___x_1437_, 0);
                    v_isSharedCheck_1445_ = (!crate::leanh::lean_is_exclusive(v___x_1437_)) as u8;
                    if v_isSharedCheck_1445_ == 0 {
                        v___x_1440_ = v___x_1437_;
                        v_isShared_1441_ = v_isSharedCheck_1445_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1438_);
                        crate::leanh::lean_dec(v___x_1437_);
                        v___x_1440_ = crate::leanh::lean_box(0);
                        v_isShared_1441_ = v_isSharedCheck_1445_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1437_);
                    crate::leanh::lean_inc(v_a_1427_);
                    crate::leanh::lean_inc_ref(v_a_1426_);
                    crate::leanh::lean_inc(v_a_1425_);
                    crate::leanh::lean_inc_ref(v_a_1424_);
                    crate::leanh::lean_inc(v_matcherName_1423_);
                    v___x_1446_ = lean_get_match_equations_for(
                        v_matcherName_1423_,
                        v_a_1424_,
                        v_a_1425_,
                        v_a_1426_,
                        v_a_1427_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1446_) == 0 {
                        v_a_1447_ = crate::leanh::lean_ctor_get(v___x_1446_, 0);
                        crate::leanh::lean_inc(v_a_1447_);
                        crate::leanh::lean_dec_ref_known(v___x_1446_, 1);
                        v_eqnNames_1448_ = crate::leanh::lean_ctor_get(v_a_1447_, 0);
                        crate::leanh::lean_inc_ref(v_eqnNames_1448_);
                        crate::leanh::lean_dec(v_a_1447_);
                        v_sz_1449_ = lean_array_size(v_eqnNames_1448_);
                        v___x_1450_ = 0usize;
                        v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_1449_, v___x_1450_, v_eqnNames_1448_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
                        if crate::leanh::lean_obj_tag(v___x_1451_) == 0 {
                            v_a_1452_ = crate::leanh::lean_ctor_get(v___x_1451_, 0);
                            v_isSharedCheck_1497_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1451_)) as u8;
                            if v_isSharedCheck_1497_ == 0 {
                                v___x_1454_ = v___x_1451_;
                                v_isShared_1455_ = v_isSharedCheck_1497_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1452_);
                                crate::leanh::lean_dec(v___x_1451_);
                                v___x_1454_ = crate::leanh::lean_box(0);
                                v_isShared_1455_ = v_isSharedCheck_1497_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_matcherName_1423_);
                            v_a_1498_ = crate::leanh::lean_ctor_get(v___x_1451_, 0);
                            v_isSharedCheck_1505_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1451_)) as u8;
                            if v_isSharedCheck_1505_ == 0 {
                                v___x_1500_ = v___x_1451_;
                                v_isShared_1501_ = v_isSharedCheck_1505_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1498_);
                                crate::leanh::lean_dec(v___x_1451_);
                                v___x_1500_ = crate::leanh::lean_box(0);
                                v_isShared_1501_ = v_isSharedCheck_1505_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_matcherName_1423_);
                        v_a_1506_ = crate::leanh::lean_ctor_get(v___x_1446_, 0);
                        v_isSharedCheck_1513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1446_)) as u8;
                        if v_isSharedCheck_1513_ == 0 {
                            v___x_1508_ = v___x_1446_;
                            v_isShared_1509_ = v_isSharedCheck_1513_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1506_);
                            crate::leanh::lean_dec(v___x_1446_);
                            v___x_1508_ = crate::leanh::lean_box(0);
                            v_isShared_1509_ = v_isSharedCheck_1513_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1441_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1440_, 0);
                    v___x_1443_ = v___x_1440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_val_1438_);
                    v___x_1443_ = v_reuseFailAlloc_1444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1443_;
            }
            3 => {
                v___x_1456_ = lean_st_ref_take(v_a_1427_);
                v_env_1457_ = crate::leanh::lean_ctor_get(v___x_1456_, 0);
                v_nextMacroScope_1458_ = crate::leanh::lean_ctor_get(v___x_1456_, 1);
                v_ngen_1459_ = crate::leanh::lean_ctor_get(v___x_1456_, 2);
                v_auxDeclNGen_1460_ = crate::leanh::lean_ctor_get(v___x_1456_, 3);
                v_traceState_1461_ = crate::leanh::lean_ctor_get(v___x_1456_, 4);
                v_messages_1462_ = crate::leanh::lean_ctor_get(v___x_1456_, 6);
                v_infoState_1463_ = crate::leanh::lean_ctor_get(v___x_1456_, 7);
                v_snapshotTasks_1464_ = crate::leanh::lean_ctor_get(v___x_1456_, 8);
                v_isSharedCheck_1495_ = (!crate::leanh::lean_is_exclusive(v___x_1456_)) as u8;
                if v_isSharedCheck_1495_ == 0 {
                    v_unused_1496_ = crate::leanh::lean_ctor_get(v___x_1456_, 5);
                    crate::leanh::lean_dec(v_unused_1496_);
                    v___x_1466_ = v___x_1456_;
                    v_isShared_1467_ = v_isSharedCheck_1495_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1464_);
                    crate::leanh::lean_inc(v_infoState_1463_);
                    crate::leanh::lean_inc(v_messages_1462_);
                    crate::leanh::lean_inc(v_traceState_1461_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1460_);
                    crate::leanh::lean_inc(v_ngen_1459_);
                    crate::leanh::lean_inc(v_nextMacroScope_1458_);
                    crate::leanh::lean_inc(v_env_1457_);
                    crate::leanh::lean_dec(v___x_1456_);
                    v___x_1466_ = crate::leanh::lean_box(0);
                    v_isShared_1467_ = v_isSharedCheck_1495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1468_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1,
                );
                v___x_1469_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_1468_, v_a_1452_);
                crate::leanh::lean_dec(v_a_1452_);
                crate::leanh::lean_inc_ref(v___x_1469_);
                v___f_1470_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1470_, 0, v_matcherName_1423_);
                crate::leanh::lean_closure_set(v___f_1470_, 1, v___x_1469_);
                v___x_1471_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1431_,
                    v_env_1457_,
                    v___f_1470_,
                    v_asyncMode_1432_,
                    v___x_1434_,
                );
                v___x_1472_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2,
                );
                if v_isShared_1467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1466_, 5, v___x_1472_);
                    crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1471_);
                    v___x_1474_ = v___x_1466_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_nextMacroScope_1458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_ngen_1459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_auxDeclNGen_1460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_traceState_1461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 5, v___x_1472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 6, v_messages_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 7, v_infoState_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 8, v_snapshotTasks_1464_);
                    v___x_1474_ = v_reuseFailAlloc_1494_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1475_ = lean_st_ref_set(v_a_1427_, v___x_1474_);
                v___x_1476_ = lean_st_ref_take(v_a_1425_);
                v_mctx_1477_ = crate::leanh::lean_ctor_get(v___x_1476_, 0);
                v_zetaDeltaFVarIds_1478_ = crate::leanh::lean_ctor_get(v___x_1476_, 2);
                v_postponed_1479_ = crate::leanh::lean_ctor_get(v___x_1476_, 3);
                v_diag_1480_ = crate::leanh::lean_ctor_get(v___x_1476_, 4);
                v_isSharedCheck_1492_ = (!crate::leanh::lean_is_exclusive(v___x_1476_)) as u8;
                if v_isSharedCheck_1492_ == 0 {
                    v_unused_1493_ = crate::leanh::lean_ctor_get(v___x_1476_, 1);
                    crate::leanh::lean_dec(v_unused_1493_);
                    v___x_1482_ = v___x_1476_;
                    v_isShared_1483_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1480_);
                    crate::leanh::lean_inc(v_postponed_1479_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1478_);
                    crate::leanh::lean_inc(v_mctx_1477_);
                    crate::leanh::lean_dec(v___x_1476_);
                    v___x_1482_ = crate::leanh::lean_box(0);
                    v_isShared_1483_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1484_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once),
                    _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3,
                );
                if v_isShared_1483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1482_, 1, v___x_1484_);
                    v___x_1486_ = v___x_1482_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_mctx_1477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1484_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1491_,
                        2,
                        v_zetaDeltaFVarIds_1478_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_postponed_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_diag_1480_);
                    v___x_1486_ = v_reuseFailAlloc_1491_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1487_ = lean_st_ref_set(v_a_1425_, v___x_1486_);
                if v_isShared_1455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1469_);
                    v___x_1489_ = v___x_1454_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1469_);
                    v___x_1489_ = v_reuseFailAlloc_1490_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1489_;
            }
            9 => {
                if v_isShared_1501_ == 0 {
                    v___x_1503_ = v___x_1500_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1503_;
            }
            11 => {
                if v_isShared_1509_ == 0 {
                    v___x_1511_ = v___x_1508_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
                    v___x_1511_ = v_reuseFailAlloc_1512_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getMatchTheorems___boxed(
    mut v_matcherName_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_a_1517_: *mut crate::leanh::LeanObject,
    mut v_a_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(
        v_matcherName_1514_,
        v_a_1515_,
        v_a_1516_,
        v_a_1517_,
        v_a_1518_,
    );
    crate::leanh::lean_dec(v_a_1518_);
    crate::leanh::lean_dec_ref(v_a_1517_);
    crate::leanh::lean_dec(v_a_1516_);
    crate::leanh::lean_dec_ref(v_a_1515_);
    return v_res_1520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default,
    );
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState);
    res = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup,
    );
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatchEqsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
}
