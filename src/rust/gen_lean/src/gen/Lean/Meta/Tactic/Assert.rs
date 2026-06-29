// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Revert Lean.Elab.InfoTree.Main Lean.Util.ForEachExpr Lean.Meta.AppBuilder
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_infer_type, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_push___redArg, l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_hasExprMVar,
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_letE___override,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkBVar, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkForall,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_get_x21, l_Lean_LocalContext_setKind, l_Lean_LocalDecl_fvarId,
    l_Lean_LocalDecl_index, l_Lean_LocalDecl_userName, l_Lean_instDecidableEqLocalDeclKind,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEqRefl, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_MVarId_getDecl,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_Meta_FVarSubst_insert,
    runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, l_Lean_Meta_intro1Core, l_Lean_Meta_introNCore,
    runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, l_Lean_MVarId_revertAfter,
    runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_modifyExprMVarLCtx, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_assert___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 115, 115, 101, 114, 116, 0],
    };
static mut l_Lean_MVarId_assert___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assert___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assert___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_assert___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6255460451893900049 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_assert___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assert___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_define___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [100, 101, 102, 105, 110, 101, 0],
    };
static mut l_Lean_MVarId_define___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_define___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_define___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_define___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12110259722422313427 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_define___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_define___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertExt___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_MVarId_assertExt___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertExt___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_assertExt___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_assertExt___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_assertExt___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_assertAfter___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [97, 115, 115, 101, 114, 116, 65, 102, 116, 101, 114, 0],
    };
static mut l_Lean_MVarId_assertAfter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertAfter___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6688911828405300775 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_assertAfter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            97, 115, 115, 101, 114, 116, 72, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0,
        ],
    };
static mut l_Lean_MVarId_assertHypotheses___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16050730560474456637 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_assertHypotheses___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__2_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_assertHypotheses___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
    mut v_mvarId_2182_: *mut crate::leanh::LeanObject,
    mut v_x_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_a_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2189_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2182_,
                    v_x_2183_,
                    v___y_2184_,
                    v___y_2185_,
                    v___y_2186_,
                    v___y_2187_,
                );
                if crate::leanh::lean_obj_tag(v___x_2189_) == 0 {
                    v_a_2190_ = crate::leanh::lean_ctor_get(v___x_2189_, 0);
                    v_isSharedCheck_2197_ = (!crate::leanh::lean_is_exclusive(v___x_2189_)) as u8;
                    if v_isSharedCheck_2197_ == 0 {
                        v___x_2192_ = v___x_2189_;
                        v_isShared_2193_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2190_);
                        crate::leanh::lean_dec(v___x_2189_);
                        v___x_2192_ = crate::leanh::lean_box(0);
                        v_isShared_2193_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2198_ = crate::leanh::lean_ctor_get(v___x_2189_, 0);
                    v_isSharedCheck_2205_ = (!crate::leanh::lean_is_exclusive(v___x_2189_)) as u8;
                    if v_isSharedCheck_2205_ == 0 {
                        v___x_2200_ = v___x_2189_;
                        v_isShared_2201_ = v_isSharedCheck_2205_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2198_);
                        crate::leanh::lean_dec(v___x_2189_);
                        v___x_2200_ = crate::leanh::lean_box(0);
                        v_isShared_2201_ = v_isSharedCheck_2205_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2193_ == 0 {
                    v___x_2195_ = v___x_2192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
                    v___x_2195_ = v_reuseFailAlloc_2196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2195_;
            }
            3 => {
                if v_isShared_2201_ == 0 {
                    v___x_2203_ = v___x_2200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(
    mut v_mvarId_2206_: *mut crate::leanh::LeanObject,
    mut v_x_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2206_,
        v_x_2207_,
        v___y_2208_,
        v___y_2209_,
        v___y_2210_,
        v___y_2211_,
    );
    crate::leanh::lean_dec(v___y_2211_);
    crate::leanh::lean_dec_ref(v___y_2210_);
    crate::leanh::lean_dec(v___y_2209_);
    crate::leanh::lean_dec_ref(v___y_2208_);
    return v_res_2213_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(
    mut v_00_u03b1_2214_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2215_: *mut crate::leanh::LeanObject,
    mut v_x_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2215_,
        v_x_2216_,
        v___y_2217_,
        v___y_2218_,
        v___y_2219_,
        v___y_2220_,
    );
    return v___x_2222_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(
    mut v_00_u03b1_2223_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2224_: *mut crate::leanh::LeanObject,
    mut v_x_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
    mut v___y_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(
        v_00_u03b1_2223_,
        v_mvarId_2224_,
        v_x_2225_,
        v___y_2226_,
        v___y_2227_,
        v___y_2228_,
        v___y_2229_,
    );
    crate::leanh::lean_dec(v___y_2229_);
    crate::leanh::lean_dec_ref(v___y_2228_);
    crate::leanh::lean_dec(v___y_2227_);
    crate::leanh::lean_dec_ref(v___y_2226_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_2232_: *mut crate::leanh::LeanObject,
    mut v_x_2233_: *mut crate::leanh::LeanObject,
    mut v_x_2234_: *mut crate::leanh::LeanObject,
    mut v_x_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2236_ = crate::leanh::lean_ctor_get(v_x_2232_, 0);
                v_vs_2237_ = crate::leanh::lean_ctor_get(v_x_2232_, 1);
                v_isSharedCheck_2261_ = (!crate::leanh::lean_is_exclusive(v_x_2232_)) as u8;
                if v_isSharedCheck_2261_ == 0 {
                    v___x_2239_ = v_x_2232_;
                    v_isShared_2240_ = v_isSharedCheck_2261_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2237_);
                    crate::leanh::lean_inc(v_ks_2236_);
                    crate::leanh::lean_dec(v_x_2232_);
                    v___x_2239_ = crate::leanh::lean_box(0);
                    v_isShared_2240_ = v_isSharedCheck_2261_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2241_ = lean_array_get_size(v_ks_2236_);
                v___x_2242_ = lean_nat_dec_lt(v_x_2233_, v___x_2241_);
                if v___x_2242_ == 0 {
                    crate::leanh::lean_dec(v_x_2233_);
                    v___x_2243_ = lean_array_push(v_ks_2236_, v_x_2234_);
                    v___x_2244_ = lean_array_push(v_vs_2237_, v_x_2235_);
                    if v_isShared_2240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2239_, 1, v___x_2244_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2243_);
                        v___x_2246_ = v___x_2239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2244_);
                        v___x_2246_ = v_reuseFailAlloc_2247_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2248_ = lean_array_fget_borrowed(v_ks_2236_, v_x_2233_);
                    v___x_2249_ = l_Lean_instBEqMVarId_beq(v_x_2234_, v_k_x27_2248_);
                    if v___x_2249_ == 0 {
                        if v_isShared_2240_ == 0 {
                            v___x_2251_ = v___x_2239_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2255_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_ks_2236_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_vs_2237_);
                            v___x_2251_ = v_reuseFailAlloc_2255_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2256_ = lean_array_fset(v_ks_2236_, v_x_2233_, v_x_2234_);
                        v___x_2257_ = lean_array_fset(v_vs_2237_, v_x_2233_, v_x_2235_);
                        crate::leanh::lean_dec(v_x_2233_);
                        if v_isShared_2240_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2239_, 1, v___x_2257_);
                            crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2256_);
                            v___x_2259_ = v___x_2239_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2260_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2256_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2257_);
                            v___x_2259_ = v_reuseFailAlloc_2260_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2246_;
            }
            3 => {
                v___x_2252_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2253_ = lean_nat_add(v_x_2233_, v___x_2252_);
                crate::leanh::lean_dec(v_x_2233_);
                v_x_2232_ = v___x_2251_;
                v_x_2233_ = v___x_2253_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_2262_: *mut crate::leanh::LeanObject,
    mut v_k_2263_: *mut crate::leanh::LeanObject,
    mut v_v_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2266_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_2262_, v___x_2265_, v_k_2263_, v_v_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2267_: usize = 0;
    let mut v___x_2268_: usize = 0;
    let mut v___x_2269_: usize = 0;
    v___x_2267_ = 5usize;
    v___x_2268_ = 1usize;
    v___x_2269_ = lean_usize_shift_left(v___x_2268_, v___x_2267_);
    return v___x_2269_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: usize = 0;
    let mut v___x_2272_: usize = 0;
    v___x_2270_ = 1usize;
    v___x_2271_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_2272_ = lean_usize_sub(v___x_2271_, v___x_2270_);
    return v___x_2272_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2273_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(
    mut v_x_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: usize,
    mut v_x_2276_: usize,
    mut v_x_2277_: *mut crate::leanh::LeanObject,
    mut v_x_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2283_: usize = 0;
    let mut v_j_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v_v_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_node_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_unused_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: u8 = 0;
    let mut v_ks_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: usize = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2274_) == 0 {
                    v_es_2279_ = crate::leanh::lean_ctor_get(v_x_2274_, 0);
                    v___x_2280_ = 5usize;
                    v___x_2281_ = 1usize;
                    v___x_2282_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2283_ = lean_usize_land(v_x_2275_, v___x_2282_);
                    v_j_2284_ = lean_usize_to_nat(v___x_2283_);
                    v___x_2285_ = lean_array_get_size(v_es_2279_);
                    v___x_2286_ = lean_nat_dec_lt(v_j_2284_, v___x_2285_);
                    if v___x_2286_ == 0 {
                        crate::leanh::lean_dec(v_j_2284_);
                        crate::leanh::lean_dec(v_x_2278_);
                        crate::leanh::lean_dec(v_x_2277_);
                        return v_x_2274_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2279_);
                        v_isSharedCheck_2323_ = (!crate::leanh::lean_is_exclusive(v_x_2274_)) as u8;
                        if v_isSharedCheck_2323_ == 0 {
                            v_unused_2324_ = crate::leanh::lean_ctor_get(v_x_2274_, 0);
                            crate::leanh::lean_dec(v_unused_2324_);
                            v___x_2288_ = v_x_2274_;
                            v_isShared_2289_ = v_isSharedCheck_2323_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2274_);
                            v___x_2288_ = crate::leanh::lean_box(0);
                            v_isShared_2289_ = v_isSharedCheck_2323_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2325_ = crate::leanh::lean_ctor_get(v_x_2274_, 0);
                    v_vs_2326_ = crate::leanh::lean_ctor_get(v_x_2274_, 1);
                    v_isSharedCheck_2346_ = (!crate::leanh::lean_is_exclusive(v_x_2274_)) as u8;
                    if v_isSharedCheck_2346_ == 0 {
                        v___x_2328_ = v_x_2274_;
                        v_isShared_2329_ = v_isSharedCheck_2346_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2326_);
                        crate::leanh::lean_inc(v_ks_2325_);
                        crate::leanh::lean_dec(v_x_2274_);
                        v___x_2328_ = crate::leanh::lean_box(0);
                        v_isShared_2329_ = v_isSharedCheck_2346_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2290_ = lean_array_fget(v_es_2279_, v_j_2284_);
                v___x_2291_ = crate::leanh::lean_box(0);
                v_xs_x27_2292_ = lean_array_fset(v_es_2279_, v_j_2284_, v___x_2291_);
                match crate::leanh::lean_obj_tag(v_v_2290_) {
                    0 => {
                        v_key_2299_ = crate::leanh::lean_ctor_get(v_v_2290_, 0);
                        v_val_2300_ = crate::leanh::lean_ctor_get(v_v_2290_, 1);
                        v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v_v_2290_)) as u8;
                        if v_isSharedCheck_2310_ == 0 {
                            v___x_2302_ = v_v_2290_;
                            v_isShared_2303_ = v_isSharedCheck_2310_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2300_);
                            crate::leanh::lean_inc(v_key_2299_);
                            crate::leanh::lean_dec(v_v_2290_);
                            v___x_2302_ = crate::leanh::lean_box(0);
                            v_isShared_2303_ = v_isSharedCheck_2310_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2311_ = crate::leanh::lean_ctor_get(v_v_2290_, 0);
                        v_isSharedCheck_2321_ = (!crate::leanh::lean_is_exclusive(v_v_2290_)) as u8;
                        if v_isSharedCheck_2321_ == 0 {
                            v___x_2313_ = v_v_2290_;
                            v_isShared_2314_ = v_isSharedCheck_2321_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2311_);
                            crate::leanh::lean_dec(v_v_2290_);
                            v___x_2313_ = crate::leanh::lean_box(0);
                            v_isShared_2314_ = v_isSharedCheck_2321_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2322_, 0, v_x_2277_);
                        crate::leanh::lean_ctor_set(v___x_2322_, 1, v_x_2278_);
                        v___y_2294_ = v___x_2322_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2295_ = lean_array_fset(v_xs_x27_2292_, v_j_2284_, v___y_2294_);
                crate::leanh::lean_dec(v_j_2284_);
                if v_isShared_2289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2295_);
                    v___x_2297_ = v___x_2288_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2297_;
            }
            4 => {
                v___x_2304_ = l_Lean_instBEqMVarId_beq(v_x_2277_, v_key_2299_);
                if v___x_2304_ == 0 {
                    crate::leanh::lean_del_object(v___x_2302_);
                    v___x_2305_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2299_,
                        v_val_2300_,
                        v_x_2277_,
                        v_x_2278_,
                    );
                    v___x_2306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2306_, 0, v___x_2305_);
                    v___y_2294_ = v___x_2306_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2300_);
                    crate::leanh::lean_dec(v_key_2299_);
                    if v_isShared_2303_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2302_, 1, v_x_2278_);
                        crate::leanh::lean_ctor_set(v___x_2302_, 0, v_x_2277_);
                        v___x_2308_ = v___x_2302_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_x_2277_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_x_2278_);
                        v___x_2308_ = v_reuseFailAlloc_2309_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2294_ = v___x_2308_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2315_ = lean_usize_shift_right(v_x_2275_, v___x_2280_);
                v___x_2316_ = lean_usize_add(v_x_2276_, v___x_2281_);
                v___x_2317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_node_2311_, v___x_2315_, v___x_2316_, v_x_2277_, v_x_2278_);
                if v_isShared_2314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2317_);
                    v___x_2319_ = v___x_2313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2294_ = v___x_2319_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2329_ == 0 {
                    v___x_2331_ = v___x_2328_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_ks_2325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_vs_2326_);
                    v___x_2331_ = v_reuseFailAlloc_2345_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2332_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v___x_2331_, v_x_2277_, v_x_2278_);
                v___x_2340_ = 7usize;
                v___x_2341_ = lean_usize_dec_le(v___x_2340_, v_x_2276_);
                if v___x_2341_ == 0 {
                    v___x_2342_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2332_);
                    v___x_2343_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
                    crate::leanh::lean_dec(v___x_2342_);
                    v___y_2334_ = v___x_2344_;
                    state = 10;
                    continue;
                } else {
                    v___y_2334_ = v___x_2341_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2334_ == 0 {
                    v_ks_2335_ = crate::leanh::lean_ctor_get(v_newNode_2332_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2335_);
                    v_vs_2336_ = crate::leanh::lean_ctor_get(v_newNode_2332_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2336_);
                    crate::leanh::lean_dec_ref(v_newNode_2332_);
                    v___x_2337_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2338_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_2339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2276_, v_ks_2335_, v_vs_2336_, v___x_2337_, v___x_2338_);
                    crate::leanh::lean_dec_ref(v_vs_2336_);
                    crate::leanh::lean_dec_ref(v_ks_2335_);
                    return v___x_2339_;
                } else {
                    return v_newNode_2332_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_2347_: usize,
    mut v_keys_2348_: *mut crate::leanh::LeanObject,
    mut v_vals_2349_: *mut crate::leanh::LeanObject,
    mut v_i_2350_: *mut crate::leanh::LeanObject,
    mut v_entries_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u8 = 0;
    let mut v_k_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u64 = 0;
    let mut v_h_2357_: usize = 0;
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v_h_2363_: usize = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2352_ = lean_array_get_size(v_keys_2348_);
                v___x_2353_ = lean_nat_dec_lt(v_i_2350_, v___x_2352_);
                if v___x_2353_ == 0 {
                    crate::leanh::lean_dec(v_i_2350_);
                    return v_entries_2351_;
                } else {
                    v_k_2354_ = lean_array_fget_borrowed(v_keys_2348_, v_i_2350_);
                    v_v_2355_ = lean_array_fget_borrowed(v_vals_2349_, v_i_2350_);
                    v___x_2356_ = l_Lean_instHashableMVarId_hash(v_k_2354_);
                    v_h_2357_ = lean_uint64_to_usize(v___x_2356_);
                    v___x_2358_ = 5usize;
                    v___x_2359_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2360_ = 1usize;
                    v___x_2361_ = lean_usize_sub(v_depth_2347_, v___x_2360_);
                    v___x_2362_ = lean_usize_mul(v___x_2358_, v___x_2361_);
                    v_h_2363_ = lean_usize_shift_right(v_h_2357_, v___x_2362_);
                    v___x_2364_ = lean_nat_add(v_i_2350_, v___x_2359_);
                    crate::leanh::lean_dec(v_i_2350_);
                    crate::leanh::lean_inc(v_v_2355_);
                    crate::leanh::lean_inc(v_k_2354_);
                    v___x_2365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_entries_2351_, v_h_2363_, v_depth_2347_, v_k_2354_, v_v_2355_);
                    v_i_2350_ = v___x_2364_;
                    v_entries_2351_ = v___x_2365_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_2367_: *mut crate::leanh::LeanObject,
    mut v_keys_2368_: *mut crate::leanh::LeanObject,
    mut v_vals_2369_: *mut crate::leanh::LeanObject,
    mut v_i_2370_: *mut crate::leanh::LeanObject,
    mut v_entries_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2372_: usize = 0;
    let mut v_res_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2372_ = crate::leanh::lean_unbox_usize(v_depth_2367_);
    crate::leanh::lean_dec(v_depth_2367_);
    v_res_2373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_2372_, v_keys_2368_, v_vals_2369_, v_i_2370_, v_entries_2371_);
    crate::leanh::lean_dec_ref(v_vals_2369_);
    crate::leanh::lean_dec_ref(v_keys_2368_);
    return v_res_2373_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_2374_: *mut crate::leanh::LeanObject,
    mut v_x_2375_: *mut crate::leanh::LeanObject,
    mut v_x_2376_: *mut crate::leanh::LeanObject,
    mut v_x_2377_: *mut crate::leanh::LeanObject,
    mut v_x_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1323__boxed_2379_: usize = 0;
    let mut v_x_1324__boxed_2380_: usize = 0;
    let mut v_res_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1323__boxed_2379_ = crate::leanh::lean_unbox_usize(v_x_2375_);
    crate::leanh::lean_dec(v_x_2375_);
    v_x_1324__boxed_2380_ = crate::leanh::lean_unbox_usize(v_x_2376_);
    crate::leanh::lean_dec(v_x_2376_);
    v_res_2381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2374_, v_x_1323__boxed_2379_, v_x_1324__boxed_2380_, v_x_2377_, v_x_2378_);
    return v_res_2381_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(
    mut v_x_2382_: *mut crate::leanh::LeanObject,
    mut v_x_2383_: *mut crate::leanh::LeanObject,
    mut v_x_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: u64 = 0;
    let mut v___x_2386_: usize = 0;
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l_Lean_instHashableMVarId_hash(v_x_2383_);
    v___x_2386_ = lean_uint64_to_usize(v___x_2385_);
    v___x_2387_ = 1usize;
    v___x_2388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2382_, v___x_2386_, v___x_2387_, v_x_2383_, v_x_2384_);
    return v___x_2388_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
    mut v_mvarId_2389_: *mut crate::leanh::LeanObject,
    mut v_val_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v_depth_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2393_ = lean_st_ref_take(v___y_2391_);
                v_mctx_2394_ = crate::leanh::lean_ctor_get(v___x_2393_, 0);
                v_cache_2395_ = crate::leanh::lean_ctor_get(v___x_2393_, 1);
                v_zetaDeltaFVarIds_2396_ = crate::leanh::lean_ctor_get(v___x_2393_, 2);
                v_postponed_2397_ = crate::leanh::lean_ctor_get(v___x_2393_, 3);
                v_diag_2398_ = crate::leanh::lean_ctor_get(v___x_2393_, 4);
                v_isSharedCheck_2426_ = (!crate::leanh::lean_is_exclusive(v___x_2393_)) as u8;
                if v_isSharedCheck_2426_ == 0 {
                    v___x_2400_ = v___x_2393_;
                    v_isShared_2401_ = v_isSharedCheck_2426_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2398_);
                    crate::leanh::lean_inc(v_postponed_2397_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2396_);
                    crate::leanh::lean_inc(v_cache_2395_);
                    crate::leanh::lean_inc(v_mctx_2394_);
                    crate::leanh::lean_dec(v___x_2393_);
                    v___x_2400_ = crate::leanh::lean_box(0);
                    v_isShared_2401_ = v_isSharedCheck_2426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2402_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 0);
                v_levelAssignDepth_2403_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 1);
                v_lmvarCounter_2404_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 2);
                v_mvarCounter_2405_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 3);
                v_lDecls_2406_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 4);
                v_decls_2407_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 5);
                v_userNames_2408_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 6);
                v_lAssignment_2409_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 7);
                v_eAssignment_2410_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 8);
                v_dAssignment_2411_ = crate::leanh::lean_ctor_get(v_mctx_2394_, 9);
                v_isSharedCheck_2425_ = (!crate::leanh::lean_is_exclusive(v_mctx_2394_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2413_ = v_mctx_2394_;
                    v_isShared_2414_ = v_isSharedCheck_2425_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2411_);
                    crate::leanh::lean_inc(v_eAssignment_2410_);
                    crate::leanh::lean_inc(v_lAssignment_2409_);
                    crate::leanh::lean_inc(v_userNames_2408_);
                    crate::leanh::lean_inc(v_decls_2407_);
                    crate::leanh::lean_inc(v_lDecls_2406_);
                    crate::leanh::lean_inc(v_mvarCounter_2405_);
                    crate::leanh::lean_inc(v_lmvarCounter_2404_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2403_);
                    crate::leanh::lean_inc(v_depth_2402_);
                    crate::leanh::lean_dec(v_mctx_2394_);
                    v___x_2413_ = crate::leanh::lean_box(0);
                    v_isShared_2414_ = v_isSharedCheck_2425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_2410_, v_mvarId_2389_, v_val_2390_);
                if v_isShared_2414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2413_, 8, v___x_2415_);
                    v___x_2417_ = v___x_2413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_depth_2402_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2424_,
                        1,
                        v_levelAssignDepth_2403_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_lmvarCounter_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_mvarCounter_2405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_lDecls_2406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 5, v_decls_2407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 6, v_userNames_2408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 7, v_lAssignment_2409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 8, v___x_2415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 9, v_dAssignment_2411_);
                    v___x_2417_ = v_reuseFailAlloc_2424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2400_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2400_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_cache_2395_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2423_,
                        2,
                        v_zetaDeltaFVarIds_2396_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_postponed_2397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_diag_2398_);
                    v___x_2419_ = v_reuseFailAlloc_2423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2420_ = lean_st_ref_set(v___y_2391_, v___x_2419_);
                v___x_2421_ = crate::leanh::lean_box(0);
                v___x_2422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2422_, 0, v___x_2421_);
                return v___x_2422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(
    mut v_mvarId_2427_: *mut crate::leanh::LeanObject,
    mut v_val_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
        v_mvarId_2427_,
        v_val_2428_,
        v___y_2429_,
    );
    crate::leanh::lean_dec(v___y_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Lean_MVarId_assert___lam__0(
    mut v_mvarId_2432_: *mut crate::leanh::LeanObject,
    mut v___x_2433_: *mut crate::leanh::LeanObject,
    mut v_name_2434_: *mut crate::leanh::LeanObject,
    mut v_type_2435_: *mut crate::leanh::LeanObject,
    mut v_val_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_unused_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2465_: u8 = 0;
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2469_: u8 = 0;
    let mut v_a_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v_a_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_a_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2432_);
                v___x_2442_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2432_,
                    v___x_2433_,
                    v___y_2437_,
                    v___y_2438_,
                    v___y_2439_,
                    v___y_2440_,
                );
                if crate::leanh::lean_obj_tag(v___x_2442_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2442_, 1);
                    crate::leanh::lean_inc(v_mvarId_2432_);
                    v___x_2443_ = l_Lean_MVarId_getTag(
                        v_mvarId_2432_,
                        v___y_2437_,
                        v___y_2438_,
                        v___y_2439_,
                        v___y_2440_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2443_) == 0 {
                        v_a_2444_ = crate::leanh::lean_ctor_get(v___x_2443_, 0);
                        crate::leanh::lean_inc(v_a_2444_);
                        crate::leanh::lean_dec_ref_known(v___x_2443_, 1);
                        crate::leanh::lean_inc(v_mvarId_2432_);
                        v___x_2445_ = l_Lean_MVarId_getType(
                            v_mvarId_2432_,
                            v___y_2437_,
                            v___y_2438_,
                            v___y_2439_,
                            v___y_2440_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2445_) == 0 {
                            v_a_2446_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                            crate::leanh::lean_inc(v_a_2446_);
                            crate::leanh::lean_dec_ref_known(v___x_2445_, 1);
                            v___x_2447_ = 0;
                            v___x_2448_ =
                                l_Lean_mkForall(v_name_2434_, v___x_2447_, v_type_2435_, v_a_2446_);
                            v___x_2449_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___x_2448_,
                                v_a_2444_,
                                v___y_2437_,
                                v___y_2438_,
                                v___y_2439_,
                                v___y_2440_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2449_) == 0 {
                                v_a_2450_ = crate::leanh::lean_ctor_get(v___x_2449_, 0);
                                crate::leanh::lean_inc_n(v_a_2450_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2449_, 1);
                                v___x_2451_ = l_Lean_Expr_app___override(v_a_2450_, v_val_2436_);
                                v___x_2452_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2432_, v___x_2451_, v___y_2438_);
                                v_isSharedCheck_2460_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2452_)) as u8;
                                if v_isSharedCheck_2460_ == 0 {
                                    v_unused_2461_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                                    crate::leanh::lean_dec(v_unused_2461_);
                                    v___x_2454_ = v___x_2452_;
                                    v_isShared_2455_ = v_isSharedCheck_2460_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2452_);
                                    v___x_2454_ = crate::leanh::lean_box(0);
                                    v_isShared_2455_ = v_isSharedCheck_2460_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_val_2436_);
                                crate::leanh::lean_dec(v_mvarId_2432_);
                                v_a_2462_ = crate::leanh::lean_ctor_get(v___x_2449_, 0);
                                v_isSharedCheck_2469_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2449_)) as u8;
                                if v_isSharedCheck_2469_ == 0 {
                                    v___x_2464_ = v___x_2449_;
                                    v_isShared_2465_ = v_isSharedCheck_2469_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2462_);
                                    crate::leanh::lean_dec(v___x_2449_);
                                    v___x_2464_ = crate::leanh::lean_box(0);
                                    v_isShared_2465_ = v_isSharedCheck_2469_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2444_);
                            crate::leanh::lean_dec_ref(v_val_2436_);
                            crate::leanh::lean_dec_ref(v_type_2435_);
                            crate::leanh::lean_dec(v_name_2434_);
                            crate::leanh::lean_dec(v_mvarId_2432_);
                            v_a_2470_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                            v_isSharedCheck_2477_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                            if v_isSharedCheck_2477_ == 0 {
                                v___x_2472_ = v___x_2445_;
                                v_isShared_2473_ = v_isSharedCheck_2477_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2470_);
                                crate::leanh::lean_dec(v___x_2445_);
                                v___x_2472_ = crate::leanh::lean_box(0);
                                v_isShared_2473_ = v_isSharedCheck_2477_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_val_2436_);
                        crate::leanh::lean_dec_ref(v_type_2435_);
                        crate::leanh::lean_dec(v_name_2434_);
                        crate::leanh::lean_dec(v_mvarId_2432_);
                        v_a_2478_ = crate::leanh::lean_ctor_get(v___x_2443_, 0);
                        v_isSharedCheck_2485_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2443_)) as u8;
                        if v_isSharedCheck_2485_ == 0 {
                            v___x_2480_ = v___x_2443_;
                            v_isShared_2481_ = v_isSharedCheck_2485_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2478_);
                            crate::leanh::lean_dec(v___x_2443_);
                            v___x_2480_ = crate::leanh::lean_box(0);
                            v_isShared_2481_ = v_isSharedCheck_2485_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_val_2436_);
                    crate::leanh::lean_dec_ref(v_type_2435_);
                    crate::leanh::lean_dec(v_name_2434_);
                    crate::leanh::lean_dec(v_mvarId_2432_);
                    v_a_2486_ = crate::leanh::lean_ctor_get(v___x_2442_, 0);
                    v_isSharedCheck_2493_ = (!crate::leanh::lean_is_exclusive(v___x_2442_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2488_ = v___x_2442_;
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2486_);
                        crate::leanh::lean_dec(v___x_2442_);
                        v___x_2488_ = crate::leanh::lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2456_ = l_Lean_Expr_mvarId_x21(v_a_2450_);
                crate::leanh::lean_dec(v_a_2450_);
                if v_isShared_2455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2454_, 0, v___x_2456_);
                    v___x_2458_ = v___x_2454_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
                    v___x_2458_ = v_reuseFailAlloc_2459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2458_;
            }
            3 => {
                if v_isShared_2465_ == 0 {
                    v___x_2467_ = v___x_2464_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
                    v___x_2467_ = v_reuseFailAlloc_2468_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2467_;
            }
            5 => {
                if v_isShared_2473_ == 0 {
                    v___x_2475_ = v___x_2472_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
                    v___x_2475_ = v_reuseFailAlloc_2476_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2475_;
            }
            7 => {
                if v_isShared_2481_ == 0 {
                    v___x_2483_ = v___x_2480_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
                    v___x_2483_ = v_reuseFailAlloc_2484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2483_;
            }
            9 => {
                if v_isShared_2489_ == 0 {
                    v___x_2491_ = v___x_2488_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
                    v___x_2491_ = v_reuseFailAlloc_2492_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assert___lam__0___boxed(
    mut v_mvarId_2494_: *mut crate::leanh::LeanObject,
    mut v___x_2495_: *mut crate::leanh::LeanObject,
    mut v_name_2496_: *mut crate::leanh::LeanObject,
    mut v_type_2497_: *mut crate::leanh::LeanObject,
    mut v_val_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2504_ = l_Lean_MVarId_assert___lam__0(
        v_mvarId_2494_,
        v___x_2495_,
        v_name_2496_,
        v_type_2497_,
        v_val_2498_,
        v___y_2499_,
        v___y_2500_,
        v___y_2501_,
        v___y_2502_,
    );
    crate::leanh::lean_dec(v___y_2502_);
    crate::leanh::lean_dec_ref(v___y_2501_);
    crate::leanh::lean_dec(v___y_2500_);
    crate::leanh::lean_dec_ref(v___y_2499_);
    return v_res_2504_;
}
pub unsafe fn l_Lean_MVarId_assert(
    mut v_mvarId_2508_: *mut crate::leanh::LeanObject,
    mut v_name_2509_: *mut crate::leanh::LeanObject,
    mut v_type_2510_: *mut crate::leanh::LeanObject,
    mut v_val_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2517_ = l_Lean_MVarId_assert___closed__1;
    crate::leanh::lean_inc(v_mvarId_2508_);
    v___f_2518_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_assert___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2518_, 0, v_mvarId_2508_);
    crate::leanh::lean_closure_set(v___f_2518_, 1, v___x_2517_);
    crate::leanh::lean_closure_set(v___f_2518_, 2, v_name_2509_);
    crate::leanh::lean_closure_set(v___f_2518_, 3, v_type_2510_);
    crate::leanh::lean_closure_set(v___f_2518_, 4, v_val_2511_);
    v___x_2519_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2508_,
        v___f_2518_,
        v_a_2512_,
        v_a_2513_,
        v_a_2514_,
        v_a_2515_,
    );
    return v___x_2519_;
}
pub unsafe fn l_Lean_MVarId_assert___boxed(
    mut v_mvarId_2520_: *mut crate::leanh::LeanObject,
    mut v_name_2521_: *mut crate::leanh::LeanObject,
    mut v_type_2522_: *mut crate::leanh::LeanObject,
    mut v_val_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Lean_MVarId_assert(
        v_mvarId_2520_,
        v_name_2521_,
        v_type_2522_,
        v_val_2523_,
        v_a_2524_,
        v_a_2525_,
        v_a_2526_,
        v_a_2527_,
    );
    crate::leanh::lean_dec(v_a_2527_);
    crate::leanh::lean_dec_ref(v_a_2526_);
    crate::leanh::lean_dec(v_a_2525_);
    crate::leanh::lean_dec_ref(v_a_2524_);
    return v_res_2529_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(
    mut v_mvarId_2530_: *mut crate::leanh::LeanObject,
    mut v_val_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
        v_mvarId_2530_,
        v_val_2531_,
        v___y_2533_,
    );
    return v___x_2537_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(
    mut v_mvarId_2538_: *mut crate::leanh::LeanObject,
    mut v_val_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2545_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(
        v_mvarId_2538_,
        v_val_2539_,
        v___y_2540_,
        v___y_2541_,
        v___y_2542_,
        v___y_2543_,
    );
    crate::leanh::lean_dec(v___y_2543_);
    crate::leanh::lean_dec_ref(v___y_2542_);
    crate::leanh::lean_dec(v___y_2541_);
    crate::leanh::lean_dec_ref(v___y_2540_);
    return v_res_2545_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(
    mut v_00_u03b2_2546_: *mut crate::leanh::LeanObject,
    mut v_x_2547_: *mut crate::leanh::LeanObject,
    mut v_x_2548_: *mut crate::leanh::LeanObject,
    mut v_x_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_2547_, v_x_2548_, v_x_2549_);
    return v___x_2550_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2551_: *mut crate::leanh::LeanObject,
    mut v_x_2552_: *mut crate::leanh::LeanObject,
    mut v_x_2553_: usize,
    mut v_x_2554_: usize,
    mut v_x_2555_: *mut crate::leanh::LeanObject,
    mut v_x_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2552_, v_x_2553_, v_x_2554_, v_x_2555_, v_x_2556_);
    return v___x_2557_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2558_: *mut crate::leanh::LeanObject,
    mut v_x_2559_: *mut crate::leanh::LeanObject,
    mut v_x_2560_: *mut crate::leanh::LeanObject,
    mut v_x_2561_: *mut crate::leanh::LeanObject,
    mut v_x_2562_: *mut crate::leanh::LeanObject,
    mut v_x_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1711__boxed_2564_: usize = 0;
    let mut v_x_1712__boxed_2565_: usize = 0;
    let mut v_res_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1711__boxed_2564_ = crate::leanh::lean_unbox_usize(v_x_2560_);
    crate::leanh::lean_dec(v_x_2560_);
    v_x_1712__boxed_2565_ = crate::leanh::lean_unbox_usize(v_x_2561_);
    crate::leanh::lean_dec(v_x_2561_);
    v_res_2566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_2558_, v_x_2559_, v_x_1711__boxed_2564_, v_x_1712__boxed_2565_, v_x_2562_, v_x_2563_);
    return v_res_2566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_2567_: *mut crate::leanh::LeanObject,
    mut v_n_2568_: *mut crate::leanh::LeanObject,
    mut v_k_2569_: *mut crate::leanh::LeanObject,
    mut v_v_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2571_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_2568_, v_k_2569_, v_v_2570_);
    return v___x_2571_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_2572_: *mut crate::leanh::LeanObject,
    mut v_depth_2573_: usize,
    mut v_keys_2574_: *mut crate::leanh::LeanObject,
    mut v_vals_2575_: *mut crate::leanh::LeanObject,
    mut v_heq_2576_: *mut crate::leanh::LeanObject,
    mut v_i_2577_: *mut crate::leanh::LeanObject,
    mut v_entries_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_2573_, v_keys_2574_, v_vals_2575_, v_i_2577_, v_entries_2578_);
    return v___x_2579_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_2580_: *mut crate::leanh::LeanObject,
    mut v_depth_2581_: *mut crate::leanh::LeanObject,
    mut v_keys_2582_: *mut crate::leanh::LeanObject,
    mut v_vals_2583_: *mut crate::leanh::LeanObject,
    mut v_heq_2584_: *mut crate::leanh::LeanObject,
    mut v_i_2585_: *mut crate::leanh::LeanObject,
    mut v_entries_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2587_ = crate::leanh::lean_unbox_usize(v_depth_2581_);
    crate::leanh::lean_dec(v_depth_2581_);
    v_res_2588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2580_, v_depth_boxed_2587_, v_keys_2582_, v_vals_2583_, v_heq_2584_, v_i_2585_, v_entries_2586_);
    crate::leanh::lean_dec_ref(v_vals_2583_);
    crate::leanh::lean_dec_ref(v_keys_2582_);
    return v_res_2588_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2589_: *mut crate::leanh::LeanObject,
    mut v_x_2590_: *mut crate::leanh::LeanObject,
    mut v_x_2591_: *mut crate::leanh::LeanObject,
    mut v_x_2592_: *mut crate::leanh::LeanObject,
    mut v_x_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_2590_, v_x_2591_, v_x_2592_, v_x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_MVarId_note(
    mut v_g_2595_: *mut crate::leanh::LeanObject,
    mut v_h_2596_: *mut crate::leanh::LeanObject,
    mut v_v_2597_: *mut crate::leanh::LeanObject,
    mut v_t_x3f_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_a_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_val_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_x3f_2598_) == 0 {
                    crate::leanh::lean_inc(v_a_2602_);
                    crate::leanh::lean_inc_ref(v_a_2601_);
                    crate::leanh::lean_inc(v_a_2600_);
                    crate::leanh::lean_inc_ref(v_a_2599_);
                    crate::leanh::lean_inc_ref(v_v_2597_);
                    v___x_2618_ =
                        lean_infer_type(v_v_2597_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
                    if crate::leanh::lean_obj_tag(v___x_2618_) == 0 {
                        v_a_2619_ = crate::leanh::lean_ctor_get(v___x_2618_, 0);
                        crate::leanh::lean_inc(v_a_2619_);
                        crate::leanh::lean_dec_ref_known(v___x_2618_, 1);
                        v_a_2605_ = v_a_2619_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_v_2597_);
                        crate::leanh::lean_dec(v_h_2596_);
                        crate::leanh::lean_dec(v_g_2595_);
                        v_a_2620_ = crate::leanh::lean_ctor_get(v___x_2618_, 0);
                        v_isSharedCheck_2627_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2618_)) as u8;
                        if v_isSharedCheck_2627_ == 0 {
                            v___x_2622_ = v___x_2618_;
                            v_isShared_2623_ = v_isSharedCheck_2627_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2620_);
                            crate::leanh::lean_dec(v___x_2618_);
                            v___x_2622_ = crate::leanh::lean_box(0);
                            v_isShared_2623_ = v_isSharedCheck_2627_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_val_2628_ = crate::leanh::lean_ctor_get(v_t_x3f_2598_, 0);
                    crate::leanh::lean_inc(v_val_2628_);
                    crate::leanh::lean_dec_ref_known(v_t_x3f_2598_, 1);
                    v_a_2605_ = v_val_2628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2606_ = l_Lean_MVarId_assert(
                    v_g_2595_, v_h_2596_, v_a_2605_, v_v_2597_, v_a_2599_, v_a_2600_, v_a_2601_,
                    v_a_2602_,
                );
                if crate::leanh::lean_obj_tag(v___x_2606_) == 0 {
                    v_a_2607_ = crate::leanh::lean_ctor_get(v___x_2606_, 0);
                    crate::leanh::lean_inc(v_a_2607_);
                    crate::leanh::lean_dec_ref_known(v___x_2606_, 1);
                    v___x_2608_ = 1;
                    v___x_2609_ = l_Lean_Meta_intro1Core(
                        v_a_2607_,
                        v___x_2608_,
                        v_a_2599_,
                        v_a_2600_,
                        v_a_2601_,
                        v_a_2602_,
                    );
                    return v___x_2609_;
                } else {
                    v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2606_, 0);
                    v_isSharedCheck_2617_ = (!crate::leanh::lean_is_exclusive(v___x_2606_)) as u8;
                    if v_isSharedCheck_2617_ == 0 {
                        v___x_2612_ = v___x_2606_;
                        v_isShared_2613_ = v_isSharedCheck_2617_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2610_);
                        crate::leanh::lean_dec(v___x_2606_);
                        v___x_2612_ = crate::leanh::lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2617_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2613_ == 0 {
                    v___x_2615_ = v___x_2612_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
                    v___x_2615_ = v_reuseFailAlloc_2616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2615_;
            }
            4 => {
                if v_isShared_2623_ == 0 {
                    v___x_2625_ = v___x_2622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
                    v___x_2625_ = v_reuseFailAlloc_2626_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_note___boxed(
    mut v_g_2629_: *mut crate::leanh::LeanObject,
    mut v_h_2630_: *mut crate::leanh::LeanObject,
    mut v_v_2631_: *mut crate::leanh::LeanObject,
    mut v_t_x3f_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_MVarId_note(
        v_g_2629_,
        v_h_2630_,
        v_v_2631_,
        v_t_x3f_2632_,
        v_a_2633_,
        v_a_2634_,
        v_a_2635_,
        v_a_2636_,
    );
    crate::leanh::lean_dec(v_a_2636_);
    crate::leanh::lean_dec_ref(v_a_2635_);
    crate::leanh::lean_dec(v_a_2634_);
    crate::leanh::lean_dec_ref(v_a_2633_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_MVarId_define___lam__0(
    mut v_mvarId_2639_: *mut crate::leanh::LeanObject,
    mut v___x_2640_: *mut crate::leanh::LeanObject,
    mut v_name_2641_: *mut crate::leanh::LeanObject,
    mut v_type_2642_: *mut crate::leanh::LeanObject,
    mut v_val_2643_: *mut crate::leanh::LeanObject,
    mut v___y_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2661_: u8 = 0;
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_unused_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_a_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_a_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2695_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2639_);
                v___x_2649_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2639_,
                    v___x_2640_,
                    v___y_2644_,
                    v___y_2645_,
                    v___y_2646_,
                    v___y_2647_,
                );
                if crate::leanh::lean_obj_tag(v___x_2649_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2649_, 1);
                    crate::leanh::lean_inc(v_mvarId_2639_);
                    v___x_2650_ = l_Lean_MVarId_getTag(
                        v_mvarId_2639_,
                        v___y_2644_,
                        v___y_2645_,
                        v___y_2646_,
                        v___y_2647_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2650_) == 0 {
                        v_a_2651_ = crate::leanh::lean_ctor_get(v___x_2650_, 0);
                        crate::leanh::lean_inc(v_a_2651_);
                        crate::leanh::lean_dec_ref_known(v___x_2650_, 1);
                        crate::leanh::lean_inc(v_mvarId_2639_);
                        v___x_2652_ = l_Lean_MVarId_getType(
                            v_mvarId_2639_,
                            v___y_2644_,
                            v___y_2645_,
                            v___y_2646_,
                            v___y_2647_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2652_) == 0 {
                            v_a_2653_ = crate::leanh::lean_ctor_get(v___x_2652_, 0);
                            crate::leanh::lean_inc(v_a_2653_);
                            crate::leanh::lean_dec_ref_known(v___x_2652_, 1);
                            v___x_2654_ = 0;
                            v___x_2655_ = l_Lean_Expr_letE___override(
                                v_name_2641_,
                                v_type_2642_,
                                v_val_2643_,
                                v_a_2653_,
                                v___x_2654_,
                            );
                            v___x_2656_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___x_2655_,
                                v_a_2651_,
                                v___y_2644_,
                                v___y_2645_,
                                v___y_2646_,
                                v___y_2647_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                                v_a_2657_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                                crate::leanh::lean_inc_n(v_a_2657_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2656_, 1);
                                v___x_2658_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2639_, v_a_2657_, v___y_2645_);
                                v_isSharedCheck_2666_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2658_)) as u8;
                                if v_isSharedCheck_2666_ == 0 {
                                    v_unused_2667_ = crate::leanh::lean_ctor_get(v___x_2658_, 0);
                                    crate::leanh::lean_dec(v_unused_2667_);
                                    v___x_2660_ = v___x_2658_;
                                    v_isShared_2661_ = v_isSharedCheck_2666_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2658_);
                                    v___x_2660_ = crate::leanh::lean_box(0);
                                    v_isShared_2661_ = v_isSharedCheck_2666_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_mvarId_2639_);
                                v_a_2668_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                                v_isSharedCheck_2675_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2656_)) as u8;
                                if v_isSharedCheck_2675_ == 0 {
                                    v___x_2670_ = v___x_2656_;
                                    v_isShared_2671_ = v_isSharedCheck_2675_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2668_);
                                    crate::leanh::lean_dec(v___x_2656_);
                                    v___x_2670_ = crate::leanh::lean_box(0);
                                    v_isShared_2671_ = v_isSharedCheck_2675_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2651_);
                            crate::leanh::lean_dec_ref(v_val_2643_);
                            crate::leanh::lean_dec_ref(v_type_2642_);
                            crate::leanh::lean_dec(v_name_2641_);
                            crate::leanh::lean_dec(v_mvarId_2639_);
                            v_a_2676_ = crate::leanh::lean_ctor_get(v___x_2652_, 0);
                            v_isSharedCheck_2683_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2652_)) as u8;
                            if v_isSharedCheck_2683_ == 0 {
                                v___x_2678_ = v___x_2652_;
                                v_isShared_2679_ = v_isSharedCheck_2683_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2676_);
                                crate::leanh::lean_dec(v___x_2652_);
                                v___x_2678_ = crate::leanh::lean_box(0);
                                v_isShared_2679_ = v_isSharedCheck_2683_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_val_2643_);
                        crate::leanh::lean_dec_ref(v_type_2642_);
                        crate::leanh::lean_dec(v_name_2641_);
                        crate::leanh::lean_dec(v_mvarId_2639_);
                        v_a_2684_ = crate::leanh::lean_ctor_get(v___x_2650_, 0);
                        v_isSharedCheck_2691_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2650_)) as u8;
                        if v_isSharedCheck_2691_ == 0 {
                            v___x_2686_ = v___x_2650_;
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2684_);
                            crate::leanh::lean_dec(v___x_2650_);
                            v___x_2686_ = crate::leanh::lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_val_2643_);
                    crate::leanh::lean_dec_ref(v_type_2642_);
                    crate::leanh::lean_dec(v_name_2641_);
                    crate::leanh::lean_dec(v_mvarId_2639_);
                    v_a_2692_ = crate::leanh::lean_ctor_get(v___x_2649_, 0);
                    v_isSharedCheck_2699_ = (!crate::leanh::lean_is_exclusive(v___x_2649_)) as u8;
                    if v_isSharedCheck_2699_ == 0 {
                        v___x_2694_ = v___x_2649_;
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2692_);
                        crate::leanh::lean_dec(v___x_2649_);
                        v___x_2694_ = crate::leanh::lean_box(0);
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2662_ = l_Lean_Expr_mvarId_x21(v_a_2657_);
                crate::leanh::lean_dec(v_a_2657_);
                if v_isShared_2661_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2660_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
                    v___x_2664_ = v_reuseFailAlloc_2665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2664_;
            }
            3 => {
                if v_isShared_2671_ == 0 {
                    v___x_2673_ = v___x_2670_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
                    v___x_2673_ = v_reuseFailAlloc_2674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2673_;
            }
            5 => {
                if v_isShared_2679_ == 0 {
                    v___x_2681_ = v___x_2678_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2681_;
            }
            7 => {
                if v_isShared_2687_ == 0 {
                    v___x_2689_ = v___x_2686_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
                    v___x_2689_ = v_reuseFailAlloc_2690_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2689_;
            }
            9 => {
                if v_isShared_2695_ == 0 {
                    v___x_2697_ = v___x_2694_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
                    v___x_2697_ = v_reuseFailAlloc_2698_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_define___lam__0___boxed(
    mut v_mvarId_2700_: *mut crate::leanh::LeanObject,
    mut v___x_2701_: *mut crate::leanh::LeanObject,
    mut v_name_2702_: *mut crate::leanh::LeanObject,
    mut v_type_2703_: *mut crate::leanh::LeanObject,
    mut v_val_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ = l_Lean_MVarId_define___lam__0(
        v_mvarId_2700_,
        v___x_2701_,
        v_name_2702_,
        v_type_2703_,
        v_val_2704_,
        v___y_2705_,
        v___y_2706_,
        v___y_2707_,
        v___y_2708_,
    );
    crate::leanh::lean_dec(v___y_2708_);
    crate::leanh::lean_dec_ref(v___y_2707_);
    crate::leanh::lean_dec(v___y_2706_);
    crate::leanh::lean_dec_ref(v___y_2705_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_MVarId_define(
    mut v_mvarId_2714_: *mut crate::leanh::LeanObject,
    mut v_name_2715_: *mut crate::leanh::LeanObject,
    mut v_type_2716_: *mut crate::leanh::LeanObject,
    mut v_val_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_MVarId_define___closed__1;
    crate::leanh::lean_inc(v_mvarId_2714_);
    v___f_2724_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_define___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2724_, 0, v_mvarId_2714_);
    crate::leanh::lean_closure_set(v___f_2724_, 1, v___x_2723_);
    crate::leanh::lean_closure_set(v___f_2724_, 2, v_name_2715_);
    crate::leanh::lean_closure_set(v___f_2724_, 3, v_type_2716_);
    crate::leanh::lean_closure_set(v___f_2724_, 4, v_val_2717_);
    v___x_2725_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2714_,
        v___f_2724_,
        v_a_2718_,
        v_a_2719_,
        v_a_2720_,
        v_a_2721_,
    );
    return v___x_2725_;
}
pub unsafe fn l_Lean_MVarId_define___boxed(
    mut v_mvarId_2726_: *mut crate::leanh::LeanObject,
    mut v_name_2727_: *mut crate::leanh::LeanObject,
    mut v_type_2728_: *mut crate::leanh::LeanObject,
    mut v_val_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
    mut v_a_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lean_MVarId_define(
        v_mvarId_2726_,
        v_name_2727_,
        v_type_2728_,
        v_val_2729_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
        v_a_2733_,
    );
    crate::leanh::lean_dec(v_a_2733_);
    crate::leanh::lean_dec_ref(v_a_2732_);
    crate::leanh::lean_dec(v_a_2731_);
    crate::leanh::lean_dec_ref(v_a_2730_);
    return v_res_2735_;
}
pub unsafe fn _init_l_Lean_MVarId_assertExt___lam__0___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2740_ = l_Lean_mkBVar(v___x_2739_);
    return v___x_2740_;
}
pub unsafe fn l_Lean_MVarId_assertExt___lam__0(
    mut v_mvarId_2741_: *mut crate::leanh::LeanObject,
    mut v___x_2742_: *mut crate::leanh::LeanObject,
    mut v_type_2743_: *mut crate::leanh::LeanObject,
    mut v_val_2744_: *mut crate::leanh::LeanObject,
    mut v_hName_2745_: *mut crate::leanh::LeanObject,
    mut v_name_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_unused_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v_a_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_a_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2826_: u8 = 0;
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2741_);
                v___x_2752_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2741_,
                    v___x_2742_,
                    v___y_2747_,
                    v___y_2748_,
                    v___y_2749_,
                    v___y_2750_,
                );
                if crate::leanh::lean_obj_tag(v___x_2752_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2752_, 1);
                    crate::leanh::lean_inc(v_mvarId_2741_);
                    v___x_2753_ = l_Lean_MVarId_getTag(
                        v_mvarId_2741_,
                        v___y_2747_,
                        v___y_2748_,
                        v___y_2749_,
                        v___y_2750_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2753_) == 0 {
                        v_a_2754_ = crate::leanh::lean_ctor_get(v___x_2753_, 0);
                        crate::leanh::lean_inc(v_a_2754_);
                        crate::leanh::lean_dec_ref_known(v___x_2753_, 1);
                        crate::leanh::lean_inc(v_mvarId_2741_);
                        v___x_2755_ = l_Lean_MVarId_getType(
                            v_mvarId_2741_,
                            v___y_2747_,
                            v___y_2748_,
                            v___y_2749_,
                            v___y_2750_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2755_) == 0 {
                            v_a_2756_ = crate::leanh::lean_ctor_get(v___x_2755_, 0);
                            crate::leanh::lean_inc(v_a_2756_);
                            crate::leanh::lean_dec_ref_known(v___x_2755_, 1);
                            crate::leanh::lean_inc_ref(v_type_2743_);
                            v___x_2757_ = l_Lean_Meta_getLevel(
                                v_type_2743_,
                                v___y_2747_,
                                v___y_2748_,
                                v___y_2749_,
                                v___y_2750_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2757_) == 0 {
                                v_a_2758_ = crate::leanh::lean_ctor_get(v___x_2757_, 0);
                                crate::leanh::lean_inc(v_a_2758_);
                                crate::leanh::lean_dec_ref_known(v___x_2757_, 1);
                                v___x_2759_ = l_Lean_MVarId_assertExt___lam__0___closed__1;
                                v___x_2760_ = crate::leanh::lean_box(0);
                                v___x_2761_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2761_, 0, v_a_2758_);
                                crate::leanh::lean_ctor_set(v___x_2761_, 1, v___x_2760_);
                                v___x_2762_ = l_Lean_mkConst(v___x_2759_, v___x_2761_);
                                v___x_2763_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_assertExt___lam__0___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_assertExt___lam__0___closed__2_once
                                    ),
                                    _init_l_Lean_MVarId_assertExt___lam__0___closed__2,
                                );
                                crate::leanh::lean_inc_ref(v_val_2744_);
                                crate::leanh::lean_inc_ref(v_type_2743_);
                                v___x_2764_ = l_Lean_mkApp3(
                                    v___x_2762_,
                                    v_type_2743_,
                                    v___x_2763_,
                                    v_val_2744_,
                                );
                                v___x_2765_ = 0;
                                v___x_2766_ = l_Lean_mkForall(
                                    v_hName_2745_,
                                    v___x_2765_,
                                    v___x_2764_,
                                    v_a_2756_,
                                );
                                v___x_2767_ = l_Lean_mkForall(
                                    v_name_2746_,
                                    v___x_2765_,
                                    v_type_2743_,
                                    v___x_2766_,
                                );
                                v___x_2768_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v___x_2767_,
                                    v_a_2754_,
                                    v___y_2747_,
                                    v___y_2748_,
                                    v___y_2749_,
                                    v___y_2750_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2768_) == 0 {
                                    v_a_2769_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                                    crate::leanh::lean_inc(v_a_2769_);
                                    crate::leanh::lean_dec_ref_known(v___x_2768_, 1);
                                    crate::leanh::lean_inc_ref(v_val_2744_);
                                    v___x_2770_ = l_Lean_Meta_mkEqRefl(
                                        v_val_2744_,
                                        v___y_2747_,
                                        v___y_2748_,
                                        v___y_2749_,
                                        v___y_2750_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2770_) == 0 {
                                        v_a_2771_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                                        crate::leanh::lean_inc(v_a_2771_);
                                        crate::leanh::lean_dec_ref_known(v___x_2770_, 1);
                                        crate::leanh::lean_inc(v_a_2769_);
                                        v___x_2772_ =
                                            l_Lean_mkAppB(v_a_2769_, v_val_2744_, v_a_2771_);
                                        v___x_2773_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2741_, v___x_2772_, v___y_2748_);
                                        v_isSharedCheck_2781_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2773_)) as u8;
                                        if v_isSharedCheck_2781_ == 0 {
                                            v_unused_2782_ =
                                                crate::leanh::lean_ctor_get(v___x_2773_, 0);
                                            crate::leanh::lean_dec(v_unused_2782_);
                                            v___x_2775_ = v___x_2773_;
                                            v_isShared_2776_ = v_isSharedCheck_2781_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2773_);
                                            v___x_2775_ = crate::leanh::lean_box(0);
                                            v_isShared_2776_ = v_isSharedCheck_2781_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2769_);
                                        crate::leanh::lean_dec_ref(v_val_2744_);
                                        crate::leanh::lean_dec(v_mvarId_2741_);
                                        v_a_2783_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                                        v_isSharedCheck_2790_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2770_)) as u8;
                                        if v_isSharedCheck_2790_ == 0 {
                                            v___x_2785_ = v___x_2770_;
                                            v_isShared_2786_ = v_isSharedCheck_2790_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2783_);
                                            crate::leanh::lean_dec(v___x_2770_);
                                            v___x_2785_ = crate::leanh::lean_box(0);
                                            v_isShared_2786_ = v_isSharedCheck_2790_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_val_2744_);
                                    crate::leanh::lean_dec(v_mvarId_2741_);
                                    v_a_2791_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                                    v_isSharedCheck_2798_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2768_)) as u8;
                                    if v_isSharedCheck_2798_ == 0 {
                                        v___x_2793_ = v___x_2768_;
                                        v_isShared_2794_ = v_isSharedCheck_2798_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2791_);
                                        crate::leanh::lean_dec(v___x_2768_);
                                        v___x_2793_ = crate::leanh::lean_box(0);
                                        v_isShared_2794_ = v_isSharedCheck_2798_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2756_);
                                crate::leanh::lean_dec(v_a_2754_);
                                crate::leanh::lean_dec(v_name_2746_);
                                crate::leanh::lean_dec(v_hName_2745_);
                                crate::leanh::lean_dec_ref(v_val_2744_);
                                crate::leanh::lean_dec_ref(v_type_2743_);
                                crate::leanh::lean_dec(v_mvarId_2741_);
                                v_a_2799_ = crate::leanh::lean_ctor_get(v___x_2757_, 0);
                                v_isSharedCheck_2806_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2757_)) as u8;
                                if v_isSharedCheck_2806_ == 0 {
                                    v___x_2801_ = v___x_2757_;
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2799_);
                                    crate::leanh::lean_dec(v___x_2757_);
                                    v___x_2801_ = crate::leanh::lean_box(0);
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2754_);
                            crate::leanh::lean_dec(v_name_2746_);
                            crate::leanh::lean_dec(v_hName_2745_);
                            crate::leanh::lean_dec_ref(v_val_2744_);
                            crate::leanh::lean_dec_ref(v_type_2743_);
                            crate::leanh::lean_dec(v_mvarId_2741_);
                            v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2755_, 0);
                            v_isSharedCheck_2814_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2755_)) as u8;
                            if v_isSharedCheck_2814_ == 0 {
                                v___x_2809_ = v___x_2755_;
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2807_);
                                crate::leanh::lean_dec(v___x_2755_);
                                v___x_2809_ = crate::leanh::lean_box(0);
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_2746_);
                        crate::leanh::lean_dec(v_hName_2745_);
                        crate::leanh::lean_dec_ref(v_val_2744_);
                        crate::leanh::lean_dec_ref(v_type_2743_);
                        crate::leanh::lean_dec(v_mvarId_2741_);
                        v_a_2815_ = crate::leanh::lean_ctor_get(v___x_2753_, 0);
                        v_isSharedCheck_2822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2753_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2753_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2815_);
                            crate::leanh::lean_dec(v___x_2753_);
                            v___x_2817_ = crate::leanh::lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2746_);
                    crate::leanh::lean_dec(v_hName_2745_);
                    crate::leanh::lean_dec_ref(v_val_2744_);
                    crate::leanh::lean_dec_ref(v_type_2743_);
                    crate::leanh::lean_dec(v_mvarId_2741_);
                    v_a_2823_ = crate::leanh::lean_ctor_get(v___x_2752_, 0);
                    v_isSharedCheck_2830_ = (!crate::leanh::lean_is_exclusive(v___x_2752_)) as u8;
                    if v_isSharedCheck_2830_ == 0 {
                        v___x_2825_ = v___x_2752_;
                        v_isShared_2826_ = v_isSharedCheck_2830_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2823_);
                        crate::leanh::lean_dec(v___x_2752_);
                        v___x_2825_ = crate::leanh::lean_box(0);
                        v_isShared_2826_ = v_isSharedCheck_2830_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2777_ = l_Lean_Expr_mvarId_x21(v_a_2769_);
                crate::leanh::lean_dec(v_a_2769_);
                if v_isShared_2776_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2775_, 0, v___x_2777_);
                    v___x_2779_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2779_;
            }
            3 => {
                if v_isShared_2786_ == 0 {
                    v___x_2788_ = v___x_2785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
                    v___x_2788_ = v_reuseFailAlloc_2789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2788_;
            }
            5 => {
                if v_isShared_2794_ == 0 {
                    v___x_2796_ = v___x_2793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2796_;
            }
            7 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2804_;
            }
            9 => {
                if v_isShared_2810_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2812_;
            }
            11 => {
                if v_isShared_2818_ == 0 {
                    v___x_2820_ = v___x_2817_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
                    v___x_2820_ = v_reuseFailAlloc_2821_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2820_;
            }
            13 => {
                if v_isShared_2826_ == 0 {
                    v___x_2828_ = v___x_2825_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
                    v___x_2828_ = v_reuseFailAlloc_2829_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assertExt___lam__0___boxed(
    mut v_mvarId_2831_: *mut crate::leanh::LeanObject,
    mut v___x_2832_: *mut crate::leanh::LeanObject,
    mut v_type_2833_: *mut crate::leanh::LeanObject,
    mut v_val_2834_: *mut crate::leanh::LeanObject,
    mut v_hName_2835_: *mut crate::leanh::LeanObject,
    mut v_name_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
    mut v___y_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ = l_Lean_MVarId_assertExt___lam__0(
        v_mvarId_2831_,
        v___x_2832_,
        v_type_2833_,
        v_val_2834_,
        v_hName_2835_,
        v_name_2836_,
        v___y_2837_,
        v___y_2838_,
        v___y_2839_,
        v___y_2840_,
    );
    crate::leanh::lean_dec(v___y_2840_);
    crate::leanh::lean_dec_ref(v___y_2839_);
    crate::leanh::lean_dec(v___y_2838_);
    crate::leanh::lean_dec_ref(v___y_2837_);
    return v_res_2842_;
}
pub unsafe fn l_Lean_MVarId_assertExt(
    mut v_mvarId_2843_: *mut crate::leanh::LeanObject,
    mut v_name_2844_: *mut crate::leanh::LeanObject,
    mut v_type_2845_: *mut crate::leanh::LeanObject,
    mut v_val_2846_: *mut crate::leanh::LeanObject,
    mut v_hName_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
    mut v_a_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_MVarId_assert___closed__1;
    crate::leanh::lean_inc(v_mvarId_2843_);
    v___f_2854_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_assertExt___lam__0___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2854_, 0, v_mvarId_2843_);
    crate::leanh::lean_closure_set(v___f_2854_, 1, v___x_2853_);
    crate::leanh::lean_closure_set(v___f_2854_, 2, v_type_2845_);
    crate::leanh::lean_closure_set(v___f_2854_, 3, v_val_2846_);
    crate::leanh::lean_closure_set(v___f_2854_, 4, v_hName_2847_);
    crate::leanh::lean_closure_set(v___f_2854_, 5, v_name_2844_);
    v___x_2855_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2843_,
        v___f_2854_,
        v_a_2848_,
        v_a_2849_,
        v_a_2850_,
        v_a_2851_,
    );
    return v___x_2855_;
}
pub unsafe fn l_Lean_MVarId_assertExt___boxed(
    mut v_mvarId_2856_: *mut crate::leanh::LeanObject,
    mut v_name_2857_: *mut crate::leanh::LeanObject,
    mut v_type_2858_: *mut crate::leanh::LeanObject,
    mut v_val_2859_: *mut crate::leanh::LeanObject,
    mut v_hName_2860_: *mut crate::leanh::LeanObject,
    mut v_a_2861_: *mut crate::leanh::LeanObject,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l_Lean_MVarId_assertExt(
        v_mvarId_2856_,
        v_name_2857_,
        v_type_2858_,
        v_val_2859_,
        v_hName_2860_,
        v_a_2861_,
        v_a_2862_,
        v_a_2863_,
        v_a_2864_,
    );
    crate::leanh::lean_dec(v_a_2864_);
    crate::leanh::lean_dec_ref(v_a_2863_);
    crate::leanh::lean_dec(v_a_2862_);
    crate::leanh::lean_dec_ref(v_a_2861_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(
    mut v_t_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2872_: u8 = 0;
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v_enabled_2888_: u8 = 0;
    let mut v_assignment_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2870_ = lean_st_ref_get(v___y_2868_);
                v_infoState_2871_ = crate::leanh::lean_ctor_get(v___x_2870_, 7);
                crate::leanh::lean_inc_ref(v_infoState_2871_);
                crate::leanh::lean_dec(v___x_2870_);
                v_enabled_2872_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_2871_);
                if v_enabled_2872_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_2867_);
                    v___x_2873_ = crate::leanh::lean_box(0);
                    v___x_2874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
                    return v___x_2874_;
                } else {
                    v___x_2875_ = lean_st_ref_take(v___y_2868_);
                    v_infoState_2876_ = crate::leanh::lean_ctor_get(v___x_2875_, 7);
                    v_env_2877_ = crate::leanh::lean_ctor_get(v___x_2875_, 0);
                    v_nextMacroScope_2878_ = crate::leanh::lean_ctor_get(v___x_2875_, 1);
                    v_ngen_2879_ = crate::leanh::lean_ctor_get(v___x_2875_, 2);
                    v_auxDeclNGen_2880_ = crate::leanh::lean_ctor_get(v___x_2875_, 3);
                    v_traceState_2881_ = crate::leanh::lean_ctor_get(v___x_2875_, 4);
                    v_cache_2882_ = crate::leanh::lean_ctor_get(v___x_2875_, 5);
                    v_messages_2883_ = crate::leanh::lean_ctor_get(v___x_2875_, 6);
                    v_snapshotTasks_2884_ = crate::leanh::lean_ctor_get(v___x_2875_, 8);
                    v_isSharedCheck_2906_ = (!crate::leanh::lean_is_exclusive(v___x_2875_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2886_ = v___x_2875_;
                        v_isShared_2887_ = v_isSharedCheck_2906_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_2884_);
                        crate::leanh::lean_inc(v_infoState_2876_);
                        crate::leanh::lean_inc(v_messages_2883_);
                        crate::leanh::lean_inc(v_cache_2882_);
                        crate::leanh::lean_inc(v_traceState_2881_);
                        crate::leanh::lean_inc(v_auxDeclNGen_2880_);
                        crate::leanh::lean_inc(v_ngen_2879_);
                        crate::leanh::lean_inc(v_nextMacroScope_2878_);
                        crate::leanh::lean_inc(v_env_2877_);
                        crate::leanh::lean_dec(v___x_2875_);
                        v___x_2886_ = crate::leanh::lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2906_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_2888_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_2876_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_2889_ = crate::leanh::lean_ctor_get(v_infoState_2876_, 0);
                v_lazyAssignment_2890_ = crate::leanh::lean_ctor_get(v_infoState_2876_, 1);
                v_trees_2891_ = crate::leanh::lean_ctor_get(v_infoState_2876_, 2);
                v_isSharedCheck_2905_ = (!crate::leanh::lean_is_exclusive(v_infoState_2876_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v___x_2893_ = v_infoState_2876_;
                    v_isShared_2894_ = v_isSharedCheck_2905_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_2891_);
                    crate::leanh::lean_inc(v_lazyAssignment_2890_);
                    crate::leanh::lean_inc(v_assignment_2889_);
                    crate::leanh::lean_dec(v_infoState_2876_);
                    v___x_2893_ = crate::leanh::lean_box(0);
                    v_isShared_2894_ = v_isSharedCheck_2905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2895_ = l_Lean_PersistentArray_push___redArg(v_trees_2891_, v_t_2867_);
                if v_isShared_2894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2893_, 2, v___x_2895_);
                    v___x_2897_ = v___x_2893_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2904_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_assignment_2889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_lazyAssignment_2890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2904_, 2, v___x_2895_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2904_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_2888_,
                    );
                    v___x_2897_ = v_reuseFailAlloc_2904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2886_, 7, v___x_2897_);
                    v___x_2899_ = v___x_2886_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_traceState_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_messages_2883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 7, v___x_2897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_snapshotTasks_2884_);
                    v___x_2899_ = v_reuseFailAlloc_2903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2900_ = lean_st_ref_set(v___y_2868_, v___x_2899_);
                v___x_2901_ = crate::leanh::lean_box(0);
                v___x_2902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2902_, 0, v___x_2901_);
                return v___x_2902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(
    mut v_t_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_2907_, v___y_2908_);
    crate::leanh::lean_dec(v___y_2908_);
    return v_res_2910_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2911_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2912_ = lean_mk_empty_array_with_capacity(v___x_2911_);
    v___x_2913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2913_, 0, v___x_2912_);
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: usize = 0;
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = 5usize;
    v___x_2915_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2916_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2917_ = lean_mk_empty_array_with_capacity(v___x_2916_);
    v___x_2918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once
        ),
        _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0,
    );
    v___x_2919_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2919_, 0, v___x_2918_);
    crate::leanh::lean_ctor_set(v___x_2919_, 1, v___x_2917_);
    crate::leanh::lean_ctor_set(v___x_2919_, 2, v___x_2915_);
    crate::leanh::lean_ctor_set(v___x_2919_, 3, v___x_2915_);
    crate::leanh::lean_ctor_set_usize(v___x_2919_, 4, v___x_2914_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
    mut v_t_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_2928_: u8 = 0;
    v___x_2926_ = lean_st_ref_get(v___y_2924_);
    v_infoState_2927_ = crate::leanh::lean_ctor_get(v___x_2926_, 7);
    crate::leanh::lean_inc_ref(v_infoState_2927_);
    crate::leanh::lean_dec(v___x_2926_);
    v_enabled_2928_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_2927_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_2927_);
    if v_enabled_2928_ == 0 {
        let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_2920_);
        v___x_2929_ = crate::leanh::lean_box(0);
        v___x_2930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2929_);
        return v___x_2930_;
    } else {
        let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2931_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once
            ),
            _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1,
        );
        v___x_2932_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2932_, 0, v_t_2920_);
        crate::leanh::lean_ctor_set(v___x_2932_, 1, v___x_2931_);
        v___x_2933_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_2932_, v___y_2924_);
        return v___x_2933_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(
    mut v_t_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
        v_t_2934_,
        v___y_2935_,
        v___y_2936_,
        v___y_2937_,
        v___y_2938_,
    );
    crate::leanh::lean_dec(v___y_2938_);
    crate::leanh::lean_dec_ref(v___y_2937_);
    crate::leanh::lean_dec(v___y_2936_);
    crate::leanh::lean_dec_ref(v___y_2935_);
    return v_res_2940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(
    mut v___x_2941_: *mut crate::leanh::LeanObject,
    mut v_as_2942_: *mut crate::leanh::LeanObject,
    mut v_sz_2943_: usize,
    mut v_i_2944_: usize,
    mut v_b_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v_array_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v_a_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v_reuseFailAlloc_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_unused_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2951_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
                if v___x_2951_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2941_);
                    v___x_2952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2952_, 0, v_b_2945_);
                    return v___x_2952_;
                } else {
                    v_snd_2953_ = crate::leanh::lean_ctor_get(v_b_2945_, 1);
                    v_fst_2954_ = crate::leanh::lean_ctor_get(v_b_2945_, 0);
                    v_isSharedCheck_3001_ = (!crate::leanh::lean_is_exclusive(v_b_2945_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2956_ = v_b_2945_;
                        v_isShared_2957_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2953_);
                        crate::leanh::lean_inc(v_fst_2954_);
                        crate::leanh::lean_dec(v_b_2945_);
                        v___x_2956_ = crate::leanh::lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_2958_ = crate::leanh::lean_ctor_get(v_snd_2953_, 0);
                v_start_2959_ = crate::leanh::lean_ctor_get(v_snd_2953_, 1);
                v_stop_2960_ = crate::leanh::lean_ctor_get(v_snd_2953_, 2);
                v___x_2961_ = lean_nat_dec_lt(v_start_2959_, v_stop_2960_);
                if v___x_2961_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2941_);
                    if v_isShared_2957_ == 0 {
                        v___x_2963_ = v___x_2956_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_fst_2954_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2953_);
                        v___x_2963_ = v_reuseFailAlloc_2965_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2960_);
                    crate::leanh::lean_inc(v_start_2959_);
                    crate::leanh::lean_inc_ref(v_array_2958_);
                    v_isSharedCheck_2997_ = (!crate::leanh::lean_is_exclusive(v_snd_2953_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v_unused_2998_ = crate::leanh::lean_ctor_get(v_snd_2953_, 2);
                        crate::leanh::lean_dec(v_unused_2998_);
                        v_unused_2999_ = crate::leanh::lean_ctor_get(v_snd_2953_, 1);
                        crate::leanh::lean_dec(v_unused_2999_);
                        v_unused_3000_ = crate::leanh::lean_ctor_get(v_snd_2953_, 0);
                        crate::leanh::lean_dec(v_unused_3000_);
                        v___x_2967_ = v_snd_2953_;
                        v_isShared_2968_ = v_isSharedCheck_2997_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2953_);
                        v___x_2967_ = crate::leanh::lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_2997_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2964_, 0, v___x_2963_);
                return v___x_2964_;
            }
            3 => {
                v_a_2969_ = lean_array_uget_borrowed(v_as_2942_, v_i_2944_);
                v___x_2970_ = lean_array_fget_borrowed(v_array_2958_, v_start_2959_);
                crate::leanh::lean_inc_n(v___x_2970_, 3);
                v___x_2971_ = l_Lean_mkFVar(v___x_2970_);
                crate::leanh::lean_inc_n(v_a_2969_, 2);
                v___x_2972_ = l_Lean_Meta_FVarSubst_insert(v_fst_2954_, v_a_2969_, v___x_2971_);
                crate::leanh::lean_inc_ref(v___x_2941_);
                v___x_2973_ = l_Lean_LocalContext_get_x21(v___x_2941_, v___x_2970_);
                v___x_2974_ = l_Lean_LocalDecl_userName(v___x_2973_);
                crate::leanh::lean_dec_ref(v___x_2973_);
                v___x_2975_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2975_, 0, v___x_2974_);
                crate::leanh::lean_ctor_set(v___x_2975_, 1, v___x_2970_);
                crate::leanh::lean_ctor_set(v___x_2975_, 2, v_a_2969_);
                v___x_2976_ = crate::leanh::lean_alloc_ctor(11, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2976_, 0, v___x_2975_);
                v___x_2977_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
                    v___x_2976_,
                    v___y_2946_,
                    v___y_2947_,
                    v___y_2948_,
                    v___y_2949_,
                );
                if crate::leanh::lean_obj_tag(v___x_2977_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2977_, 1);
                    v___x_2978_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2979_ = lean_nat_add(v_start_2959_, v___x_2978_);
                    crate::leanh::lean_dec(v_start_2959_);
                    if v_isShared_2968_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2967_, 1, v___x_2979_);
                        v___x_2981_ = v___x_2967_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2988_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_array_2958_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_stop_2960_);
                        v___x_2981_ = v_reuseFailAlloc_2988_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2972_);
                    crate::leanh::lean_del_object(v___x_2967_);
                    crate::leanh::lean_dec(v_stop_2960_);
                    crate::leanh::lean_dec(v_start_2959_);
                    crate::leanh::lean_dec_ref(v_array_2958_);
                    crate::leanh::lean_del_object(v___x_2956_);
                    crate::leanh::lean_dec_ref(v___x_2941_);
                    v_a_2989_ = crate::leanh::lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_2996_ = (!crate::leanh::lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v___x_2991_ = v___x_2977_;
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2989_);
                        crate::leanh::lean_dec(v___x_2977_);
                        v___x_2991_ = crate::leanh::lean_box(0);
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2956_, 1, v___x_2981_);
                    crate::leanh::lean_ctor_set(v___x_2956_, 0, v___x_2972_);
                    v___x_2983_ = v___x_2956_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2987_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2984_ = 1usize;
                v___x_2985_ = lean_usize_add(v_i_2944_, v___x_2984_);
                v_i_2944_ = v___x_2985_;
                v_b_2945_ = v___x_2983_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2992_ == 0 {
                    v___x_2994_ = v___x_2991_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
                    v___x_2994_ = v_reuseFailAlloc_2995_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1___boxed(
    mut v___x_3002_: *mut crate::leanh::LeanObject,
    mut v_as_3003_: *mut crate::leanh::LeanObject,
    mut v_sz_3004_: *mut crate::leanh::LeanObject,
    mut v_i_3005_: *mut crate::leanh::LeanObject,
    mut v_b_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3012_: usize = 0;
    let mut v_i_boxed_3013_: usize = 0;
    let mut v_res_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3012_ = crate::leanh::lean_unbox_usize(v_sz_3004_);
    crate::leanh::lean_dec(v_sz_3004_);
    v_i_boxed_3013_ = crate::leanh::lean_unbox_usize(v_i_3005_);
    crate::leanh::lean_dec(v_i_3005_);
    v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_3002_, v_as_3003_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
    crate::leanh::lean_dec(v___y_3010_);
    crate::leanh::lean_dec_ref(v___y_3009_);
    crate::leanh::lean_dec(v___y_3008_);
    crate::leanh::lean_dec_ref(v___y_3007_);
    crate::leanh::lean_dec_ref(v_as_3003_);
    return v_res_3014_;
}
pub unsafe fn l_Lean_MVarId_assertAfter(
    mut v_mvarId_3018_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3019_: *mut crate::leanh::LeanObject,
    mut v_userName_3020_: *mut crate::leanh::LeanObject,
    mut v_type_3021_: *mut crate::leanh::LeanObject,
    mut v_val_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v_fst_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_a_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_reuseFailAlloc_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_a_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_a_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut v_a_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3028_ = l_Lean_MVarId_assertAfter___closed__1;
                crate::leanh::lean_inc(v_mvarId_3018_);
                v___x_3029_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3018_,
                    v___x_3028_,
                    v_a_3023_,
                    v_a_3024_,
                    v_a_3025_,
                    v_a_3026_,
                );
                if crate::leanh::lean_obj_tag(v___x_3029_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3029_, 1);
                    v___x_3030_ = l_Lean_MVarId_revertAfter(
                        v_mvarId_3018_,
                        v_fvarId_3019_,
                        v_a_3023_,
                        v_a_3024_,
                        v_a_3025_,
                        v_a_3026_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3030_) == 0 {
                        v_a_3031_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                        crate::leanh::lean_inc(v_a_3031_);
                        crate::leanh::lean_dec_ref_known(v___x_3030_, 1);
                        v_fst_3032_ = crate::leanh::lean_ctor_get(v_a_3031_, 0);
                        crate::leanh::lean_inc(v_fst_3032_);
                        v_snd_3033_ = crate::leanh::lean_ctor_get(v_a_3031_, 1);
                        crate::leanh::lean_inc(v_snd_3033_);
                        crate::leanh::lean_dec(v_a_3031_);
                        v___x_3034_ = l_Lean_MVarId_assert(
                            v_snd_3033_,
                            v_userName_3020_,
                            v_type_3021_,
                            v_val_3022_,
                            v_a_3023_,
                            v_a_3024_,
                            v_a_3025_,
                            v_a_3026_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3034_) == 0 {
                            v_a_3035_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                            crate::leanh::lean_inc(v_a_3035_);
                            crate::leanh::lean_dec_ref_known(v___x_3034_, 1);
                            v___x_3036_ = 1;
                            v___x_3037_ = l_Lean_Meta_intro1Core(
                                v_a_3035_,
                                v___x_3036_,
                                v_a_3023_,
                                v_a_3024_,
                                v_a_3025_,
                                v_a_3026_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3037_) == 0 {
                                v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                                crate::leanh::lean_inc(v_a_3038_);
                                crate::leanh::lean_dec_ref_known(v___x_3037_, 1);
                                v_fst_3039_ = crate::leanh::lean_ctor_get(v_a_3038_, 0);
                                crate::leanh::lean_inc(v_fst_3039_);
                                v_snd_3040_ = crate::leanh::lean_ctor_get(v_a_3038_, 1);
                                crate::leanh::lean_inc(v_snd_3040_);
                                crate::leanh::lean_dec(v_a_3038_);
                                v___x_3041_ = lean_array_get_size(v_fst_3032_);
                                v___x_3042_ = crate::leanh::lean_box(0);
                                v___x_3043_ = 0;
                                v___x_3044_ = l_Lean_Meta_introNCore(
                                    v_snd_3040_,
                                    v___x_3041_,
                                    v___x_3042_,
                                    v___x_3043_,
                                    v___x_3036_,
                                    v_a_3023_,
                                    v_a_3024_,
                                    v_a_3025_,
                                    v_a_3026_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3044_) == 0 {
                                    v_a_3045_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                                    crate::leanh::lean_inc(v_a_3045_);
                                    crate::leanh::lean_dec_ref_known(v___x_3044_, 1);
                                    v_fst_3046_ = crate::leanh::lean_ctor_get(v_a_3045_, 0);
                                    v_snd_3047_ = crate::leanh::lean_ctor_get(v_a_3045_, 1);
                                    v_isSharedCheck_3090_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_3045_)) as u8;
                                    if v_isSharedCheck_3090_ == 0 {
                                        v___x_3049_ = v_a_3045_;
                                        v_isShared_3050_ = v_isSharedCheck_3090_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_3047_);
                                        crate::leanh::lean_inc(v_fst_3046_);
                                        crate::leanh::lean_dec(v_a_3045_);
                                        v___x_3049_ = crate::leanh::lean_box(0);
                                        v_isShared_3050_ = v_isSharedCheck_3090_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_3039_);
                                    crate::leanh::lean_dec(v_fst_3032_);
                                    v_a_3091_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                                    v_isSharedCheck_3098_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3044_)) as u8;
                                    if v_isSharedCheck_3098_ == 0 {
                                        v___x_3093_ = v___x_3044_;
                                        v_isShared_3094_ = v_isSharedCheck_3098_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3091_);
                                        crate::leanh::lean_dec(v___x_3044_);
                                        v___x_3093_ = crate::leanh::lean_box(0);
                                        v_isShared_3094_ = v_isSharedCheck_3098_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3032_);
                                v_a_3099_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                                v_isSharedCheck_3106_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3037_)) as u8;
                                if v_isSharedCheck_3106_ == 0 {
                                    v___x_3101_ = v___x_3037_;
                                    v_isShared_3102_ = v_isSharedCheck_3106_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3099_);
                                    crate::leanh::lean_dec(v___x_3037_);
                                    v___x_3101_ = crate::leanh::lean_box(0);
                                    v_isShared_3102_ = v_isSharedCheck_3106_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_3032_);
                            v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                            v_isSharedCheck_3114_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3034_)) as u8;
                            if v_isSharedCheck_3114_ == 0 {
                                v___x_3109_ = v___x_3034_;
                                v_isShared_3110_ = v_isSharedCheck_3114_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3107_);
                                crate::leanh::lean_dec(v___x_3034_);
                                v___x_3109_ = crate::leanh::lean_box(0);
                                v_isShared_3110_ = v_isSharedCheck_3114_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_val_3022_);
                        crate::leanh::lean_dec_ref(v_type_3021_);
                        crate::leanh::lean_dec(v_userName_3020_);
                        v_a_3115_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                        v_isSharedCheck_3122_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                        if v_isSharedCheck_3122_ == 0 {
                            v___x_3117_ = v___x_3030_;
                            v_isShared_3118_ = v_isSharedCheck_3122_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3115_);
                            crate::leanh::lean_dec(v___x_3030_);
                            v___x_3117_ = crate::leanh::lean_box(0);
                            v_isShared_3118_ = v_isSharedCheck_3122_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_val_3022_);
                    crate::leanh::lean_dec_ref(v_type_3021_);
                    crate::leanh::lean_dec(v_userName_3020_);
                    crate::leanh::lean_dec(v_fvarId_3019_);
                    crate::leanh::lean_dec(v_mvarId_3018_);
                    v_a_3123_ = crate::leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3130_ = (!crate::leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3130_ == 0 {
                        v___x_3125_ = v___x_3029_;
                        v_isShared_3126_ = v_isSharedCheck_3130_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3123_);
                        crate::leanh::lean_dec(v___x_3029_);
                        v___x_3125_ = crate::leanh::lean_box(0);
                        v_isShared_3126_ = v_isSharedCheck_3130_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_snd_3047_);
                v___x_3051_ =
                    l_Lean_MVarId_getDecl(v_snd_3047_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
                if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                    v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                    crate::leanh::lean_inc(v_a_3052_);
                    crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                    v_lctx_3053_ = crate::leanh::lean_ctor_get(v_a_3052_, 1);
                    crate::leanh::lean_inc_ref(v_lctx_3053_);
                    crate::leanh::lean_dec(v_a_3052_);
                    v___x_3054_ = crate::leanh::lean_box(0);
                    v___x_3055_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3056_ = lean_array_get_size(v_fst_3046_);
                    v___x_3057_ =
                        l_Array_toSubarray___redArg(v_fst_3046_, v___x_3055_, v___x_3056_);
                    if v_isShared_3050_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3049_, 1, v___x_3057_);
                        crate::leanh::lean_ctor_set(v___x_3049_, 0, v___x_3054_);
                        v___x_3059_ = v___x_3049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3054_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3057_);
                        v___x_3059_ = v_reuseFailAlloc_3081_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3049_);
                    crate::leanh::lean_dec(v_snd_3047_);
                    crate::leanh::lean_dec(v_fst_3046_);
                    crate::leanh::lean_dec(v_fst_3039_);
                    crate::leanh::lean_dec(v_fst_3032_);
                    v_a_3082_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                    v_isSharedCheck_3089_ = (!crate::leanh::lean_is_exclusive(v___x_3051_)) as u8;
                    if v_isSharedCheck_3089_ == 0 {
                        v___x_3084_ = v___x_3051_;
                        v_isShared_3085_ = v_isSharedCheck_3089_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3082_);
                        crate::leanh::lean_dec(v___x_3051_);
                        v___x_3084_ = crate::leanh::lean_box(0);
                        v_isShared_3085_ = v_isSharedCheck_3089_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_sz_3060_ = lean_array_size(v_fst_3032_);
                v___x_3061_ = 0usize;
                v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v_lctx_3053_, v_fst_3032_, v_sz_3060_, v___x_3061_, v___x_3059_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
                crate::leanh::lean_dec(v_fst_3032_);
                if crate::leanh::lean_obj_tag(v___x_3062_) == 0 {
                    v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3072_ = (!crate::leanh::lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3072_ == 0 {
                        v___x_3065_ = v___x_3062_;
                        v_isShared_3066_ = v_isSharedCheck_3072_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3063_);
                        crate::leanh::lean_dec(v___x_3062_);
                        v___x_3065_ = crate::leanh::lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3072_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3047_);
                    crate::leanh::lean_dec(v_fst_3039_);
                    v_a_3073_ = crate::leanh::lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3080_ = (!crate::leanh::lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3075_ = v___x_3062_;
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3073_);
                        crate::leanh::lean_dec(v___x_3062_);
                        v___x_3075_ = crate::leanh::lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3067_ = crate::leanh::lean_ctor_get(v_a_3063_, 0);
                crate::leanh::lean_inc(v_fst_3067_);
                crate::leanh::lean_dec(v_a_3063_);
                v___x_3068_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3068_, 0, v_fst_3039_);
                crate::leanh::lean_ctor_set(v___x_3068_, 1, v_snd_3047_);
                crate::leanh::lean_ctor_set(v___x_3068_, 2, v_fst_3067_);
                if v_isShared_3066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3068_);
                    v___x_3070_ = v___x_3065_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
                    v___x_3070_ = v_reuseFailAlloc_3071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3070_;
            }
            5 => {
                if v_isShared_3076_ == 0 {
                    v___x_3078_ = v___x_3075_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
                    v___x_3078_ = v_reuseFailAlloc_3079_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3078_;
            }
            7 => {
                if v_isShared_3085_ == 0 {
                    v___x_3087_ = v___x_3084_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3087_;
            }
            9 => {
                if v_isShared_3094_ == 0 {
                    v___x_3096_ = v___x_3093_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
                    v___x_3096_ = v_reuseFailAlloc_3097_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3096_;
            }
            11 => {
                if v_isShared_3102_ == 0 {
                    v___x_3104_ = v___x_3101_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
                    v___x_3104_ = v_reuseFailAlloc_3105_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3104_;
            }
            13 => {
                if v_isShared_3110_ == 0 {
                    v___x_3112_ = v___x_3109_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
                    v___x_3112_ = v_reuseFailAlloc_3113_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3112_;
            }
            15 => {
                if v_isShared_3118_ == 0 {
                    v___x_3120_ = v___x_3117_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
                    v___x_3120_ = v_reuseFailAlloc_3121_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3120_;
            }
            17 => {
                if v_isShared_3126_ == 0 {
                    v___x_3128_ = v___x_3125_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
                    v___x_3128_ = v_reuseFailAlloc_3129_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assertAfter___boxed(
    mut v_mvarId_3131_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3132_: *mut crate::leanh::LeanObject,
    mut v_userName_3133_: *mut crate::leanh::LeanObject,
    mut v_type_3134_: *mut crate::leanh::LeanObject,
    mut v_val_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lean_MVarId_assertAfter(
        v_mvarId_3131_,
        v_fvarId_3132_,
        v_userName_3133_,
        v_type_3134_,
        v_val_3135_,
        v_a_3136_,
        v_a_3137_,
        v_a_3138_,
        v_a_3139_,
    );
    crate::leanh::lean_dec(v_a_3139_);
    crate::leanh::lean_dec_ref(v_a_3138_);
    crate::leanh::lean_dec(v_a_3137_);
    crate::leanh::lean_dec_ref(v_a_3136_);
    return v_res_3141_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(
    mut v_t_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_3142_, v___y_3146_);
    return v___x_3148_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(
    mut v_t_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    crate::leanh::lean_dec(v___y_3153_);
    crate::leanh::lean_dec_ref(v___y_3152_);
    crate::leanh::lean_dec(v___y_3151_);
    crate::leanh::lean_dec_ref(v___y_3150_);
    return v_res_3155_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
    mut v_ldecl_x27_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3159_ = lean_st_ref_take(v_a_3157_);
                v___x_3165_ = crate::leanh::lean_box(0);
                v___x_3166_ = l_Lean_LocalDecl_index(v___x_3159_);
                v___x_3167_ = l_Lean_LocalDecl_index(v_ldecl_x27_3156_);
                v___x_3168_ = lean_nat_dec_lt(v___x_3166_, v___x_3167_);
                crate::leanh::lean_dec(v___x_3167_);
                crate::leanh::lean_dec(v___x_3166_);
                if v___x_3168_ == 0 {
                    crate::leanh::lean_dec_ref(v_ldecl_x27_3156_);
                    v_fst_3161_ = v___x_3165_;
                    v_snd_3162_ = v___x_3159_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3159_);
                    v_fst_3161_ = v___x_3165_;
                    v_snd_3162_ = v_ldecl_x27_3156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3163_ = lean_st_ref_set(v_a_3157_, v_snd_3162_);
                v___x_3164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3164_, 0, v_fst_3161_);
                return v___x_3164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(
    mut v_ldecl_x27_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3172_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
            v_ldecl_x27_3169_,
            v_a_3170_,
        );
    crate::leanh::lean_dec(v_a_3170_);
    return v_res_3172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(
    mut v_ldecl_x27_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3180_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
            v_ldecl_x27_3173_,
            v_a_3174_,
        );
    return v___x_3180_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(
    mut v_ldecl_x27_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
    mut v_a_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3188_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(
        v_ldecl_x27_3181_,
        v_a_3182_,
        v_a_3183_,
        v_a_3184_,
        v_a_3185_,
        v_a_3186_,
    );
    crate::leanh::lean_dec(v_a_3186_);
    crate::leanh::lean_dec_ref(v_a_3185_);
    crate::leanh::lean_dec(v_a_3184_);
    crate::leanh::lean_dec_ref(v_a_3183_);
    crate::leanh::lean_dec(v_a_3182_);
    return v_res_3188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_as_3189_: *mut crate::leanh::LeanObject,
    mut v_i_3190_: usize,
    mut v_stop_3191_: usize,
    mut v_b_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: usize = 0;
    let mut v___x_3201_: usize = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3203_ = lean_usize_dec_eq(v_i_3190_, v_stop_3191_);
                if v___x_3203_ == 0 {
                    v___x_3204_ = lean_array_uget_borrowed(v_as_3189_, v_i_3190_);
                    if crate::leanh::lean_obj_tag(v___x_3204_) == 0 {
                        v___x_3205_ = crate::leanh::lean_box(0);
                        v_a_3199_ = v___x_3205_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3206_ = crate::leanh::lean_ctor_get(v___x_3204_, 0);
                        v___x_3207_ = l_Lean_LocalDecl_fvarId(v_val_3206_);
                        v___x_3208_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_3207_,
                            v___y_3194_,
                            v___y_3195_,
                            v___y_3196_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3208_) == 0 {
                            v_a_3209_ = crate::leanh::lean_ctor_get(v___x_3208_, 0);
                            crate::leanh::lean_inc(v_a_3209_);
                            crate::leanh::lean_dec_ref_known(v___x_3208_, 1);
                            v___x_3210_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3209_, v___y_3193_);
                            if crate::leanh::lean_obj_tag(v___x_3210_) == 0 {
                                v_a_3211_ = crate::leanh::lean_ctor_get(v___x_3210_, 0);
                                crate::leanh::lean_inc(v_a_3211_);
                                crate::leanh::lean_dec_ref_known(v___x_3210_, 1);
                                v_a_3199_ = v_a_3211_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3210_;
                            }
                        } else {
                            v_a_3212_ = crate::leanh::lean_ctor_get(v___x_3208_, 0);
                            v_isSharedCheck_3219_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3208_)) as u8;
                            if v_isSharedCheck_3219_ == 0 {
                                v___x_3214_ = v___x_3208_;
                                v_isShared_3215_ = v_isSharedCheck_3219_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3212_);
                                crate::leanh::lean_dec(v___x_3208_);
                                v___x_3214_ = crate::leanh::lean_box(0);
                                v_isShared_3215_ = v_isSharedCheck_3219_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3220_, 0, v_b_3192_);
                    return v___x_3220_;
                }
            }
            1 => {
                v___x_3200_ = 1usize;
                v___x_3201_ = lean_usize_add(v_i_3190_, v___x_3200_);
                v_i_3190_ = v___x_3201_;
                v_b_3192_ = v_a_3199_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3215_ == 0 {
                    v___x_3217_ = v___x_3214_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
                    v___x_3217_ = v_reuseFailAlloc_3218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_as_3221_: *mut crate::leanh::LeanObject,
    mut v_i_3222_: *mut crate::leanh::LeanObject,
    mut v_stop_3223_: *mut crate::leanh::LeanObject,
    mut v_b_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3230_: usize = 0;
    let mut v_stop_boxed_3231_: usize = 0;
    let mut v_res_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3230_ = crate::leanh::lean_unbox_usize(v_i_3222_);
    crate::leanh::lean_dec(v_i_3222_);
    v_stop_boxed_3231_ = crate::leanh::lean_unbox_usize(v_stop_3223_);
    crate::leanh::lean_dec(v_stop_3223_);
    v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_3221_, v_i_boxed_3230_, v_stop_boxed_3231_, v_b_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
    crate::leanh::lean_dec(v___y_3228_);
    crate::leanh::lean_dec_ref(v___y_3227_);
    crate::leanh::lean_dec_ref(v___y_3226_);
    crate::leanh::lean_dec(v___y_3225_);
    crate::leanh::lean_dec_ref(v_as_3221_);
    return v_res_3232_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(
    mut v_as_3233_: *mut crate::leanh::LeanObject,
    mut v_i_3234_: usize,
    mut v_stop_3235_: usize,
    mut v_b_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: usize = 0;
    let mut v___x_3246_: usize = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3248_ = lean_usize_dec_eq(v_i_3234_, v_stop_3235_);
                if v___x_3248_ == 0 {
                    v___x_3249_ = lean_array_uget_borrowed(v_as_3233_, v_i_3234_);
                    if crate::leanh::lean_obj_tag(v___x_3249_) == 0 {
                        v___x_3250_ = crate::leanh::lean_box(0);
                        v_a_3244_ = v___x_3250_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3251_ = crate::leanh::lean_ctor_get(v___x_3249_, 0);
                        v___x_3252_ = l_Lean_LocalDecl_fvarId(v_val_3251_);
                        v___x_3253_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_3252_,
                            v___y_3238_,
                            v___y_3240_,
                            v___y_3241_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3253_) == 0 {
                            v_a_3254_ = crate::leanh::lean_ctor_get(v___x_3253_, 0);
                            crate::leanh::lean_inc(v_a_3254_);
                            crate::leanh::lean_dec_ref_known(v___x_3253_, 1);
                            v___x_3255_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3254_, v___y_3237_);
                            if crate::leanh::lean_obj_tag(v___x_3255_) == 0 {
                                v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3255_, 0);
                                crate::leanh::lean_inc(v_a_3256_);
                                crate::leanh::lean_dec_ref_known(v___x_3255_, 1);
                                v_a_3244_ = v_a_3256_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3255_;
                            }
                        } else {
                            v_a_3257_ = crate::leanh::lean_ctor_get(v___x_3253_, 0);
                            v_isSharedCheck_3264_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3253_)) as u8;
                            if v_isSharedCheck_3264_ == 0 {
                                v___x_3259_ = v___x_3253_;
                                v_isShared_3260_ = v_isSharedCheck_3264_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3257_);
                                crate::leanh::lean_dec(v___x_3253_);
                                v___x_3259_ = crate::leanh::lean_box(0);
                                v_isShared_3260_ = v_isSharedCheck_3264_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3265_, 0, v_b_3236_);
                    return v___x_3265_;
                }
            }
            1 => {
                v___x_3245_ = 1usize;
                v___x_3246_ = lean_usize_add(v_i_3234_, v___x_3245_);
                v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_3233_, v___x_3246_, v_stop_3235_, v_a_3244_, v___y_3237_, v___y_3238_, v___y_3240_, v___y_3241_);
                return v___x_3247_;
            }
            2 => {
                if v_isShared_3260_ == 0 {
                    v___x_3262_ = v___x_3259_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
                    v___x_3262_ = v_reuseFailAlloc_3263_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2___boxed(
    mut v_as_3266_: *mut crate::leanh::LeanObject,
    mut v_i_3267_: *mut crate::leanh::LeanObject,
    mut v_stop_3268_: *mut crate::leanh::LeanObject,
    mut v_b_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3276_: usize = 0;
    let mut v_stop_boxed_3277_: usize = 0;
    let mut v_res_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3276_ = crate::leanh::lean_unbox_usize(v_i_3267_);
    crate::leanh::lean_dec(v_i_3267_);
    v_stop_boxed_3277_ = crate::leanh::lean_unbox_usize(v_stop_3268_);
    crate::leanh::lean_dec(v_stop_3268_);
    v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_3266_, v_i_boxed_3276_, v_stop_boxed_3277_, v_b_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
    crate::leanh::lean_dec(v___y_3274_);
    crate::leanh::lean_dec_ref(v___y_3273_);
    crate::leanh::lean_dec(v___y_3272_);
    crate::leanh::lean_dec_ref(v___y_3271_);
    crate::leanh::lean_dec(v___y_3270_);
    crate::leanh::lean_dec_ref(v_as_3266_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(
    mut v_x_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: usize = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: usize = 0;
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v_vs_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: usize = 0;
    let mut v___x_3324_: usize = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3279_) == 0 {
                    v_cs_3286_ = crate::leanh::lean_ctor_get(v_x_3279_, 0);
                    v_isSharedCheck_3307_ = (!crate::leanh::lean_is_exclusive(v_x_3279_)) as u8;
                    if v_isSharedCheck_3307_ == 0 {
                        v___x_3288_ = v_x_3279_;
                        v_isShared_3289_ = v_isSharedCheck_3307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_3286_);
                        crate::leanh::lean_dec(v_x_3279_);
                        v___x_3288_ = crate::leanh::lean_box(0);
                        v_isShared_3289_ = v_isSharedCheck_3307_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3308_ = crate::leanh::lean_ctor_get(v_x_3279_, 0);
                    v_isSharedCheck_3329_ = (!crate::leanh::lean_is_exclusive(v_x_3279_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3310_ = v_x_3279_;
                        v_isShared_3311_ = v_isSharedCheck_3329_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3308_);
                        crate::leanh::lean_dec(v_x_3279_);
                        v___x_3310_ = crate::leanh::lean_box(0);
                        v_isShared_3311_ = v_isSharedCheck_3329_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3290_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3291_ = lean_array_get_size(v_cs_3286_);
                v___x_3292_ = crate::leanh::lean_box(0);
                v___x_3293_ = lean_nat_dec_lt(v___x_3290_, v___x_3291_);
                if v___x_3293_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_3286_);
                    if v_isShared_3289_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3288_, 0, v___x_3292_);
                        v___x_3295_ = v___x_3288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3292_);
                        v___x_3295_ = v_reuseFailAlloc_3296_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3297_ = lean_nat_dec_le(v___x_3291_, v___x_3291_);
                    if v___x_3297_ == 0 {
                        if v___x_3293_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_3286_);
                            if v_isShared_3289_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3288_, 0, v___x_3292_);
                                v___x_3299_ = v___x_3288_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3300_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3292_);
                                v___x_3299_ = v_reuseFailAlloc_3300_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3288_);
                            v___x_3301_ = 0usize;
                            v___x_3302_ = lean_usize_of_nat(v___x_3291_);
                            v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3286_, v___x_3301_, v___x_3302_, v___x_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                            crate::leanh::lean_dec_ref(v_cs_3286_);
                            return v___x_3303_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3288_);
                        v___x_3304_ = 0usize;
                        v___x_3305_ = lean_usize_of_nat(v___x_3291_);
                        v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3286_, v___x_3304_, v___x_3305_, v___x_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                        crate::leanh::lean_dec_ref(v_cs_3286_);
                        return v___x_3306_;
                    }
                }
            }
            2 => {
                return v___x_3295_;
            }
            3 => {
                return v___x_3299_;
            }
            4 => {
                v___x_3312_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3313_ = lean_array_get_size(v_vs_3308_);
                v___x_3314_ = crate::leanh::lean_box(0);
                v___x_3315_ = lean_nat_dec_lt(v___x_3312_, v___x_3313_);
                if v___x_3315_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_3308_);
                    if v_isShared_3311_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3310_, 0);
                        crate::leanh::lean_ctor_set(v___x_3310_, 0, v___x_3314_);
                        v___x_3317_ = v___x_3310_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3314_);
                        v___x_3317_ = v_reuseFailAlloc_3318_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3319_ = lean_nat_dec_le(v___x_3313_, v___x_3313_);
                    if v___x_3319_ == 0 {
                        if v___x_3315_ == 0 {
                            crate::leanh::lean_dec_ref(v_vs_3308_);
                            if v_isShared_3311_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3310_, 0);
                                crate::leanh::lean_ctor_set(v___x_3310_, 0, v___x_3314_);
                                v___x_3321_ = v___x_3310_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3322_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3314_);
                                v___x_3321_ = v_reuseFailAlloc_3322_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3310_);
                            v___x_3323_ = 0usize;
                            v___x_3324_ = lean_usize_of_nat(v___x_3313_);
                            v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3308_, v___x_3323_, v___x_3324_, v___x_3314_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                            crate::leanh::lean_dec_ref(v_vs_3308_);
                            return v___x_3325_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3310_);
                        v___x_3326_ = 0usize;
                        v___x_3327_ = lean_usize_of_nat(v___x_3313_);
                        v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3308_, v___x_3326_, v___x_3327_, v___x_3314_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                        crate::leanh::lean_dec_ref(v_vs_3308_);
                        return v___x_3328_;
                    }
                }
            }
            5 => {
                return v___x_3317_;
            }
            6 => {
                return v___x_3321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(
    mut v_as_3330_: *mut crate::leanh::LeanObject,
    mut v_i_3331_: usize,
    mut v_stop_3332_: usize,
    mut v_b_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3340_ = lean_usize_dec_eq(v_i_3331_, v_stop_3332_);
                if v___x_3340_ == 0 {
                    v___x_3341_ = lean_array_uget_borrowed(v_as_3330_, v_i_3331_);
                    crate::leanh::lean_inc(v___x_3341_);
                    v___x_3342_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_3341_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
                    if crate::leanh::lean_obj_tag(v___x_3342_) == 0 {
                        v_a_3343_ = crate::leanh::lean_ctor_get(v___x_3342_, 0);
                        crate::leanh::lean_inc(v_a_3343_);
                        crate::leanh::lean_dec_ref_known(v___x_3342_, 1);
                        v___x_3344_ = 1usize;
                        v___x_3345_ = lean_usize_add(v_i_3331_, v___x_3344_);
                        v_i_3331_ = v___x_3345_;
                        v_b_3333_ = v_a_3343_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3342_;
                    }
                } else {
                    v___x_3347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3347_, 0, v_b_3333_);
                    return v___x_3347_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_as_3348_: *mut crate::leanh::LeanObject,
    mut v_i_3349_: *mut crate::leanh::LeanObject,
    mut v_stop_3350_: *mut crate::leanh::LeanObject,
    mut v_b_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3358_: usize = 0;
    let mut v_stop_boxed_3359_: usize = 0;
    let mut v_res_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3358_ = crate::leanh::lean_unbox_usize(v_i_3349_);
    crate::leanh::lean_dec(v_i_3349_);
    v_stop_boxed_3359_ = crate::leanh::lean_unbox_usize(v_stop_3350_);
    crate::leanh::lean_dec(v_stop_3350_);
    v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_3348_, v_i_boxed_3358_, v_stop_boxed_3359_, v_b_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
    crate::leanh::lean_dec(v___y_3356_);
    crate::leanh::lean_dec_ref(v___y_3355_);
    crate::leanh::lean_dec(v___y_3354_);
    crate::leanh::lean_dec_ref(v___y_3353_);
    crate::leanh::lean_dec(v___y_3352_);
    crate::leanh::lean_dec_ref(v_as_3348_);
    return v_res_3360_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_x_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    crate::leanh::lean_dec(v___y_3366_);
    crate::leanh::lean_dec_ref(v___y_3365_);
    crate::leanh::lean_dec(v___y_3364_);
    crate::leanh::lean_dec_ref(v___y_3363_);
    crate::leanh::lean_dec(v___y_3362_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(
    mut v_t_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: usize = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: usize = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_unused_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3376_ = crate::leanh::lean_ctor_get(v_t_3369_, 0);
                crate::leanh::lean_inc_ref(v_root_3376_);
                v_tail_3377_ = crate::leanh::lean_ctor_get(v_t_3369_, 1);
                crate::leanh::lean_inc_ref(v_tail_3377_);
                crate::leanh::lean_dec_ref(v_t_3369_);
                v___x_3378_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_3376_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                if crate::leanh::lean_obj_tag(v___x_3378_) == 0 {
                    v_isSharedCheck_3399_ = (!crate::leanh::lean_is_exclusive(v___x_3378_)) as u8;
                    if v_isSharedCheck_3399_ == 0 {
                        v_unused_3400_ = crate::leanh::lean_ctor_get(v___x_3378_, 0);
                        crate::leanh::lean_dec(v_unused_3400_);
                        v___x_3380_ = v___x_3378_;
                        v_isShared_3381_ = v_isSharedCheck_3399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3378_);
                        v___x_3380_ = crate::leanh::lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3399_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tail_3377_);
                    return v___x_3378_;
                }
            }
            1 => {
                v___x_3382_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3383_ = lean_array_get_size(v_tail_3377_);
                v___x_3384_ = crate::leanh::lean_box(0);
                v___x_3385_ = lean_nat_dec_lt(v___x_3382_, v___x_3383_);
                if v___x_3385_ == 0 {
                    crate::leanh::lean_dec_ref(v_tail_3377_);
                    if v_isShared_3381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3387_ = v___x_3380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3384_);
                        v___x_3387_ = v_reuseFailAlloc_3388_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3389_ = lean_nat_dec_le(v___x_3383_, v___x_3383_);
                    if v___x_3389_ == 0 {
                        if v___x_3385_ == 0 {
                            crate::leanh::lean_dec_ref(v_tail_3377_);
                            if v_isShared_3381_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                                v___x_3391_ = v___x_3380_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3392_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3384_);
                                v___x_3391_ = v_reuseFailAlloc_3392_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3380_);
                            v___x_3393_ = 0usize;
                            v___x_3394_ = lean_usize_of_nat(v___x_3383_);
                            v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3377_, v___x_3393_, v___x_3394_, v___x_3384_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                            crate::leanh::lean_dec_ref(v_tail_3377_);
                            return v___x_3395_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3380_);
                        v___x_3396_ = 0usize;
                        v___x_3397_ = lean_usize_of_nat(v___x_3383_);
                        v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3377_, v___x_3396_, v___x_3397_, v___x_3384_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                        crate::leanh::lean_dec_ref(v_tail_3377_);
                        return v___x_3398_;
                    }
                }
            }
            2 => {
                return v___x_3387_;
            }
            3 => {
                return v___x_3391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3___boxed(
    mut v_t_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
    crate::leanh::lean_dec(v___y_3406_);
    crate::leanh::lean_dec_ref(v___y_3405_);
    crate::leanh::lean_dec(v___y_3404_);
    crate::leanh::lean_dec_ref(v___y_3403_);
    crate::leanh::lean_dec(v___y_3402_);
    return v_res_3408_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_3409_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(
    mut v_x_3410_: *mut crate::leanh::LeanObject,
    mut v_x_3411_: usize,
    mut v_x_3412_: usize,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: usize = 0;
    let mut v_j_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: usize = 0;
    let mut v___x_3425_: usize = 0;
    let mut v___x_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: usize = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_unused_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: usize = 0;
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3410_) == 0 {
                    v_cs_3419_ = crate::leanh::lean_ctor_get(v_x_3410_, 0);
                    crate::leanh::lean_inc_ref(v_cs_3419_);
                    crate::leanh::lean_dec_ref_known(v_x_3410_, 1);
                    v___x_3420_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
                    v___x_3421_ = lean_usize_shift_right(v_x_3411_, v_x_3412_);
                    v_j_3422_ = lean_usize_to_nat(v___x_3421_);
                    v___x_3423_ = lean_array_get_borrowed(v___x_3420_, v_cs_3419_, v_j_3422_);
                    v___x_3424_ = 1usize;
                    v___x_3425_ = lean_usize_shift_left(v___x_3424_, v_x_3412_);
                    v___x_3426_ = lean_usize_sub(v___x_3425_, v___x_3424_);
                    v___x_3427_ = lean_usize_land(v_x_3411_, v___x_3426_);
                    v___x_3428_ = 5usize;
                    v___x_3429_ = lean_usize_sub(v_x_3412_, v___x_3428_);
                    crate::leanh::lean_inc(v___x_3423_);
                    v___x_3430_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_3423_, v___x_3427_, v___x_3429_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                    if crate::leanh::lean_obj_tag(v___x_3430_) == 0 {
                        v_isSharedCheck_3452_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3430_)) as u8;
                        if v_isSharedCheck_3452_ == 0 {
                            v_unused_3453_ = crate::leanh::lean_ctor_get(v___x_3430_, 0);
                            crate::leanh::lean_dec(v_unused_3453_);
                            v___x_3432_ = v___x_3430_;
                            v_isShared_3433_ = v_isSharedCheck_3452_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3430_);
                            v___x_3432_ = crate::leanh::lean_box(0);
                            v_isShared_3433_ = v_isSharedCheck_3452_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_3422_);
                        crate::leanh::lean_dec_ref(v_cs_3419_);
                        return v___x_3430_;
                    }
                } else {
                    v_vs_3454_ = crate::leanh::lean_ctor_get(v_x_3410_, 0);
                    v_isSharedCheck_3475_ = (!crate::leanh::lean_is_exclusive(v_x_3410_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3456_ = v_x_3410_;
                        v_isShared_3457_ = v_isSharedCheck_3475_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3454_);
                        crate::leanh::lean_dec(v_x_3410_);
                        v___x_3456_ = crate::leanh::lean_box(0);
                        v_isShared_3457_ = v_isSharedCheck_3475_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3434_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3435_ = lean_nat_add(v_j_3422_, v___x_3434_);
                crate::leanh::lean_dec(v_j_3422_);
                v___x_3436_ = lean_array_get_size(v_cs_3419_);
                v___x_3437_ = crate::leanh::lean_box(0);
                v___x_3438_ = lean_nat_dec_lt(v___x_3435_, v___x_3436_);
                if v___x_3438_ == 0 {
                    crate::leanh::lean_dec(v___x_3435_);
                    crate::leanh::lean_dec_ref(v_cs_3419_);
                    if v_isShared_3433_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3432_, 0, v___x_3437_);
                        v___x_3440_ = v___x_3432_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3437_);
                        v___x_3440_ = v_reuseFailAlloc_3441_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3442_ = lean_nat_dec_le(v___x_3436_, v___x_3436_);
                    if v___x_3442_ == 0 {
                        if v___x_3438_ == 0 {
                            crate::leanh::lean_dec(v___x_3435_);
                            crate::leanh::lean_dec_ref(v_cs_3419_);
                            if v_isShared_3433_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3432_, 0, v___x_3437_);
                                v___x_3444_ = v___x_3432_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3445_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3437_);
                                v___x_3444_ = v_reuseFailAlloc_3445_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3432_);
                            v___x_3446_ = lean_usize_of_nat(v___x_3435_);
                            crate::leanh::lean_dec(v___x_3435_);
                            v___x_3447_ = lean_usize_of_nat(v___x_3436_);
                            v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3419_, v___x_3446_, v___x_3447_, v___x_3437_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                            crate::leanh::lean_dec_ref(v_cs_3419_);
                            return v___x_3448_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3432_);
                        v___x_3449_ = lean_usize_of_nat(v___x_3435_);
                        crate::leanh::lean_dec(v___x_3435_);
                        v___x_3450_ = lean_usize_of_nat(v___x_3436_);
                        v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3419_, v___x_3449_, v___x_3450_, v___x_3437_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                        crate::leanh::lean_dec_ref(v_cs_3419_);
                        return v___x_3451_;
                    }
                }
            }
            2 => {
                return v___x_3440_;
            }
            3 => {
                return v___x_3444_;
            }
            4 => {
                v___x_3458_ = lean_usize_to_nat(v_x_3411_);
                v___x_3459_ = lean_array_get_size(v_vs_3454_);
                v___x_3460_ = crate::leanh::lean_box(0);
                v___x_3461_ = lean_nat_dec_lt(v___x_3458_, v___x_3459_);
                if v___x_3461_ == 0 {
                    crate::leanh::lean_dec(v___x_3458_);
                    crate::leanh::lean_dec_ref(v_vs_3454_);
                    if v_isShared_3457_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3456_, 0);
                        crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                        v___x_3463_ = v___x_3456_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3465_ = lean_nat_dec_le(v___x_3459_, v___x_3459_);
                    if v___x_3465_ == 0 {
                        if v___x_3461_ == 0 {
                            crate::leanh::lean_dec(v___x_3458_);
                            crate::leanh::lean_dec_ref(v_vs_3454_);
                            if v_isShared_3457_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3456_, 0);
                                crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                                v___x_3467_ = v___x_3456_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3468_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
                                v___x_3467_ = v_reuseFailAlloc_3468_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3456_);
                            v___x_3469_ = lean_usize_of_nat(v___x_3458_);
                            crate::leanh::lean_dec(v___x_3458_);
                            v___x_3470_ = lean_usize_of_nat(v___x_3459_);
                            v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3454_, v___x_3469_, v___x_3470_, v___x_3460_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                            crate::leanh::lean_dec_ref(v_vs_3454_);
                            return v___x_3471_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3456_);
                        v___x_3472_ = lean_usize_of_nat(v___x_3458_);
                        crate::leanh::lean_dec(v___x_3458_);
                        v___x_3473_ = lean_usize_of_nat(v___x_3459_);
                        v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3454_, v___x_3472_, v___x_3473_, v___x_3460_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                        crate::leanh::lean_dec_ref(v_vs_3454_);
                        return v___x_3474_;
                    }
                }
            }
            5 => {
                return v___x_3463_;
            }
            6 => {
                return v___x_3467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___boxed(
    mut v_x_3476_: *mut crate::leanh::LeanObject,
    mut v_x_3477_: *mut crate::leanh::LeanObject,
    mut v_x_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9426__boxed_3485_: usize = 0;
    let mut v_x_9427__boxed_3486_: usize = 0;
    let mut v_res_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9426__boxed_3485_ = crate::leanh::lean_unbox_usize(v_x_3477_);
    crate::leanh::lean_dec(v_x_3477_);
    v_x_9427__boxed_3486_ = crate::leanh::lean_unbox_usize(v_x_3478_);
    crate::leanh::lean_dec(v_x_3478_);
    v_res_3487_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_3476_, v_x_9426__boxed_3485_, v_x_9427__boxed_3486_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
    crate::leanh::lean_dec(v___y_3483_);
    crate::leanh::lean_dec_ref(v___y_3482_);
    crate::leanh::lean_dec(v___y_3481_);
    crate::leanh::lean_dec_ref(v___y_3480_);
    crate::leanh::lean_dec(v___y_3479_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(
    mut v_t_3488_: *mut crate::leanh::LeanObject,
    mut v_start_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v_root_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3500_: usize = 0;
    let mut v_tailOff_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: usize = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: usize = 0;
    let mut v___x_3534_: usize = 0;
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3497_ = lean_nat_dec_eq(v_start_3489_, v___x_3496_);
                if v___x_3497_ == 0 {
                    v_root_3498_ = crate::leanh::lean_ctor_get(v_t_3488_, 0);
                    crate::leanh::lean_inc_ref(v_root_3498_);
                    v_tail_3499_ = crate::leanh::lean_ctor_get(v_t_3488_, 1);
                    crate::leanh::lean_inc_ref(v_tail_3499_);
                    v_shift_3500_ = crate::leanh::lean_ctor_get_usize(v_t_3488_, 4);
                    v_tailOff_3501_ = crate::leanh::lean_ctor_get(v_t_3488_, 3);
                    crate::leanh::lean_inc(v_tailOff_3501_);
                    crate::leanh::lean_dec_ref(v_t_3488_);
                    v___x_3502_ = lean_nat_dec_le(v_tailOff_3501_, v_start_3489_);
                    if v___x_3502_ == 0 {
                        crate::leanh::lean_dec(v_tailOff_3501_);
                        v___x_3503_ = lean_usize_of_nat(v_start_3489_);
                        v___x_3504_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_3498_, v___x_3503_, v_shift_3500_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                        if crate::leanh::lean_obj_tag(v___x_3504_) == 0 {
                            v_isSharedCheck_3524_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3504_)) as u8;
                            if v_isSharedCheck_3524_ == 0 {
                                v_unused_3525_ = crate::leanh::lean_ctor_get(v___x_3504_, 0);
                                crate::leanh::lean_dec(v_unused_3525_);
                                v___x_3506_ = v___x_3504_;
                                v_isShared_3507_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3504_);
                                v___x_3506_ = crate::leanh::lean_box(0);
                                v_isShared_3507_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_tail_3499_);
                            return v___x_3504_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_root_3498_);
                        v___x_3526_ = lean_nat_sub(v_start_3489_, v_tailOff_3501_);
                        crate::leanh::lean_dec(v_tailOff_3501_);
                        v___x_3527_ = lean_array_get_size(v_tail_3499_);
                        v___x_3528_ = crate::leanh::lean_box(0);
                        v___x_3529_ = lean_nat_dec_lt(v___x_3526_, v___x_3527_);
                        if v___x_3529_ == 0 {
                            crate::leanh::lean_dec(v___x_3526_);
                            crate::leanh::lean_dec_ref(v_tail_3499_);
                            v___x_3530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3530_, 0, v___x_3528_);
                            return v___x_3530_;
                        } else {
                            v___x_3531_ = lean_nat_dec_le(v___x_3527_, v___x_3527_);
                            if v___x_3531_ == 0 {
                                if v___x_3529_ == 0 {
                                    crate::leanh::lean_dec(v___x_3526_);
                                    crate::leanh::lean_dec_ref(v_tail_3499_);
                                    v___x_3532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3528_);
                                    return v___x_3532_;
                                } else {
                                    v___x_3533_ = lean_usize_of_nat(v___x_3526_);
                                    crate::leanh::lean_dec(v___x_3526_);
                                    v___x_3534_ = lean_usize_of_nat(v___x_3527_);
                                    v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3533_, v___x_3534_, v___x_3528_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                                    crate::leanh::lean_dec_ref(v_tail_3499_);
                                    return v___x_3535_;
                                }
                            } else {
                                v___x_3536_ = lean_usize_of_nat(v___x_3526_);
                                crate::leanh::lean_dec(v___x_3526_);
                                v___x_3537_ = lean_usize_of_nat(v___x_3527_);
                                v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3536_, v___x_3537_, v___x_3528_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                                crate::leanh::lean_dec_ref(v_tail_3499_);
                                return v___x_3538_;
                            }
                        }
                    }
                } else {
                    v___x_3539_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_3488_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                    return v___x_3539_;
                }
            }
            1 => {
                v___x_3508_ = lean_array_get_size(v_tail_3499_);
                v___x_3509_ = crate::leanh::lean_box(0);
                v___x_3510_ = lean_nat_dec_lt(v___x_3496_, v___x_3508_);
                if v___x_3510_ == 0 {
                    crate::leanh::lean_dec_ref(v_tail_3499_);
                    if v_isShared_3507_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3506_, 0, v___x_3509_);
                        v___x_3512_ = v___x_3506_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3509_);
                        v___x_3512_ = v_reuseFailAlloc_3513_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3514_ = lean_nat_dec_le(v___x_3508_, v___x_3508_);
                    if v___x_3514_ == 0 {
                        if v___x_3510_ == 0 {
                            crate::leanh::lean_dec_ref(v_tail_3499_);
                            if v_isShared_3507_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3506_, 0, v___x_3509_);
                                v___x_3516_ = v___x_3506_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3517_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3509_);
                                v___x_3516_ = v_reuseFailAlloc_3517_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3506_);
                            v___x_3518_ = 0usize;
                            v___x_3519_ = lean_usize_of_nat(v___x_3508_);
                            v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3518_, v___x_3519_, v___x_3509_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                            crate::leanh::lean_dec_ref(v_tail_3499_);
                            return v___x_3520_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3506_);
                        v___x_3521_ = 0usize;
                        v___x_3522_ = lean_usize_of_nat(v___x_3508_);
                        v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3521_, v___x_3522_, v___x_3509_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                        crate::leanh::lean_dec_ref(v_tail_3499_);
                        return v___x_3523_;
                    }
                }
            }
            2 => {
                return v___x_3512_;
            }
            3 => {
                return v___x_3516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0___boxed(
    mut v_t_3540_: *mut crate::leanh::LeanObject,
    mut v_start_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v___y_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_3540_, v_start_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
    crate::leanh::lean_dec(v___y_3546_);
    crate::leanh::lean_dec_ref(v___y_3545_);
    crate::leanh::lean_dec(v___y_3544_);
    crate::leanh::lean_dec_ref(v___y_3543_);
    crate::leanh::lean_dec(v___y_3542_);
    crate::leanh::lean_dec(v_start_3541_);
    return v_res_3548_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(
    mut v_lctx_3549_: *mut crate::leanh::LeanObject,
    mut v_start_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_3557_ = crate::leanh::lean_ctor_get(v_lctx_3549_, 1);
    crate::leanh::lean_inc_ref(v_decls_3557_);
    crate::leanh::lean_dec_ref(v_lctx_3549_);
    v___x_3558_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_3557_, v_start_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
    return v___x_3558_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(
    mut v_lctx_3559_: *mut crate::leanh::LeanObject,
    mut v_start_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_3559_, v_start_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
    crate::leanh::lean_dec(v___y_3565_);
    crate::leanh::lean_dec_ref(v___y_3564_);
    crate::leanh::lean_dec(v___y_3563_);
    crate::leanh::lean_dec_ref(v___y_3562_);
    crate::leanh::lean_dec(v___y_3561_);
    crate::leanh::lean_dec(v_start_3560_);
    return v_res_3567_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(
    mut v_e_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
    mut v___y_3570_: *mut crate::leanh::LeanObject,
    mut v___y_3571_: *mut crate::leanh::LeanObject,
    mut v___y_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3581_: u8 = 0;
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_unused_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v_mvarId_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3605_: u8 = 0;
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3611_: u8 = 0;
    let mut v_unused_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut v_a_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3568_) == 1 {
                    v_fvarId_3575_ = crate::leanh::lean_ctor_get(v_e_3568_, 0);
                    crate::leanh::lean_inc(v_fvarId_3575_);
                    crate::leanh::lean_dec_ref_known(v_e_3568_, 1);
                    v___x_3576_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_3575_,
                        v___y_3570_,
                        v___y_3572_,
                        v___y_3573_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3576_) == 0 {
                        v_a_3577_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                        crate::leanh::lean_inc(v_a_3577_);
                        crate::leanh::lean_dec_ref_known(v___x_3576_, 1);
                        v___x_3578_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3577_, v___y_3569_);
                        v_isSharedCheck_3587_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3578_)) as u8;
                        if v_isSharedCheck_3587_ == 0 {
                            v_unused_3588_ = crate::leanh::lean_ctor_get(v___x_3578_, 0);
                            crate::leanh::lean_dec(v_unused_3588_);
                            v___x_3580_ = v___x_3578_;
                            v_isShared_3581_ = v_isSharedCheck_3587_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3578_);
                            v___x_3580_ = crate::leanh::lean_box(0);
                            v_isShared_3581_ = v_isSharedCheck_3587_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3589_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                        v_isSharedCheck_3596_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3576_)) as u8;
                        if v_isSharedCheck_3596_ == 0 {
                            v___x_3591_ = v___x_3576_;
                            v_isShared_3592_ = v_isSharedCheck_3596_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3589_);
                            crate::leanh::lean_dec(v___x_3576_);
                            v___x_3591_ = crate::leanh::lean_box(0);
                            v_isShared_3592_ = v_isSharedCheck_3596_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_e_3568_) == 2 {
                        v_mvarId_3597_ = crate::leanh::lean_ctor_get(v_e_3568_, 0);
                        crate::leanh::lean_inc(v_mvarId_3597_);
                        crate::leanh::lean_dec_ref_known(v_e_3568_, 1);
                        v___x_3598_ = l_Lean_MVarId_getDecl(
                            v_mvarId_3597_,
                            v___y_3570_,
                            v___y_3571_,
                            v___y_3572_,
                            v___y_3573_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3598_) == 0 {
                            v_a_3599_ = crate::leanh::lean_ctor_get(v___x_3598_, 0);
                            crate::leanh::lean_inc(v_a_3599_);
                            crate::leanh::lean_dec_ref_known(v___x_3598_, 1);
                            v_lctx_3600_ = crate::leanh::lean_ctor_get(v_a_3599_, 1);
                            crate::leanh::lean_inc_ref(v_lctx_3600_);
                            crate::leanh::lean_dec(v_a_3599_);
                            v___x_3601_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3602_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_3600_, v___x_3601_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
                            if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
                                v_isSharedCheck_3611_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                                if v_isSharedCheck_3611_ == 0 {
                                    v_unused_3612_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                                    crate::leanh::lean_dec(v_unused_3612_);
                                    v___x_3604_ = v___x_3602_;
                                    v_isShared_3605_ = v_isSharedCheck_3611_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3602_);
                                    v___x_3604_ = crate::leanh::lean_box(0);
                                    v_isShared_3605_ = v_isSharedCheck_3611_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_3613_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                                v_isSharedCheck_3620_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                                if v_isSharedCheck_3620_ == 0 {
                                    v___x_3615_ = v___x_3602_;
                                    v_isShared_3616_ = v_isSharedCheck_3620_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3613_);
                                    crate::leanh::lean_dec(v___x_3602_);
                                    v___x_3615_ = crate::leanh::lean_box(0);
                                    v_isShared_3616_ = v_isSharedCheck_3620_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3621_ = crate::leanh::lean_ctor_get(v___x_3598_, 0);
                            v_isSharedCheck_3628_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3598_)) as u8;
                            if v_isSharedCheck_3628_ == 0 {
                                v___x_3623_ = v___x_3598_;
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3621_);
                                crate::leanh::lean_dec(v___x_3598_);
                                v___x_3623_ = crate::leanh::lean_box(0);
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___x_3629_ = l_Lean_Expr_hasFVar(v_e_3568_);
                        if v___x_3629_ == 0 {
                            v___x_3630_ = l_Lean_Expr_hasExprMVar(v_e_3568_);
                            crate::leanh::lean_dec_ref(v_e_3568_);
                            v___x_3631_ = crate::leanh::lean_box((v___x_3630_) as usize);
                            v___x_3632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3632_, 0, v___x_3631_);
                            return v___x_3632_;
                        } else {
                            crate::leanh::lean_dec_ref(v_e_3568_);
                            v___x_3633_ = crate::leanh::lean_box((v___x_3629_) as usize);
                            v___x_3634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3634_, 0, v___x_3633_);
                            return v___x_3634_;
                        }
                    }
                }
            }
            1 => {
                v___x_3582_ = 0;
                v___x_3583_ = crate::leanh::lean_box((v___x_3582_) as usize);
                if v_isShared_3581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3580_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3585_;
            }
            3 => {
                if v_isShared_3592_ == 0 {
                    v___x_3594_ = v___x_3591_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
                    v___x_3594_ = v_reuseFailAlloc_3595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3594_;
            }
            5 => {
                v___x_3606_ = 0;
                v___x_3607_ = crate::leanh::lean_box((v___x_3606_) as usize);
                if v_isShared_3605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3604_, 0, v___x_3607_);
                    v___x_3609_ = v___x_3604_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
                    v___x_3609_ = v_reuseFailAlloc_3610_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3609_;
            }
            7 => {
                if v_isShared_3616_ == 0 {
                    v___x_3618_ = v___x_3615_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3618_;
            }
            9 => {
                if v_isShared_3624_ == 0 {
                    v___x_3626_ = v___x_3623_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed(
    mut v_e_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3642_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(
            v_e_3635_,
            v___y_3636_,
            v___y_3637_,
            v___y_3638_,
            v___y_3639_,
            v___y_3640_,
        );
    crate::leanh::lean_dec(v___y_3640_);
    crate::leanh::lean_dec_ref(v___y_3639_);
    crate::leanh::lean_dec(v___y_3638_);
    crate::leanh::lean_dec_ref(v___y_3637_);
    crate::leanh::lean_dec(v___y_3636_);
    return v_res_3642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(
    mut v_a_3643_: *mut crate::leanh::LeanObject,
    mut v_x_3644_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3645_: u8 = 0;
    let mut v_key_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3644_) == 0 {
                    v___x_3645_ = 0;
                    return v___x_3645_;
                } else {
                    v_key_3646_ = crate::leanh::lean_ctor_get(v_x_3644_, 0);
                    v_tail_3647_ = crate::leanh::lean_ctor_get(v_x_3644_, 2);
                    v___x_3648_ = lean_expr_eqv(v_key_3646_, v_a_3643_);
                    if v___x_3648_ == 0 {
                        v_x_3644_ = v_tail_3647_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3648_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_a_3650_: *mut crate::leanh::LeanObject,
    mut v_x_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3652_: u8 = 0;
    let mut v_r_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_3650_, v_x_3651_);
    crate::leanh::lean_dec(v_x_3651_);
    crate::leanh::lean_dec_ref(v_a_3650_);
    v_r_3653_ = crate::leanh::lean_box((v_res_3652_) as usize);
    return v_r_3653_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(
    mut v_x_3654_: *mut crate::leanh::LeanObject,
    mut v_x_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: u64 = 0;
    let mut v___x_3664_: u64 = 0;
    let mut v___x_3665_: u64 = 0;
    let mut v_fold_3666_: u64 = 0;
    let mut v___x_3667_: u64 = 0;
    let mut v___x_3668_: u64 = 0;
    let mut v___x_3669_: u64 = 0;
    let mut v___x_3670_: usize = 0;
    let mut v___x_3671_: usize = 0;
    let mut v___x_3672_: usize = 0;
    let mut v___x_3673_: usize = 0;
    let mut v___x_3674_: usize = 0;
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3655_) == 0 {
                    return v_x_3654_;
                } else {
                    v_key_3656_ = crate::leanh::lean_ctor_get(v_x_3655_, 0);
                    v_value_3657_ = crate::leanh::lean_ctor_get(v_x_3655_, 1);
                    v_tail_3658_ = crate::leanh::lean_ctor_get(v_x_3655_, 2);
                    v_isSharedCheck_3681_ = (!crate::leanh::lean_is_exclusive(v_x_3655_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3660_ = v_x_3655_;
                        v_isShared_3661_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3658_);
                        crate::leanh::lean_inc(v_value_3657_);
                        crate::leanh::lean_inc(v_key_3656_);
                        crate::leanh::lean_dec(v_x_3655_);
                        v___x_3660_ = crate::leanh::lean_box(0);
                        v_isShared_3661_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3662_ = lean_array_get_size(v_x_3654_);
                v___x_3663_ = l_Lean_Expr_hash(v_key_3656_);
                v___x_3664_ = 32u64;
                v___x_3665_ = lean_uint64_shift_right(v___x_3663_, v___x_3664_);
                v_fold_3666_ = lean_uint64_xor(v___x_3663_, v___x_3665_);
                v___x_3667_ = 16u64;
                v___x_3668_ = lean_uint64_shift_right(v_fold_3666_, v___x_3667_);
                v___x_3669_ = lean_uint64_xor(v_fold_3666_, v___x_3668_);
                v___x_3670_ = lean_uint64_to_usize(v___x_3669_);
                v___x_3671_ = lean_usize_of_nat(v___x_3662_);
                v___x_3672_ = 1usize;
                v___x_3673_ = lean_usize_sub(v___x_3671_, v___x_3672_);
                v___x_3674_ = lean_usize_land(v___x_3670_, v___x_3673_);
                v___x_3675_ = lean_array_uget_borrowed(v_x_3654_, v___x_3674_);
                crate::leanh::lean_inc(v___x_3675_);
                if v_isShared_3661_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3660_, 2, v___x_3675_);
                    v___x_3677_ = v___x_3660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_key_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_value_3657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 2, v___x_3675_);
                    v___x_3677_ = v_reuseFailAlloc_3680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3678_ = lean_array_uset(v_x_3654_, v___x_3674_, v___x_3677_);
                v_x_3654_ = v___x_3678_;
                v_x_3655_ = v_tail_3658_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(
    mut v_i_3682_: *mut crate::leanh::LeanObject,
    mut v_source_3683_: *mut crate::leanh::LeanObject,
    mut v_target_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: u8 = 0;
    let mut v_es_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3685_ = lean_array_get_size(v_source_3683_);
                v___x_3686_ = lean_nat_dec_lt(v_i_3682_, v___x_3685_);
                if v___x_3686_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3683_);
                    crate::leanh::lean_dec(v_i_3682_);
                    return v_target_3684_;
                } else {
                    v_es_3687_ = lean_array_fget(v_source_3683_, v_i_3682_);
                    v___x_3688_ = crate::leanh::lean_box(0);
                    v_source_3689_ = lean_array_fset(v_source_3683_, v_i_3682_, v___x_3688_);
                    v_target_3690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_3684_, v_es_3687_);
                    v___x_3691_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3692_ = lean_nat_add(v_i_3682_, v___x_3691_);
                    crate::leanh::lean_dec(v_i_3682_);
                    v_i_3682_ = v___x_3692_;
                    v_source_3683_ = v_source_3689_;
                    v_target_3684_ = v_target_3690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(
    mut v_data_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = lean_array_get_size(v_data_3694_);
    v___x_3696_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3697_ = lean_nat_mul(v___x_3695_, v___x_3696_);
    v___x_3698_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3699_ = crate::leanh::lean_box(0);
    v___x_3700_ = lean_mk_array(v_nbuckets_3697_, v___x_3699_);
    v___x_3701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_3698_, v_data_3694_, v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v_b_3703_: *mut crate::leanh::LeanObject,
    mut v_x_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3704_) == 0 {
                    crate::leanh::lean_dec(v_b_3703_);
                    crate::leanh::lean_dec_ref(v_a_3702_);
                    return v_x_3704_;
                } else {
                    v_key_3705_ = crate::leanh::lean_ctor_get(v_x_3704_, 0);
                    v_value_3706_ = crate::leanh::lean_ctor_get(v_x_3704_, 1);
                    v_tail_3707_ = crate::leanh::lean_ctor_get(v_x_3704_, 2);
                    v_isSharedCheck_3719_ = (!crate::leanh::lean_is_exclusive(v_x_3704_)) as u8;
                    if v_isSharedCheck_3719_ == 0 {
                        v___x_3709_ = v_x_3704_;
                        v_isShared_3710_ = v_isSharedCheck_3719_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3707_);
                        crate::leanh::lean_inc(v_value_3706_);
                        crate::leanh::lean_inc(v_key_3705_);
                        crate::leanh::lean_dec(v_x_3704_);
                        v___x_3709_ = crate::leanh::lean_box(0);
                        v_isShared_3710_ = v_isSharedCheck_3719_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3711_ = lean_expr_eqv(v_key_3705_, v_a_3702_);
                if v___x_3711_ == 0 {
                    v___x_3712_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_3702_, v_b_3703_, v_tail_3707_);
                    if v_isShared_3710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3709_, 2, v___x_3712_);
                        v___x_3714_ = v___x_3709_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3715_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_key_3705_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_value_3706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 2, v___x_3712_);
                        v___x_3714_ = v_reuseFailAlloc_3715_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3706_);
                    crate::leanh::lean_dec(v_key_3705_);
                    if v_isShared_3710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3709_, 1, v_b_3703_);
                        crate::leanh::lean_ctor_set(v___x_3709_, 0, v_a_3702_);
                        v___x_3717_ = v___x_3709_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_b_3703_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_tail_3707_);
                        v___x_3717_ = v_reuseFailAlloc_3718_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3714_;
            }
            3 => {
                return v___x_3717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(
    mut v_m_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_b_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u64 = 0;
    let mut v___x_3730_: u64 = 0;
    let mut v___x_3731_: u64 = 0;
    let mut v_fold_3732_: u64 = 0;
    let mut v___x_3733_: u64 = 0;
    let mut v___x_3734_: u64 = 0;
    let mut v___x_3735_: u64 = 0;
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3738_: usize = 0;
    let mut v___x_3739_: usize = 0;
    let mut v___x_3740_: usize = 0;
    let mut v_bkt_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v_val_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3723_ = crate::leanh::lean_ctor_get(v_m_3720_, 0);
                v_buckets_3724_ = crate::leanh::lean_ctor_get(v_m_3720_, 1);
                v_isSharedCheck_3767_ = (!crate::leanh::lean_is_exclusive(v_m_3720_)) as u8;
                if v_isSharedCheck_3767_ == 0 {
                    v___x_3726_ = v_m_3720_;
                    v_isShared_3727_ = v_isSharedCheck_3767_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3724_);
                    crate::leanh::lean_inc(v_size_3723_);
                    crate::leanh::lean_dec(v_m_3720_);
                    v___x_3726_ = crate::leanh::lean_box(0);
                    v_isShared_3727_ = v_isSharedCheck_3767_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3728_ = lean_array_get_size(v_buckets_3724_);
                v___x_3729_ = l_Lean_Expr_hash(v_a_3721_);
                v___x_3730_ = 32u64;
                v___x_3731_ = lean_uint64_shift_right(v___x_3729_, v___x_3730_);
                v_fold_3732_ = lean_uint64_xor(v___x_3729_, v___x_3731_);
                v___x_3733_ = 16u64;
                v___x_3734_ = lean_uint64_shift_right(v_fold_3732_, v___x_3733_);
                v___x_3735_ = lean_uint64_xor(v_fold_3732_, v___x_3734_);
                v___x_3736_ = lean_uint64_to_usize(v___x_3735_);
                v___x_3737_ = lean_usize_of_nat(v___x_3728_);
                v___x_3738_ = 1usize;
                v___x_3739_ = lean_usize_sub(v___x_3737_, v___x_3738_);
                v___x_3740_ = lean_usize_land(v___x_3736_, v___x_3739_);
                v_bkt_3741_ = lean_array_uget_borrowed(v_buckets_3724_, v___x_3740_);
                v___x_3742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_3721_, v_bkt_3741_);
                if v___x_3742_ == 0 {
                    v___x_3743_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3744_ = lean_nat_add(v_size_3723_, v___x_3743_);
                    crate::leanh::lean_dec(v_size_3723_);
                    crate::leanh::lean_inc(v_bkt_3741_);
                    v___x_3745_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3745_, 0, v_a_3721_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 1, v_b_3722_);
                    crate::leanh::lean_ctor_set(v___x_3745_, 2, v_bkt_3741_);
                    v_buckets_x27_3746_ =
                        lean_array_uset(v_buckets_3724_, v___x_3740_, v___x_3745_);
                    v___x_3747_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3748_ = lean_nat_mul(v_size_x27_3744_, v___x_3747_);
                    v___x_3749_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3750_ = lean_nat_div(v___x_3748_, v___x_3749_);
                    crate::leanh::lean_dec(v___x_3748_);
                    v___x_3751_ = lean_array_get_size(v_buckets_x27_3746_);
                    v___x_3752_ = lean_nat_dec_le(v___x_3750_, v___x_3751_);
                    crate::leanh::lean_dec(v___x_3750_);
                    if v___x_3752_ == 0 {
                        v_val_3753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_3746_);
                        if v_isShared_3727_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3726_, 1, v_val_3753_);
                            crate::leanh::lean_ctor_set(v___x_3726_, 0, v_size_x27_3744_);
                            v___x_3755_ = v___x_3726_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3756_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3756_,
                                0,
                                v_size_x27_3744_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_val_3753_);
                            v___x_3755_ = v_reuseFailAlloc_3756_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3727_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3726_, 1, v_buckets_x27_3746_);
                            crate::leanh::lean_ctor_set(v___x_3726_, 0, v_size_x27_3744_);
                            v___x_3758_ = v___x_3726_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3759_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3759_,
                                0,
                                v_size_x27_3744_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3759_,
                                1,
                                v_buckets_x27_3746_,
                            );
                            v___x_3758_ = v_reuseFailAlloc_3759_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3741_);
                    v___x_3760_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3761_ =
                        lean_array_uset(v_buckets_3724_, v___x_3740_, v___x_3760_);
                    v___x_3762_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_3721_, v_b_3722_, v_bkt_3741_);
                    v___x_3763_ = lean_array_uset(v_buckets_x27_3761_, v___x_3740_, v___x_3762_);
                    if v_isShared_3727_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3726_, 1, v___x_3763_);
                        v___x_3765_ = v___x_3726_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3766_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_size_3723_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3766_, 1, v___x_3763_);
                        v___x_3765_ = v_reuseFailAlloc_3766_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3755_;
            }
            3 => {
                return v___x_3758_;
            }
            4 => {
                return v___x_3765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(
    mut v_a_3768_: *mut crate::leanh::LeanObject,
    mut v_x_3769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3769_) == 0 {
                    v___x_3770_ = crate::leanh::lean_box(0);
                    return v___x_3770_;
                } else {
                    v_key_3771_ = crate::leanh::lean_ctor_get(v_x_3769_, 0);
                    v_value_3772_ = crate::leanh::lean_ctor_get(v_x_3769_, 1);
                    v_tail_3773_ = crate::leanh::lean_ctor_get(v_x_3769_, 2);
                    v___x_3774_ = lean_expr_eqv(v_key_3771_, v_a_3768_);
                    if v___x_3774_ == 0 {
                        v_x_3769_ = v_tail_3773_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3772_);
                        v___x_3776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3776_, 0, v_value_3772_);
                        return v___x_3776_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_x_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_3777_, v_x_3778_);
    crate::leanh::lean_dec(v_x_3778_);
    crate::leanh::lean_dec_ref(v_a_3777_);
    return v_res_3779_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(
    mut v_m_3780_: *mut crate::leanh::LeanObject,
    mut v_a_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u64 = 0;
    let mut v___x_3785_: u64 = 0;
    let mut v___x_3786_: u64 = 0;
    let mut v_fold_3787_: u64 = 0;
    let mut v___x_3788_: u64 = 0;
    let mut v___x_3789_: u64 = 0;
    let mut v___x_3790_: u64 = 0;
    let mut v___x_3791_: usize = 0;
    let mut v___x_3792_: usize = 0;
    let mut v___x_3793_: usize = 0;
    let mut v___x_3794_: usize = 0;
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3782_ = crate::leanh::lean_ctor_get(v_m_3780_, 1);
    v___x_3783_ = lean_array_get_size(v_buckets_3782_);
    v___x_3784_ = l_Lean_Expr_hash(v_a_3781_);
    v___x_3785_ = 32u64;
    v___x_3786_ = lean_uint64_shift_right(v___x_3784_, v___x_3785_);
    v_fold_3787_ = lean_uint64_xor(v___x_3784_, v___x_3786_);
    v___x_3788_ = 16u64;
    v___x_3789_ = lean_uint64_shift_right(v_fold_3787_, v___x_3788_);
    v___x_3790_ = lean_uint64_xor(v_fold_3787_, v___x_3789_);
    v___x_3791_ = lean_uint64_to_usize(v___x_3790_);
    v___x_3792_ = lean_usize_of_nat(v___x_3783_);
    v___x_3793_ = 1usize;
    v___x_3794_ = lean_usize_sub(v___x_3792_, v___x_3793_);
    v___x_3795_ = lean_usize_land(v___x_3791_, v___x_3794_);
    v___x_3796_ = lean_array_uget_borrowed(v_buckets_3782_, v___x_3795_);
    v___x_3797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_3781_, v___x_3796_);
    return v___x_3797_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg___boxed(
    mut v_m_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_3798_, v_a_3799_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    crate::leanh::lean_dec_ref(v_m_3798_);
    return v_res_3800_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(
    mut v_g_3801_: *mut crate::leanh::LeanObject,
    mut v_e_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut v_val_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = lean_st_ref_get(v_a_3803_);
                v___x_3820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_3819_, v_e_3802_);
                crate::leanh::lean_dec(v___x_3819_);
                if crate::leanh::lean_obj_tag(v___x_3820_) == 0 {
                    crate::leanh::lean_inc_ref(v_g_3801_);
                    crate::leanh::lean_inc(v___y_3808_);
                    crate::leanh::lean_inc_ref(v___y_3807_);
                    crate::leanh::lean_inc(v___y_3806_);
                    crate::leanh::lean_inc_ref(v___y_3805_);
                    crate::leanh::lean_inc(v___y_3804_);
                    crate::leanh::lean_inc_ref(v_e_3802_);
                    v___x_3821_ = crate::leanh::lean_apply_7(
                        v_g_3801_,
                        v_e_3802_,
                        v___y_3804_,
                        v___y_3805_,
                        v___y_3806_,
                        v___y_3807_,
                        v___y_3808_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3821_) == 0 {
                        v_a_3822_ = crate::leanh::lean_ctor_get(v___x_3821_, 0);
                        crate::leanh::lean_inc(v_a_3822_);
                        crate::leanh::lean_dec_ref_known(v___x_3821_, 1);
                        v___x_3829_ = (crate::leanh::lean_unbox(v_a_3822_) as u8);
                        crate::leanh::lean_dec(v_a_3822_);
                        if v___x_3829_ == 0 {
                            crate::leanh::lean_dec_ref(v_g_3801_);
                            v___x_3830_ = crate::leanh::lean_box(0);
                            v_a_3811_ = v___x_3830_;
                            state = 1;
                            continue;
                        } else {
                            match crate::leanh::lean_obj_tag(v_e_3802_) {
                                7 => {
                                    v_binderType_3831_ = crate::leanh::lean_ctor_get(v_e_3802_, 1);
                                    v_body_3832_ = crate::leanh::lean_ctor_get(v_e_3802_, 2);
                                    crate::leanh::lean_inc_ref(v_body_3832_);
                                    crate::leanh::lean_inc_ref(v_binderType_3831_);
                                    v_d_3824_ = v_binderType_3831_;
                                    v_b_3825_ = v_body_3832_;
                                    v___y_3826_ = v_a_3803_;
                                    state = 3;
                                    continue;
                                }
                                6 => {
                                    v_binderType_3833_ = crate::leanh::lean_ctor_get(v_e_3802_, 1);
                                    v_body_3834_ = crate::leanh::lean_ctor_get(v_e_3802_, 2);
                                    crate::leanh::lean_inc_ref(v_body_3834_);
                                    crate::leanh::lean_inc_ref(v_binderType_3833_);
                                    v_d_3824_ = v_binderType_3833_;
                                    v_b_3825_ = v_body_3834_;
                                    v___y_3826_ = v_a_3803_;
                                    state = 3;
                                    continue;
                                }
                                8 => {
                                    v_type_3835_ = crate::leanh::lean_ctor_get(v_e_3802_, 1);
                                    v_value_3836_ = crate::leanh::lean_ctor_get(v_e_3802_, 2);
                                    v_body_3837_ = crate::leanh::lean_ctor_get(v_e_3802_, 3);
                                    crate::leanh::lean_inc_ref(v_type_3835_);
                                    crate::leanh::lean_inc_ref(v_g_3801_);
                                    v___x_3838_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_type_3835_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    if crate::leanh::lean_obj_tag(v___x_3838_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3838_, 1);
                                        crate::leanh::lean_inc_ref(v_value_3836_);
                                        crate::leanh::lean_inc_ref(v_g_3801_);
                                        v___x_3839_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_value_3836_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                        if crate::leanh::lean_obj_tag(v___x_3839_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3839_, 1);
                                            crate::leanh::lean_inc_ref(v_body_3837_);
                                            v___x_3840_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_body_3837_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                            v___y_3817_ = v___x_3840_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_g_3801_);
                                            v___y_3817_ = v___x_3839_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_g_3801_);
                                        v___y_3817_ = v___x_3838_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                5 => {
                                    v_fn_3841_ = crate::leanh::lean_ctor_get(v_e_3802_, 0);
                                    v_arg_3842_ = crate::leanh::lean_ctor_get(v_e_3802_, 1);
                                    crate::leanh::lean_inc_ref(v_fn_3841_);
                                    crate::leanh::lean_inc_ref(v_g_3801_);
                                    v___x_3843_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_fn_3841_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    if crate::leanh::lean_obj_tag(v___x_3843_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3843_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_3842_);
                                        v___x_3844_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_arg_3842_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                        v___y_3817_ = v___x_3844_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_g_3801_);
                                        v___y_3817_ = v___x_3843_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                10 => {
                                    v_expr_3845_ = crate::leanh::lean_ctor_get(v_e_3802_, 1);
                                    crate::leanh::lean_inc_ref(v_expr_3845_);
                                    v___x_3846_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_expr_3845_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    v___y_3817_ = v___x_3846_;
                                    state = 2;
                                    continue;
                                }
                                11 => {
                                    v_struct_3847_ = crate::leanh::lean_ctor_get(v_e_3802_, 2);
                                    crate::leanh::lean_inc_ref(v_struct_3847_);
                                    v___x_3848_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_struct_3847_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    v___y_3817_ = v___x_3848_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    crate::leanh::lean_dec_ref(v_g_3801_);
                                    v___x_3849_ = crate::leanh::lean_box(0);
                                    v_a_3811_ = v___x_3849_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3802_);
                        crate::leanh::lean_dec_ref(v_g_3801_);
                        v_a_3850_ = crate::leanh::lean_ctor_get(v___x_3821_, 0);
                        v_isSharedCheck_3857_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3821_)) as u8;
                        if v_isSharedCheck_3857_ == 0 {
                            v___x_3852_ = v___x_3821_;
                            v_isShared_3853_ = v_isSharedCheck_3857_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3850_);
                            crate::leanh::lean_dec(v___x_3821_);
                            v___x_3852_ = crate::leanh::lean_box(0);
                            v_isShared_3853_ = v_isSharedCheck_3857_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3802_);
                    crate::leanh::lean_dec_ref(v_g_3801_);
                    v_val_3858_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3865_ = (!crate::leanh::lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3865_ == 0 {
                        v___x_3860_ = v___x_3820_;
                        v_isShared_3861_ = v_isSharedCheck_3865_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3858_);
                        crate::leanh::lean_dec(v___x_3820_);
                        v___x_3860_ = crate::leanh::lean_box(0);
                        v_isShared_3861_ = v_isSharedCheck_3865_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3812_ = lean_st_ref_take(v_a_3803_);
                v___x_3813_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v___x_3812_, v_e_3802_, v_a_3811_);
                v___x_3814_ = lean_st_ref_set(v_a_3803_, v___x_3813_);
                v___x_3815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3815_, 0, v_a_3811_);
                return v___x_3815_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3817_) == 0 {
                    v_a_3818_ = crate::leanh::lean_ctor_get(v___y_3817_, 0);
                    crate::leanh::lean_inc(v_a_3818_);
                    crate::leanh::lean_dec_ref_known(v___y_3817_, 1);
                    v_a_3811_ = v_a_3818_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3802_);
                    return v___y_3817_;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_g_3801_);
                v___x_3827_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_d_3824_, v___y_3826_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                if crate::leanh::lean_obj_tag(v___x_3827_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3827_, 1);
                    v___x_3828_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_b_3825_, v___y_3826_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                    v___y_3817_ = v___x_3828_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3825_);
                    crate::leanh::lean_dec_ref(v_g_3801_);
                    v___y_3817_ = v___x_3827_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_3853_ == 0 {
                    v___x_3855_ = v___x_3852_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
                    v___x_3855_ = v_reuseFailAlloc_3856_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3855_;
            }
            6 => {
                if v_isShared_3861_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3860_, 0);
                    v___x_3863_ = v___x_3860_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_val_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3864_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1___boxed(
    mut v_g_3866_: *mut crate::leanh::LeanObject,
    mut v_e_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3866_, v_e_3867_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
    crate::leanh::lean_dec(v___y_3873_);
    crate::leanh::lean_dec_ref(v___y_3872_);
    crate::leanh::lean_dec(v___y_3871_);
    crate::leanh::lean_dec_ref(v___y_3870_);
    crate::leanh::lean_dec(v___y_3869_);
    crate::leanh::lean_dec(v_a_3868_);
    return v_res_3875_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3876_ = crate::leanh::lean_box(0);
    v___x_3877_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3878_ = lean_mk_array(v___x_3877_, v___x_3876_);
    return v___x_3878_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once), _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0);
    v___x_3880_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3881_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3881_, 0, v___x_3880_);
    crate::leanh::lean_ctor_set(v___x_3881_, 1, v___x_3879_);
    return v___x_3881_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(
    mut v_e_3883_: *mut crate::leanh::LeanObject,
    mut v_a_3884_: *mut crate::leanh::LeanObject,
    mut v_a_3885_: *mut crate::leanh::LeanObject,
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once), _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
                v___x_3891_ = lean_st_mk_ref(v___x_3890_);
                v___f_3892_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2;
                v___x_3893_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_3892_, v_e_3883_, v___x_3891_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
                if crate::leanh::lean_obj_tag(v___x_3893_) == 0 {
                    v_a_3894_ = crate::leanh::lean_ctor_get(v___x_3893_, 0);
                    v_isSharedCheck_3902_ = (!crate::leanh::lean_is_exclusive(v___x_3893_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3896_ = v___x_3893_;
                        v_isShared_3897_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3894_);
                        crate::leanh::lean_dec(v___x_3893_);
                        v___x_3896_ = crate::leanh::lean_box(0);
                        v_isShared_3897_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3891_);
                    return v___x_3893_;
                }
            }
            1 => {
                v___x_3898_ = lean_st_ref_get(v___x_3891_);
                crate::leanh::lean_dec(v___x_3891_);
                crate::leanh::lean_dec(v___x_3898_);
                if v_isShared_3897_ == 0 {
                    v___x_3900_ = v___x_3896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3894_);
                    v___x_3900_ = v_reuseFailAlloc_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___boxed(
    mut v_e_3903_: *mut crate::leanh::LeanObject,
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3910_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(
        v_e_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_,
    );
    crate::leanh::lean_dec(v_a_3908_);
    crate::leanh::lean_dec_ref(v_a_3907_);
    crate::leanh::lean_dec(v_a_3906_);
    crate::leanh::lean_dec_ref(v_a_3905_);
    crate::leanh::lean_dec(v_a_3904_);
    return v_res_3910_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(
    mut v_00_u03b2_3911_: *mut crate::leanh::LeanObject,
    mut v_m_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_3912_, v_a_3913_);
    return v___x_3914_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_3915_: *mut crate::leanh::LeanObject,
    mut v_m_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_3915_, v_m_3916_, v_a_3917_);
    crate::leanh::lean_dec_ref(v_a_3917_);
    crate::leanh::lean_dec_ref(v_m_3916_);
    return v_res_3918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(
    mut v_00_u03b2_3919_: *mut crate::leanh::LeanObject,
    mut v_m_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_b_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_3920_, v_a_3921_, v_b_3922_);
    return v___x_3923_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(
    mut v_00_u03b2_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_x_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3927_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_3925_, v_x_3926_);
    return v___x_3927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v_x_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_3928_, v_a_3929_, v_x_3930_);
    crate::leanh::lean_dec(v_x_3930_);
    crate::leanh::lean_dec_ref(v_a_3929_);
    return v_res_3931_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(
    mut v_00_u03b2_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_x_3934_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3935_: u8 = 0;
    v___x_3935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_3933_, v_x_3934_);
    return v___x_3935_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3939_: u8 = 0;
    let mut v_r_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_3936_, v_a_3937_, v_x_3938_);
    crate::leanh::lean_dec(v_x_3938_);
    crate::leanh::lean_dec_ref(v_a_3937_);
    v_r_3940_ = crate::leanh::lean_box((v_res_3939_) as usize);
    return v_r_3940_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(
    mut v_00_u03b2_3941_: *mut crate::leanh::LeanObject,
    mut v_data_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(
    mut v_00_u03b2_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_b_3946_: *mut crate::leanh::LeanObject,
    mut v_x_3947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_3945_, v_b_3946_, v_x_3947_);
    return v___x_3948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(
    mut v_as_3949_: *mut crate::leanh::LeanObject,
    mut v_i_3950_: usize,
    mut v_stop_3951_: usize,
    mut v_b_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_3949_, v_i_3950_, v_stop_3951_, v_b_3952_, v___y_3953_, v___y_3954_, v___y_3956_, v___y_3957_);
    return v___x_3959_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_as_3960_: *mut crate::leanh::LeanObject,
    mut v_i_3961_: *mut crate::leanh::LeanObject,
    mut v_stop_3962_: *mut crate::leanh::LeanObject,
    mut v_b_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3970_: usize = 0;
    let mut v_stop_boxed_3971_: usize = 0;
    let mut v_res_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3970_ = crate::leanh::lean_unbox_usize(v_i_3961_);
    crate::leanh::lean_dec(v_i_3961_);
    v_stop_boxed_3971_ = crate::leanh::lean_unbox_usize(v_stop_3962_);
    crate::leanh::lean_dec(v_stop_3962_);
    v_res_3972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_3960_, v_i_boxed_3970_, v_stop_boxed_3971_, v_b_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
    crate::leanh::lean_dec(v___y_3968_);
    crate::leanh::lean_dec_ref(v___y_3967_);
    crate::leanh::lean_dec(v___y_3966_);
    crate::leanh::lean_dec_ref(v___y_3965_);
    crate::leanh::lean_dec(v___y_3964_);
    crate::leanh::lean_dec_ref(v_as_3960_);
    return v_res_3972_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(
    mut v_00_u03b2_3973_: *mut crate::leanh::LeanObject,
    mut v_i_3974_: *mut crate::leanh::LeanObject,
    mut v_source_3975_: *mut crate::leanh::LeanObject,
    mut v_target_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_3974_, v_source_3975_, v_target_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(
    mut v_00_u03b2_3978_: *mut crate::leanh::LeanObject,
    mut v_x_3979_: *mut crate::leanh::LeanObject,
    mut v_x_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_3979_, v_x_3980_);
    return v___x_3981_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
    mut v_e_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: u8 = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4005_: u8 = 0;
    let mut v_unused_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3985_ = l_Lean_Expr_hasMVar(v_e_3982_);
                if v___x_3985_ == 0 {
                    v___x_3986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3986_, 0, v_e_3982_);
                    return v___x_3986_;
                } else {
                    v___x_3987_ = lean_st_ref_get(v___y_3983_);
                    v_mctx_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3988_);
                    crate::leanh::lean_dec(v___x_3987_);
                    v___x_3989_ = l_Lean_instantiateMVarsCore(v_mctx_3988_, v_e_3982_);
                    v_fst_3990_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                    crate::leanh::lean_inc(v_fst_3990_);
                    v_snd_3991_ = crate::leanh::lean_ctor_get(v___x_3989_, 1);
                    crate::leanh::lean_inc(v_snd_3991_);
                    crate::leanh::lean_dec_ref(v___x_3989_);
                    v___x_3992_ = lean_st_ref_take(v___y_3983_);
                    v_cache_3993_ = crate::leanh::lean_ctor_get(v___x_3992_, 1);
                    v_zetaDeltaFVarIds_3994_ = crate::leanh::lean_ctor_get(v___x_3992_, 2);
                    v_postponed_3995_ = crate::leanh::lean_ctor_get(v___x_3992_, 3);
                    v_diag_3996_ = crate::leanh::lean_ctor_get(v___x_3992_, 4);
                    v_isSharedCheck_4005_ = (!crate::leanh::lean_is_exclusive(v___x_3992_)) as u8;
                    if v_isSharedCheck_4005_ == 0 {
                        v_unused_4006_ = crate::leanh::lean_ctor_get(v___x_3992_, 0);
                        crate::leanh::lean_dec(v_unused_4006_);
                        v___x_3998_ = v___x_3992_;
                        v_isShared_3999_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3996_);
                        crate::leanh::lean_inc(v_postponed_3995_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3994_);
                        crate::leanh::lean_inc(v_cache_3993_);
                        crate::leanh::lean_dec(v___x_3992_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3998_, 0, v_snd_3991_);
                    v___x_4001_ = v___x_3998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4004_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_snd_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_cache_3993_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4004_,
                        2,
                        v_zetaDeltaFVarIds_3994_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_postponed_3995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_diag_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4002_ = lean_st_ref_set(v___y_3983_, v___x_4001_);
                v___x_4003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4003_, 0, v_fst_3990_);
                return v___x_4003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(
    mut v_e_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4010_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
        v_e_4007_,
        v___y_4008_,
    );
    crate::leanh::lean_dec(v___y_4008_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(
    mut v_e_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
        v_e_4011_,
        v___y_4013_,
    );
    return v___x_4017_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(
    mut v_e_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(
        v_e_4018_,
        v___y_4019_,
        v___y_4020_,
        v___y_4021_,
        v___y_4022_,
    );
    crate::leanh::lean_dec(v___y_4022_);
    crate::leanh::lean_dec_ref(v___y_4021_);
    crate::leanh::lean_dec(v___y_4020_);
    crate::leanh::lean_dec_ref(v___y_4019_);
    return v_res_4024_;
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27___lam__0(
    mut v_type_4025_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4026_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4027_: *mut crate::leanh::LeanObject,
    mut v_userName_4028_: *mut crate::leanh::LeanObject,
    mut v_val_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4035_ =
                    l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
                        v_type_4025_,
                        v___y_4031_,
                    );
                v_a_4036_ = crate::leanh::lean_ctor_get(v___x_4035_, 0);
                crate::leanh::lean_inc(v_a_4036_);
                crate::leanh::lean_dec_ref(v___x_4035_);
                v___x_4037_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_4026_,
                    v___y_4030_,
                    v___y_4032_,
                    v___y_4033_,
                );
                if crate::leanh::lean_obj_tag(v___x_4037_) == 0 {
                    v_a_4038_ = crate::leanh::lean_ctor_get(v___x_4037_, 0);
                    crate::leanh::lean_inc(v_a_4038_);
                    crate::leanh::lean_dec_ref_known(v___x_4037_, 1);
                    v___x_4039_ = lean_st_mk_ref(v_a_4038_);
                    crate::leanh::lean_inc(v_a_4036_);
                    v___x_4040_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_4036_, v___x_4039_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
                    if crate::leanh::lean_obj_tag(v___x_4040_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4040_, 1);
                        v___x_4041_ = lean_st_ref_get(v___x_4039_);
                        crate::leanh::lean_dec(v___x_4039_);
                        v___x_4042_ = l_Lean_LocalDecl_fvarId(v___x_4041_);
                        crate::leanh::lean_dec(v___x_4041_);
                        v___x_4043_ = l_Lean_MVarId_assertAfter(
                            v_mvarId_4027_,
                            v___x_4042_,
                            v_userName_4028_,
                            v_a_4036_,
                            v_val_4029_,
                            v___y_4030_,
                            v___y_4031_,
                            v___y_4032_,
                            v___y_4033_,
                        );
                        return v___x_4043_;
                    } else {
                        crate::leanh::lean_dec(v___x_4039_);
                        crate::leanh::lean_dec(v_a_4036_);
                        crate::leanh::lean_dec_ref(v_val_4029_);
                        crate::leanh::lean_dec(v_userName_4028_);
                        crate::leanh::lean_dec(v_mvarId_4027_);
                        v_a_4044_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                        v_isSharedCheck_4051_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4040_)) as u8;
                        if v_isSharedCheck_4051_ == 0 {
                            v___x_4046_ = v___x_4040_;
                            v_isShared_4047_ = v_isSharedCheck_4051_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4044_);
                            crate::leanh::lean_dec(v___x_4040_);
                            v___x_4046_ = crate::leanh::lean_box(0);
                            v_isShared_4047_ = v_isSharedCheck_4051_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4036_);
                    crate::leanh::lean_dec_ref(v_val_4029_);
                    crate::leanh::lean_dec(v_userName_4028_);
                    crate::leanh::lean_dec(v_mvarId_4027_);
                    v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4059_ = (!crate::leanh::lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4059_ == 0 {
                        v___x_4054_ = v___x_4037_;
                        v_isShared_4055_ = v_isSharedCheck_4059_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4052_);
                        crate::leanh::lean_dec(v___x_4037_);
                        v___x_4054_ = crate::leanh::lean_box(0);
                        v_isShared_4055_ = v_isSharedCheck_4059_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4047_ == 0 {
                    v___x_4049_ = v___x_4046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
                    v___x_4049_ = v_reuseFailAlloc_4050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4049_;
            }
            3 => {
                if v_isShared_4055_ == 0 {
                    v___x_4057_ = v___x_4054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
                    v___x_4057_ = v_reuseFailAlloc_4058_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27___lam__0___boxed(
    mut v_type_4060_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4061_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4062_: *mut crate::leanh::LeanObject,
    mut v_userName_4063_: *mut crate::leanh::LeanObject,
    mut v_val_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4070_ = l_Lean_MVarId_assertAfter_x27___lam__0(
        v_type_4060_,
        v_fvarId_4061_,
        v_mvarId_4062_,
        v_userName_4063_,
        v_val_4064_,
        v___y_4065_,
        v___y_4066_,
        v___y_4067_,
        v___y_4068_,
    );
    crate::leanh::lean_dec(v___y_4068_);
    crate::leanh::lean_dec_ref(v___y_4067_);
    crate::leanh::lean_dec(v___y_4066_);
    crate::leanh::lean_dec_ref(v___y_4065_);
    return v_res_4070_;
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27(
    mut v_mvarId_4071_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4072_: *mut crate::leanh::LeanObject,
    mut v_userName_4073_: *mut crate::leanh::LeanObject,
    mut v_type_4074_: *mut crate::leanh::LeanObject,
    mut v_val_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
    mut v_a_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_4071_);
    v___f_4081_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_assertAfter_x27___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4081_, 0, v_type_4074_);
    crate::leanh::lean_closure_set(v___f_4081_, 1, v_fvarId_4072_);
    crate::leanh::lean_closure_set(v___f_4081_, 2, v_mvarId_4071_);
    crate::leanh::lean_closure_set(v___f_4081_, 3, v_userName_4073_);
    crate::leanh::lean_closure_set(v___f_4081_, 4, v_val_4075_);
    v___x_4082_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_4071_,
        v___f_4081_,
        v_a_4076_,
        v_a_4077_,
        v_a_4078_,
        v_a_4079_,
    );
    return v___x_4082_;
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27___boxed(
    mut v_mvarId_4083_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4084_: *mut crate::leanh::LeanObject,
    mut v_userName_4085_: *mut crate::leanh::LeanObject,
    mut v_type_4086_: *mut crate::leanh::LeanObject,
    mut v_val_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
    mut v_a_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v_a_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4093_ = l_Lean_MVarId_assertAfter_x27(
        v_mvarId_4083_,
        v_fvarId_4084_,
        v_userName_4085_,
        v_type_4086_,
        v_val_4087_,
        v_a_4088_,
        v_a_4089_,
        v_a_4090_,
        v_a_4091_,
    );
    crate::leanh::lean_dec(v_a_4091_);
    crate::leanh::lean_dec_ref(v_a_4090_);
    crate::leanh::lean_dec(v_a_4089_);
    crate::leanh::lean_dec_ref(v_a_4088_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
    mut v_mvarId_4094_: *mut crate::leanh::LeanObject,
    mut v_f_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4098_ = lean_st_ref_take(v___y_4096_);
                v_mctx_4099_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                v_cache_4100_ = crate::leanh::lean_ctor_get(v___x_4098_, 1);
                v_zetaDeltaFVarIds_4101_ = crate::leanh::lean_ctor_get(v___x_4098_, 2);
                v_postponed_4102_ = crate::leanh::lean_ctor_get(v___x_4098_, 3);
                v_diag_4103_ = crate::leanh::lean_ctor_get(v___x_4098_, 4);
                v_isSharedCheck_4114_ = (!crate::leanh::lean_is_exclusive(v___x_4098_)) as u8;
                if v_isSharedCheck_4114_ == 0 {
                    v___x_4105_ = v___x_4098_;
                    v_isShared_4106_ = v_isSharedCheck_4114_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4103_);
                    crate::leanh::lean_inc(v_postponed_4102_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4101_);
                    crate::leanh::lean_inc(v_cache_4100_);
                    crate::leanh::lean_inc(v_mctx_4099_);
                    crate::leanh::lean_dec(v___x_4098_);
                    v___x_4105_ = crate::leanh::lean_box(0);
                    v_isShared_4106_ = v_isSharedCheck_4114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4107_ = l_Lean_MetavarContext_modifyExprMVarLCtx(
                    v_mctx_4099_,
                    v_mvarId_4094_,
                    v_f_4095_,
                );
                if v_isShared_4106_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4105_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_cache_4100_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4113_,
                        2,
                        v_zetaDeltaFVarIds_4101_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 3, v_postponed_4102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_diag_4103_);
                    v___x_4109_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4110_ = lean_st_ref_set(v___y_4096_, v___x_4109_);
                v___x_4111_ = crate::leanh::lean_box(0);
                v___x_4112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(
    mut v_mvarId_4115_: *mut crate::leanh::LeanObject,
    mut v_f_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
        v_mvarId_4115_,
        v_f_4116_,
        v___y_4117_,
    );
    crate::leanh::lean_dec(v___y_4117_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(
    mut v_mvarId_4120_: *mut crate::leanh::LeanObject,
    mut v_f_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
        v_mvarId_4120_,
        v_f_4121_,
        v___y_4123_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(
    mut v_mvarId_4128_: *mut crate::leanh::LeanObject,
    mut v_f_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4135_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(
        v_mvarId_4128_,
        v_f_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
    );
    crate::leanh::lean_dec(v___y_4133_);
    crate::leanh::lean_dec_ref(v___y_4132_);
    crate::leanh::lean_dec(v___y_4131_);
    crate::leanh::lean_dec_ref(v___y_4130_);
    return v_res_4135_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
    mut v_upperBound_4136_: *mut crate::leanh::LeanObject,
    mut v_hs_4137_: *mut crate::leanh::LeanObject,
    mut v_fst_4138_: *mut crate::leanh::LeanObject,
    mut v___x_4139_: *mut crate::leanh::LeanObject,
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_b_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4149_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: u8 = 0;
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4147_ = lean_nat_dec_lt(v_a_4140_, v_upperBound_4136_);
                if v___x_4147_ == 0 {
                    crate::leanh::lean_dec(v_a_4140_);
                    return v_b_4141_;
                } else {
                    v___x_4148_ = lean_array_fget_borrowed(v_hs_4137_, v_a_4140_);
                    v_kind_4149_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4148_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v___x_4154_ = 0;
                    v___x_4155_ = l_Lean_instDecidableEqLocalDeclKind(v_kind_4149_, v___x_4154_);
                    if v___x_4155_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_4156_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4157_ = lean_nat_dec_eq(v___x_4139_, v___x_4156_);
                        if v___x_4157_ == 0 {
                            v_a_4143_ = v_b_4141_;
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4144_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4145_ = lean_nat_add(v_a_4140_, v___x_4144_);
                crate::leanh::lean_dec(v_a_4140_);
                v_a_4140_ = v___x_4145_;
                v_b_4141_ = v_a_4143_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4151_ = crate::leanh::lean_box(0);
                v___x_4152_ = lean_array_get_borrowed(v___x_4151_, v_fst_4138_, v_a_4140_);
                crate::leanh::lean_inc(v___x_4152_);
                v___x_4153_ = l_Lean_LocalContext_setKind(v_b_4141_, v___x_4152_, v_kind_4149_);
                v_a_4143_ = v___x_4153_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(
    mut v_upperBound_4158_: *mut crate::leanh::LeanObject,
    mut v_hs_4159_: *mut crate::leanh::LeanObject,
    mut v_fst_4160_: *mut crate::leanh::LeanObject,
    mut v___x_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_b_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4164_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
            v_upperBound_4158_,
            v_hs_4159_,
            v_fst_4160_,
            v___x_4161_,
            v_a_4162_,
            v_b_4163_,
        );
    crate::leanh::lean_dec(v___x_4161_);
    crate::leanh::lean_dec_ref(v_fst_4160_);
    crate::leanh::lean_dec_ref(v_hs_4159_);
    crate::leanh::lean_dec(v_upperBound_4158_);
    return v_res_4164_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__0(
    mut v___x_4165_: *mut crate::leanh::LeanObject,
    mut v_hs_4166_: *mut crate::leanh::LeanObject,
    mut v_fst_4167_: *mut crate::leanh::LeanObject,
    mut v___x_4168_: *mut crate::leanh::LeanObject,
    mut v_lctx_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4170_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
            v___x_4165_,
            v_hs_4166_,
            v_fst_4167_,
            v___x_4165_,
            v___x_4168_,
            v_lctx_4169_,
        );
    return v___x_4170_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__0___boxed(
    mut v___x_4171_: *mut crate::leanh::LeanObject,
    mut v_hs_4172_: *mut crate::leanh::LeanObject,
    mut v_fst_4173_: *mut crate::leanh::LeanObject,
    mut v___x_4174_: *mut crate::leanh::LeanObject,
    mut v_lctx_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4176_ = l_Lean_MVarId_assertHypotheses___lam__0(
        v___x_4171_,
        v_hs_4172_,
        v_fst_4173_,
        v___x_4174_,
        v_lctx_4175_,
    );
    crate::leanh::lean_dec_ref(v_fst_4173_);
    crate::leanh::lean_dec_ref(v_hs_4172_);
    crate::leanh::lean_dec(v___x_4171_);
    return v_res_4176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(
    mut v_as_4177_: *mut crate::leanh::LeanObject,
    mut v_i_4178_: usize,
    mut v_stop_4179_: usize,
    mut v_b_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4187_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4181_ = lean_usize_dec_eq(v_i_4178_, v_stop_4179_);
                if v___x_4181_ == 0 {
                    v___x_4182_ = 1usize;
                    v___x_4183_ = lean_usize_sub(v_i_4178_, v___x_4182_);
                    v___x_4184_ = lean_array_uget_borrowed(v_as_4177_, v___x_4183_);
                    v_userName_4185_ = crate::leanh::lean_ctor_get(v___x_4184_, 0);
                    v_type_4186_ = crate::leanh::lean_ctor_get(v___x_4184_, 1);
                    v_binderInfo_4187_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4184_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_4186_);
                    crate::leanh::lean_inc(v_userName_4185_);
                    v___x_4188_ = l_Lean_Expr_forallE___override(
                        v_userName_4185_,
                        v_type_4186_,
                        v_b_4180_,
                        v_binderInfo_4187_,
                    );
                    v_i_4178_ = v___x_4183_;
                    v_b_4180_ = v___x_4188_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4180_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(
    mut v_as_4190_: *mut crate::leanh::LeanObject,
    mut v_i_4191_: *mut crate::leanh::LeanObject,
    mut v_stop_4192_: *mut crate::leanh::LeanObject,
    mut v_b_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4194_: usize = 0;
    let mut v_stop_boxed_4195_: usize = 0;
    let mut v_res_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4194_ = crate::leanh::lean_unbox_usize(v_i_4191_);
    crate::leanh::lean_dec(v_i_4191_);
    v_stop_boxed_4195_ = crate::leanh::lean_unbox_usize(v_stop_4192_);
    crate::leanh::lean_dec(v_stop_4192_);
    v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_4190_, v_i_boxed_4194_, v_stop_boxed_4195_, v_b_4193_);
    crate::leanh::lean_dec_ref(v_as_4190_);
    return v_res_4196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(
    mut v_as_4197_: *mut crate::leanh::LeanObject,
    mut v_i_4198_: usize,
    mut v_stop_4199_: usize,
    mut v_b_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: usize = 0;
    let mut v___x_4206_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4201_ = lean_usize_dec_eq(v_i_4198_, v_stop_4199_);
                if v___x_4201_ == 0 {
                    v___x_4202_ = lean_array_uget_borrowed(v_as_4197_, v_i_4198_);
                    v_value_4203_ = crate::leanh::lean_ctor_get(v___x_4202_, 2);
                    crate::leanh::lean_inc_ref(v_value_4203_);
                    v___x_4204_ = l_Lean_Expr_app___override(v_b_4200_, v_value_4203_);
                    v___x_4205_ = 1usize;
                    v___x_4206_ = lean_usize_add(v_i_4198_, v___x_4205_);
                    v_i_4198_ = v___x_4206_;
                    v_b_4200_ = v___x_4204_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4200_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(
    mut v_as_4208_: *mut crate::leanh::LeanObject,
    mut v_i_4209_: *mut crate::leanh::LeanObject,
    mut v_stop_4210_: *mut crate::leanh::LeanObject,
    mut v_b_4211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4212_: usize = 0;
    let mut v_stop_boxed_4213_: usize = 0;
    let mut v_res_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4212_ = crate::leanh::lean_unbox_usize(v_i_4209_);
    crate::leanh::lean_dec(v_i_4209_);
    v_stop_boxed_4213_ = crate::leanh::lean_unbox_usize(v_stop_4210_);
    crate::leanh::lean_dec(v_stop_4210_);
    v_res_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_4208_, v_i_boxed_4212_, v_stop_boxed_4213_, v_b_4211_);
    crate::leanh::lean_dec_ref(v_as_4208_);
    return v_res_4214_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__1(
    mut v_mvarId_4215_: *mut crate::leanh::LeanObject,
    mut v___x_4216_: *mut crate::leanh::LeanObject,
    mut v___x_4217_: *mut crate::leanh::LeanObject,
    mut v___x_4218_: u8,
    mut v_hs_4219_: *mut crate::leanh::LeanObject,
    mut v___x_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_unused_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: usize = 0;
    let mut v___x_4259_: usize = 0;
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: usize = 0;
    let mut v___x_4262_: usize = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4267_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4271_: u8 = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: usize = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4215_);
                v___x_4247_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4215_,
                    v___x_4216_,
                    v___y_4221_,
                    v___y_4222_,
                    v___y_4223_,
                    v___y_4224_,
                );
                if crate::leanh::lean_obj_tag(v___x_4247_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4247_, 1);
                    crate::leanh::lean_inc(v_mvarId_4215_);
                    v___x_4248_ = l_Lean_MVarId_getTag(
                        v_mvarId_4215_,
                        v___y_4221_,
                        v___y_4222_,
                        v___y_4223_,
                        v___y_4224_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4248_) == 0 {
                        v_a_4249_ = crate::leanh::lean_ctor_get(v___x_4248_, 0);
                        crate::leanh::lean_inc(v_a_4249_);
                        crate::leanh::lean_dec_ref_known(v___x_4248_, 1);
                        crate::leanh::lean_inc(v_mvarId_4215_);
                        v___x_4250_ = l_Lean_MVarId_getType(
                            v_mvarId_4215_,
                            v___y_4221_,
                            v___y_4222_,
                            v___y_4223_,
                            v___y_4224_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4250_) == 0 {
                            v_a_4251_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                            crate::leanh::lean_inc(v_a_4251_);
                            crate::leanh::lean_dec_ref_known(v___x_4250_, 1);
                            v___x_4272_ = lean_nat_dec_lt(v___x_4220_, v___x_4217_);
                            if v___x_4272_ == 0 {
                                v___y_4253_ = v_a_4251_;
                                state = 4;
                                continue;
                            } else {
                                v___x_4273_ = lean_usize_of_nat(v___x_4217_);
                                v___x_4274_ = 0usize;
                                v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_hs_4219_, v___x_4273_, v___x_4274_, v_a_4251_);
                                v___y_4253_ = v___x_4275_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4249_);
                            crate::leanh::lean_dec(v___x_4220_);
                            crate::leanh::lean_dec_ref(v_hs_4219_);
                            crate::leanh::lean_dec(v___x_4217_);
                            crate::leanh::lean_dec(v_mvarId_4215_);
                            v_a_4276_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                            v_isSharedCheck_4283_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                            if v_isSharedCheck_4283_ == 0 {
                                v___x_4278_ = v___x_4250_;
                                v_isShared_4279_ = v_isSharedCheck_4283_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4276_);
                                crate::leanh::lean_dec(v___x_4250_);
                                v___x_4278_ = crate::leanh::lean_box(0);
                                v_isShared_4279_ = v_isSharedCheck_4283_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4220_);
                        crate::leanh::lean_dec_ref(v_hs_4219_);
                        crate::leanh::lean_dec(v___x_4217_);
                        crate::leanh::lean_dec(v_mvarId_4215_);
                        v_a_4284_ = crate::leanh::lean_ctor_get(v___x_4248_, 0);
                        v_isSharedCheck_4291_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4248_)) as u8;
                        if v_isSharedCheck_4291_ == 0 {
                            v___x_4286_ = v___x_4248_;
                            v_isShared_4287_ = v_isSharedCheck_4291_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4284_);
                            crate::leanh::lean_dec(v___x_4248_);
                            v___x_4286_ = crate::leanh::lean_box(0);
                            v_isShared_4287_ = v_isSharedCheck_4291_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4220_);
                    crate::leanh::lean_dec_ref(v_hs_4219_);
                    crate::leanh::lean_dec(v___x_4217_);
                    crate::leanh::lean_dec(v_mvarId_4215_);
                    v_a_4292_ = crate::leanh::lean_ctor_get(v___x_4247_, 0);
                    v_isSharedCheck_4299_ = (!crate::leanh::lean_is_exclusive(v___x_4247_)) as u8;
                    if v_isSharedCheck_4299_ == 0 {
                        v___x_4294_ = v___x_4247_;
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4292_);
                        crate::leanh::lean_dec(v___x_4247_);
                        v___x_4294_ = crate::leanh::lean_box(0);
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4229_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
                    v_mvarId_4215_,
                    v___y_4228_,
                    v___y_4222_,
                );
                crate::leanh::lean_dec_ref(v___x_4229_);
                v___x_4230_ = l_Lean_Expr_mvarId_x21(v___y_4227_);
                crate::leanh::lean_dec_ref(v___y_4227_);
                v___x_4231_ = crate::leanh::lean_box(0);
                v___x_4232_ = 1;
                crate::leanh::lean_inc(v___x_4217_);
                v___x_4233_ = l_Lean_Meta_introNCore(
                    v___x_4230_,
                    v___x_4217_,
                    v___x_4231_,
                    v___x_4218_,
                    v___x_4232_,
                    v___y_4221_,
                    v___y_4222_,
                    v___y_4223_,
                    v___y_4224_,
                );
                if crate::leanh::lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
                    crate::leanh::lean_inc(v_a_4234_);
                    crate::leanh::lean_dec_ref_known(v___x_4233_, 1);
                    v_fst_4235_ = crate::leanh::lean_ctor_get(v_a_4234_, 0);
                    v_snd_4236_ = crate::leanh::lean_ctor_get(v_a_4234_, 1);
                    crate::leanh::lean_inc(v_fst_4235_);
                    v___f_4237_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_assertHypotheses___lam__0___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_4237_, 0, v___x_4217_);
                    crate::leanh::lean_closure_set(v___f_4237_, 1, v_hs_4219_);
                    crate::leanh::lean_closure_set(v___f_4237_, 2, v_fst_4235_);
                    crate::leanh::lean_closure_set(v___f_4237_, 3, v___x_4220_);
                    crate::leanh::lean_inc(v_snd_4236_);
                    v___x_4238_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_4236_, v___f_4237_, v___y_4222_);
                    v_isSharedCheck_4245_ = (!crate::leanh::lean_is_exclusive(v___x_4238_)) as u8;
                    if v_isSharedCheck_4245_ == 0 {
                        v_unused_4246_ = crate::leanh::lean_ctor_get(v___x_4238_, 0);
                        crate::leanh::lean_dec(v_unused_4246_);
                        v___x_4240_ = v___x_4238_;
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4238_);
                        v___x_4240_ = crate::leanh::lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4220_);
                    crate::leanh::lean_dec_ref(v_hs_4219_);
                    crate::leanh::lean_dec(v___x_4217_);
                    return v___x_4233_;
                }
            }
            2 => {
                if v_isShared_4241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4240_, 0, v_a_4234_);
                    v___x_4243_ = v___x_4240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4234_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4243_;
            }
            4 => {
                v___x_4254_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___y_4253_,
                    v_a_4249_,
                    v___y_4221_,
                    v___y_4222_,
                    v___y_4223_,
                    v___y_4224_,
                );
                if crate::leanh::lean_obj_tag(v___x_4254_) == 0 {
                    v_a_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    crate::leanh::lean_inc(v_a_4255_);
                    crate::leanh::lean_dec_ref_known(v___x_4254_, 1);
                    v___x_4256_ = lean_nat_dec_lt(v___x_4220_, v___x_4217_);
                    if v___x_4256_ == 0 {
                        crate::leanh::lean_inc(v_a_4255_);
                        v___y_4227_ = v_a_4255_;
                        v___y_4228_ = v_a_4255_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4257_ = lean_nat_dec_le(v___x_4217_, v___x_4217_);
                        if v___x_4257_ == 0 {
                            if v___x_4256_ == 0 {
                                crate::leanh::lean_inc(v_a_4255_);
                                v___y_4227_ = v_a_4255_;
                                v___y_4228_ = v_a_4255_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4258_ = 0usize;
                                v___x_4259_ = lean_usize_of_nat(v___x_4217_);
                                crate::leanh::lean_inc(v_a_4255_);
                                v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_4219_, v___x_4258_, v___x_4259_, v_a_4255_);
                                v___y_4227_ = v_a_4255_;
                                v___y_4228_ = v___x_4260_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4261_ = 0usize;
                            v___x_4262_ = lean_usize_of_nat(v___x_4217_);
                            crate::leanh::lean_inc(v_a_4255_);
                            v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_4219_, v___x_4261_, v___x_4262_, v_a_4255_);
                            v___y_4227_ = v_a_4255_;
                            v___y_4228_ = v___x_4263_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4220_);
                    crate::leanh::lean_dec_ref(v_hs_4219_);
                    crate::leanh::lean_dec(v___x_4217_);
                    crate::leanh::lean_dec(v_mvarId_4215_);
                    v_a_4264_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    v_isSharedCheck_4271_ = (!crate::leanh::lean_is_exclusive(v___x_4254_)) as u8;
                    if v_isSharedCheck_4271_ == 0 {
                        v___x_4266_ = v___x_4254_;
                        v_isShared_4267_ = v_isSharedCheck_4271_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4264_);
                        crate::leanh::lean_dec(v___x_4254_);
                        v___x_4266_ = crate::leanh::lean_box(0);
                        v_isShared_4267_ = v_isSharedCheck_4271_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4267_ == 0 {
                    v___x_4269_ = v___x_4266_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
                    v___x_4269_ = v_reuseFailAlloc_4270_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4269_;
            }
            7 => {
                if v_isShared_4279_ == 0 {
                    v___x_4281_ = v___x_4278_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4281_;
            }
            9 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4289_;
            }
            11 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__1___boxed(
    mut v_mvarId_4300_: *mut crate::leanh::LeanObject,
    mut v___x_4301_: *mut crate::leanh::LeanObject,
    mut v___x_4302_: *mut crate::leanh::LeanObject,
    mut v___x_4303_: *mut crate::leanh::LeanObject,
    mut v_hs_4304_: *mut crate::leanh::LeanObject,
    mut v___x_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3359__boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3359__boxed_4311_ = (crate::leanh::lean_unbox(v___x_4303_) as u8);
    v_res_4312_ = l_Lean_MVarId_assertHypotheses___lam__1(
        v_mvarId_4300_,
        v___x_4301_,
        v___x_4302_,
        v___x_3359__boxed_4311_,
        v_hs_4304_,
        v___x_4305_,
        v___y_4306_,
        v___y_4307_,
        v___y_4308_,
        v___y_4309_,
    );
    crate::leanh::lean_dec(v___y_4309_);
    crate::leanh::lean_dec_ref(v___y_4308_);
    crate::leanh::lean_dec(v___y_4307_);
    crate::leanh::lean_dec_ref(v___y_4306_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses(
    mut v_mvarId_4318_: *mut crate::leanh::LeanObject,
    mut v_hs_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: u8 = 0;
    v___x_4325_ = lean_array_get_size(v_hs_4319_);
    v___x_4326_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4327_ = lean_nat_dec_eq(v___x_4325_, v___x_4326_);
    if v___x_4327_ == 0 {
        let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4328_ = l_Lean_MVarId_assertHypotheses___closed__1;
        v___x_4329_ = crate::leanh::lean_box((v___x_4327_) as usize);
        crate::leanh::lean_inc(v_mvarId_4318_);
        v___f_4330_ = crate::leanh::lean_alloc_closure(
            l_Lean_MVarId_assertHypotheses___lam__1___boxed as *mut core::ffi::c_void,
            11,
            6,
        );
        crate::leanh::lean_closure_set(v___f_4330_, 0, v_mvarId_4318_);
        crate::leanh::lean_closure_set(v___f_4330_, 1, v___x_4328_);
        crate::leanh::lean_closure_set(v___f_4330_, 2, v___x_4325_);
        crate::leanh::lean_closure_set(v___f_4330_, 3, v___x_4329_);
        crate::leanh::lean_closure_set(v___f_4330_, 4, v_hs_4319_);
        crate::leanh::lean_closure_set(v___f_4330_, 5, v___x_4326_);
        v___x_4331_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
            v_mvarId_4318_,
            v___f_4330_,
            v_a_4320_,
            v_a_4321_,
            v_a_4322_,
            v_a_4323_,
        );
        return v___x_4331_;
    } else {
        let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_hs_4319_);
        v___x_4332_ = l_Lean_MVarId_assertHypotheses___closed__2;
        v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4333_, 0, v___x_4332_);
        crate::leanh::lean_ctor_set(v___x_4333_, 1, v_mvarId_4318_);
        v___x_4334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4333_);
        return v___x_4334_;
    }
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___boxed(
    mut v_mvarId_4335_: *mut crate::leanh::LeanObject,
    mut v_hs_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_MVarId_assertHypotheses(
        v_mvarId_4335_,
        v_hs_4336_,
        v_a_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
    );
    crate::leanh::lean_dec(v_a_4340_);
    crate::leanh::lean_dec_ref(v_a_4339_);
    crate::leanh::lean_dec(v_a_4338_);
    crate::leanh::lean_dec_ref(v_a_4337_);
    return v_res_4342_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(
    mut v_upperBound_4343_: *mut crate::leanh::LeanObject,
    mut v_hs_4344_: *mut crate::leanh::LeanObject,
    mut v_fst_4345_: *mut crate::leanh::LeanObject,
    mut v___x_4346_: *mut crate::leanh::LeanObject,
    mut v_inst_4347_: *mut crate::leanh::LeanObject,
    mut v_R_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_b_4350_: *mut crate::leanh::LeanObject,
    mut v_c_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
            v_upperBound_4343_,
            v_hs_4344_,
            v_fst_4345_,
            v___x_4346_,
            v_a_4349_,
            v_b_4350_,
        );
    return v___x_4352_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(
    mut v_upperBound_4353_: *mut crate::leanh::LeanObject,
    mut v_hs_4354_: *mut crate::leanh::LeanObject,
    mut v_fst_4355_: *mut crate::leanh::LeanObject,
    mut v___x_4356_: *mut crate::leanh::LeanObject,
    mut v_inst_4357_: *mut crate::leanh::LeanObject,
    mut v_R_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_b_4360_: *mut crate::leanh::LeanObject,
    mut v_c_4361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4362_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(
        v_upperBound_4353_,
        v_hs_4354_,
        v_fst_4355_,
        v___x_4356_,
        v_inst_4357_,
        v_R_4358_,
        v_a_4359_,
        v_b_4360_,
        v_c_4361_,
    );
    crate::leanh::lean_dec(v___x_4356_);
    crate::leanh::lean_dec_ref(v_fst_4355_);
    crate::leanh::lean_dec_ref(v_hs_4354_);
    crate::leanh::lean_dec(v_upperBound_4353_);
    return v_res_4362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Assert(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Assert(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Assert(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Assert(builtin);
}
