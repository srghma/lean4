// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Revert Lean.Elab.InfoTree.Main Lean.Util.ForEachExpr Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_assert___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_MVarId_assert___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assert___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_assert___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_assert___closed__0_value) as *mut LeanObject,
        6255460451893900049 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_assert___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assert___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_define___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_MVarId_define___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_define___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_define___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_define___closed__0_value) as *mut LeanObject,
        12110259722422313427 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_define___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_define___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertExt___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_MVarId_assertExt___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertExt___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_assertExt___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertExt___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_assertExt___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_assertExt___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_assertAfter___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_MVarId_assertAfter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertAfter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__0_value) as *mut LeanObject,
        6688911828405300775 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_assertAfter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertAfter___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_MVarId_assertHypotheses___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__0_value) as *mut LeanObject,
        16050730560474456637 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_assertHypotheses___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_assertHypotheses___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_MVarId_assertHypotheses___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assertHypotheses___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
    mut v_mvarId_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
    mut v___y_2185_: *mut LeanObject,
    mut v___y_2186_: *mut LeanObject,
    mut v___y_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_a_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2189_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2182_,
                    v_x_2183_,
                    v___y_2184_,
                    v___y_2185_,
                    v___y_2186_,
                    v___y_2187_,
                );
                if lean_obj_tag(v___x_2189_) == 0 {
                    v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
                    v_isSharedCheck_2197_ = (!lean_is_exclusive(v___x_2189_)) as u8;
                    if v_isSharedCheck_2197_ == 0 {
                        v___x_2192_ = v___x_2189_;
                        v_isShared_2193_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2190_);
                        lean_dec(v___x_2189_);
                        v___x_2192_ = lean_box(0);
                        v_isShared_2193_ = v_isSharedCheck_2197_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2198_ = lean_ctor_get(v___x_2189_, 0);
                    v_isSharedCheck_2205_ = (!lean_is_exclusive(v___x_2189_)) as u8;
                    if v_isSharedCheck_2205_ == 0 {
                        v___x_2200_ = v___x_2189_;
                        v_isShared_2201_ = v_isSharedCheck_2205_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2198_);
                        lean_dec(v___x_2189_);
                        v___x_2200_ = lean_box(0);
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
                    v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
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
                    v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
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
    mut v_mvarId_2206_: *mut LeanObject,
    mut v_x_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2213_: *mut LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(
        v_mvarId_2206_,
        v_x_2207_,
        v___y_2208_,
        v___y_2209_,
        v___y_2210_,
        v___y_2211_,
    );
    lean_dec(v___y_2211_);
    lean_dec_ref(v___y_2210_);
    lean_dec(v___y_2209_);
    lean_dec_ref(v___y_2208_);
    return v_res_2213_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(
    mut v_00_u03b1_2214_: *mut LeanObject,
    mut v_mvarId_2215_: *mut LeanObject,
    mut v_x_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2223_: *mut LeanObject,
    mut v_mvarId_2224_: *mut LeanObject,
    mut v_x_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(
        v_00_u03b1_2223_,
        v_mvarId_2224_,
        v_x_2225_,
        v___y_2226_,
        v___y_2227_,
        v___y_2228_,
        v___y_2229_,
    );
    lean_dec(v___y_2229_);
    lean_dec_ref(v___y_2228_);
    lean_dec(v___y_2227_);
    lean_dec_ref(v___y_2226_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_2232_: *mut LeanObject,
    mut v_x_2233_: *mut LeanObject,
    mut v_x_2234_: *mut LeanObject,
    mut v_x_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2236_ = lean_ctor_get(v_x_2232_, 0);
                v_vs_2237_ = lean_ctor_get(v_x_2232_, 1);
                v_isSharedCheck_2261_ = (!lean_is_exclusive(v_x_2232_)) as u8;
                if v_isSharedCheck_2261_ == 0 {
                    v___x_2239_ = v_x_2232_;
                    v_isShared_2240_ = v_isSharedCheck_2261_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2237_);
                    lean_inc(v_ks_2236_);
                    lean_dec(v_x_2232_);
                    v___x_2239_ = lean_box(0);
                    v_isShared_2240_ = v_isSharedCheck_2261_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2241_ = lean_array_get_size(v_ks_2236_);
                v___x_2242_ = lean_nat_dec_lt(v_x_2233_, v___x_2241_);
                if v___x_2242_ == 0 {
                    lean_dec(v_x_2233_);
                    v___x_2243_ = lean_array_push(v_ks_2236_, v_x_2234_);
                    v___x_2244_ = lean_array_push(v_vs_2237_, v_x_2235_);
                    if v_isShared_2240_ == 0 {
                        lean_ctor_set(v___x_2239_, 1, v___x_2244_);
                        lean_ctor_set(v___x_2239_, 0, v___x_2243_);
                        v___x_2246_ = v___x_2239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
                        lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2244_);
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
                            v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_ks_2236_);
                            lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_vs_2237_);
                            v___x_2251_ = v_reuseFailAlloc_2255_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2256_ = lean_array_fset(v_ks_2236_, v_x_2233_, v_x_2234_);
                        v___x_2257_ = lean_array_fset(v_vs_2237_, v_x_2233_, v_x_2235_);
                        lean_dec(v_x_2233_);
                        if v_isShared_2240_ == 0 {
                            lean_ctor_set(v___x_2239_, 1, v___x_2257_);
                            lean_ctor_set(v___x_2239_, 0, v___x_2256_);
                            v___x_2259_ = v___x_2239_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2256_);
                            lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2257_);
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
                v___x_2252_ = lean_unsigned_to_nat(1);
                v___x_2253_ = lean_nat_add(v_x_2233_, v___x_2252_);
                lean_dec(v_x_2233_);
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
    mut v_n_2262_: *mut LeanObject,
    mut v_k_2263_: *mut LeanObject,
    mut v_v_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    v___x_2265_ = lean_unsigned_to_nat(0);
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
    v___x_2271_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_2272_ = lean_usize_sub(v___x_2271_, v___x_2270_);
    return v___x_2272_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2273_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(
    mut v_x_2274_: *mut LeanObject,
    mut v_x_2275_: usize,
    mut v_x_2276_: usize,
    mut v_x_2277_: *mut LeanObject,
    mut v_x_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2283_: usize = 0;
    let mut v_j_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v_v_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_node_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_unused_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: u8 = 0;
    let mut v_ks_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: usize = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v_reuseFailAlloc_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2274_) == 0 {
                    v_es_2279_ = lean_ctor_get(v_x_2274_, 0);
                    v___x_2280_ = 5usize;
                    v___x_2281_ = 1usize;
                    v___x_2282_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2283_ = lean_usize_land(v_x_2275_, v___x_2282_);
                    v_j_2284_ = lean_usize_to_nat(v___x_2283_);
                    v___x_2285_ = lean_array_get_size(v_es_2279_);
                    v___x_2286_ = lean_nat_dec_lt(v_j_2284_, v___x_2285_);
                    if v___x_2286_ == 0 {
                        lean_dec(v_j_2284_);
                        lean_dec(v_x_2278_);
                        lean_dec(v_x_2277_);
                        return v_x_2274_;
                    } else {
                        lean_inc_ref(v_es_2279_);
                        v_isSharedCheck_2323_ = (!lean_is_exclusive(v_x_2274_)) as u8;
                        if v_isSharedCheck_2323_ == 0 {
                            v_unused_2324_ = lean_ctor_get(v_x_2274_, 0);
                            lean_dec(v_unused_2324_);
                            v___x_2288_ = v_x_2274_;
                            v_isShared_2289_ = v_isSharedCheck_2323_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2274_);
                            v___x_2288_ = lean_box(0);
                            v_isShared_2289_ = v_isSharedCheck_2323_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2325_ = lean_ctor_get(v_x_2274_, 0);
                    v_vs_2326_ = lean_ctor_get(v_x_2274_, 1);
                    v_isSharedCheck_2346_ = (!lean_is_exclusive(v_x_2274_)) as u8;
                    if v_isSharedCheck_2346_ == 0 {
                        v___x_2328_ = v_x_2274_;
                        v_isShared_2329_ = v_isSharedCheck_2346_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2326_);
                        lean_inc(v_ks_2325_);
                        lean_dec(v_x_2274_);
                        v___x_2328_ = lean_box(0);
                        v_isShared_2329_ = v_isSharedCheck_2346_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2290_ = lean_array_fget(v_es_2279_, v_j_2284_);
                v___x_2291_ = lean_box(0);
                v_xs_x27_2292_ = lean_array_fset(v_es_2279_, v_j_2284_, v___x_2291_);
                match lean_obj_tag(v_v_2290_) {
                    0 => {
                        v_key_2299_ = lean_ctor_get(v_v_2290_, 0);
                        v_val_2300_ = lean_ctor_get(v_v_2290_, 1);
                        v_isSharedCheck_2310_ = (!lean_is_exclusive(v_v_2290_)) as u8;
                        if v_isSharedCheck_2310_ == 0 {
                            v___x_2302_ = v_v_2290_;
                            v_isShared_2303_ = v_isSharedCheck_2310_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2300_);
                            lean_inc(v_key_2299_);
                            lean_dec(v_v_2290_);
                            v___x_2302_ = lean_box(0);
                            v_isShared_2303_ = v_isSharedCheck_2310_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2311_ = lean_ctor_get(v_v_2290_, 0);
                        v_isSharedCheck_2321_ = (!lean_is_exclusive(v_v_2290_)) as u8;
                        if v_isSharedCheck_2321_ == 0 {
                            v___x_2313_ = v_v_2290_;
                            v_isShared_2314_ = v_isSharedCheck_2321_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2311_);
                            lean_dec(v_v_2290_);
                            v___x_2313_ = lean_box(0);
                            v_isShared_2314_ = v_isSharedCheck_2321_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2322_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2322_, 0, v_x_2277_);
                        lean_ctor_set(v___x_2322_, 1, v_x_2278_);
                        v___y_2294_ = v___x_2322_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2295_ = lean_array_fset(v_xs_x27_2292_, v_j_2284_, v___y_2294_);
                lean_dec(v_j_2284_);
                if v_isShared_2289_ == 0 {
                    lean_ctor_set(v___x_2288_, 0, v___x_2295_);
                    v___x_2297_ = v___x_2288_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
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
                    lean_del_object(v___x_2302_);
                    v___x_2305_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2299_,
                        v_val_2300_,
                        v_x_2277_,
                        v_x_2278_,
                    );
                    v___x_2306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2306_, 0, v___x_2305_);
                    v___y_2294_ = v___x_2306_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2300_);
                    lean_dec(v_key_2299_);
                    if v_isShared_2303_ == 0 {
                        lean_ctor_set(v___x_2302_, 1, v_x_2278_);
                        lean_ctor_set(v___x_2302_, 0, v_x_2277_);
                        v___x_2308_ = v___x_2302_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_x_2277_);
                        lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_x_2278_);
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
                    lean_ctor_set(v___x_2313_, 0, v___x_2317_);
                    v___x_2319_ = v___x_2313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
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
                    v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_ks_2325_);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_vs_2326_);
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
                    v___x_2343_ = lean_unsigned_to_nat(4);
                    v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
                    lean_dec(v___x_2342_);
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
                    v_ks_2335_ = lean_ctor_get(v_newNode_2332_, 0);
                    lean_inc_ref(v_ks_2335_);
                    v_vs_2336_ = lean_ctor_get(v_newNode_2332_, 1);
                    lean_inc_ref(v_vs_2336_);
                    lean_dec_ref(v_newNode_2332_);
                    v___x_2337_ = lean_unsigned_to_nat(0);
                    v___x_2338_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_2339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2276_, v_ks_2335_, v_vs_2336_, v___x_2337_, v___x_2338_);
                    lean_dec_ref(v_vs_2336_);
                    lean_dec_ref(v_ks_2335_);
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
    mut v_keys_2348_: *mut LeanObject,
    mut v_vals_2349_: *mut LeanObject,
    mut v_i_2350_: *mut LeanObject,
    mut v_entries_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u8 = 0;
    let mut v_k_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u64 = 0;
    let mut v_h_2357_: usize = 0;
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v_h_2363_: usize = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2352_ = lean_array_get_size(v_keys_2348_);
                v___x_2353_ = lean_nat_dec_lt(v_i_2350_, v___x_2352_);
                if v___x_2353_ == 0 {
                    lean_dec(v_i_2350_);
                    return v_entries_2351_;
                } else {
                    v_k_2354_ = lean_array_fget_borrowed(v_keys_2348_, v_i_2350_);
                    v_v_2355_ = lean_array_fget_borrowed(v_vals_2349_, v_i_2350_);
                    v___x_2356_ = l_Lean_instHashableMVarId_hash(v_k_2354_);
                    v_h_2357_ = lean_uint64_to_usize(v___x_2356_);
                    v___x_2358_ = 5usize;
                    v___x_2359_ = lean_unsigned_to_nat(1);
                    v___x_2360_ = 1usize;
                    v___x_2361_ = lean_usize_sub(v_depth_2347_, v___x_2360_);
                    v___x_2362_ = lean_usize_mul(v___x_2358_, v___x_2361_);
                    v_h_2363_ = lean_usize_shift_right(v_h_2357_, v___x_2362_);
                    v___x_2364_ = lean_nat_add(v_i_2350_, v___x_2359_);
                    lean_dec(v_i_2350_);
                    lean_inc(v_v_2355_);
                    lean_inc(v_k_2354_);
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
    mut v_depth_2367_: *mut LeanObject,
    mut v_keys_2368_: *mut LeanObject,
    mut v_vals_2369_: *mut LeanObject,
    mut v_i_2370_: *mut LeanObject,
    mut v_entries_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2372_: usize = 0;
    let mut v_res_2373_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2372_ = lean_unbox_usize(v_depth_2367_);
    lean_dec(v_depth_2367_);
    v_res_2373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_2372_, v_keys_2368_, v_vals_2369_, v_i_2370_, v_entries_2371_);
    lean_dec_ref(v_vals_2369_);
    lean_dec_ref(v_keys_2368_);
    return v_res_2373_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_2374_: *mut LeanObject,
    mut v_x_2375_: *mut LeanObject,
    mut v_x_2376_: *mut LeanObject,
    mut v_x_2377_: *mut LeanObject,
    mut v_x_2378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1323__boxed_2379_: usize = 0;
    let mut v_x_1324__boxed_2380_: usize = 0;
    let mut v_res_2381_: *mut LeanObject = core::ptr::null_mut();
    v_x_1323__boxed_2379_ = lean_unbox_usize(v_x_2375_);
    lean_dec(v_x_2375_);
    v_x_1324__boxed_2380_ = lean_unbox_usize(v_x_2376_);
    lean_dec(v_x_2376_);
    v_res_2381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2374_, v_x_1323__boxed_2379_, v_x_1324__boxed_2380_, v_x_2377_, v_x_2378_);
    return v_res_2381_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(
    mut v_x_2382_: *mut LeanObject,
    mut v_x_2383_: *mut LeanObject,
    mut v_x_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2385_: u64 = 0;
    let mut v___x_2386_: usize = 0;
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    v___x_2385_ = l_Lean_instHashableMVarId_hash(v_x_2383_);
    v___x_2386_ = lean_uint64_to_usize(v___x_2385_);
    v___x_2387_ = 1usize;
    v___x_2388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2382_, v___x_2386_, v___x_2387_, v_x_2383_, v_x_2384_);
    return v___x_2388_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
    mut v_mvarId_2389_: *mut LeanObject,
    mut v_val_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v_depth_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2393_ = lean_st_ref_take(v___y_2391_);
                v_mctx_2394_ = lean_ctor_get(v___x_2393_, 0);
                v_cache_2395_ = lean_ctor_get(v___x_2393_, 1);
                v_zetaDeltaFVarIds_2396_ = lean_ctor_get(v___x_2393_, 2);
                v_postponed_2397_ = lean_ctor_get(v___x_2393_, 3);
                v_diag_2398_ = lean_ctor_get(v___x_2393_, 4);
                v_isSharedCheck_2426_ = (!lean_is_exclusive(v___x_2393_)) as u8;
                if v_isSharedCheck_2426_ == 0 {
                    v___x_2400_ = v___x_2393_;
                    v_isShared_2401_ = v_isSharedCheck_2426_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2398_);
                    lean_inc(v_postponed_2397_);
                    lean_inc(v_zetaDeltaFVarIds_2396_);
                    lean_inc(v_cache_2395_);
                    lean_inc(v_mctx_2394_);
                    lean_dec(v___x_2393_);
                    v___x_2400_ = lean_box(0);
                    v_isShared_2401_ = v_isSharedCheck_2426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2402_ = lean_ctor_get(v_mctx_2394_, 0);
                v_levelAssignDepth_2403_ = lean_ctor_get(v_mctx_2394_, 1);
                v_lmvarCounter_2404_ = lean_ctor_get(v_mctx_2394_, 2);
                v_mvarCounter_2405_ = lean_ctor_get(v_mctx_2394_, 3);
                v_lDecls_2406_ = lean_ctor_get(v_mctx_2394_, 4);
                v_decls_2407_ = lean_ctor_get(v_mctx_2394_, 5);
                v_userNames_2408_ = lean_ctor_get(v_mctx_2394_, 6);
                v_lAssignment_2409_ = lean_ctor_get(v_mctx_2394_, 7);
                v_eAssignment_2410_ = lean_ctor_get(v_mctx_2394_, 8);
                v_dAssignment_2411_ = lean_ctor_get(v_mctx_2394_, 9);
                v_isSharedCheck_2425_ = (!lean_is_exclusive(v_mctx_2394_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2413_ = v_mctx_2394_;
                    v_isShared_2414_ = v_isSharedCheck_2425_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_2411_);
                    lean_inc(v_eAssignment_2410_);
                    lean_inc(v_lAssignment_2409_);
                    lean_inc(v_userNames_2408_);
                    lean_inc(v_decls_2407_);
                    lean_inc(v_lDecls_2406_);
                    lean_inc(v_mvarCounter_2405_);
                    lean_inc(v_lmvarCounter_2404_);
                    lean_inc(v_levelAssignDepth_2403_);
                    lean_inc(v_depth_2402_);
                    lean_dec(v_mctx_2394_);
                    v___x_2413_ = lean_box(0);
                    v_isShared_2414_ = v_isSharedCheck_2425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_eAssignment_2410_, v_mvarId_2389_, v_val_2390_);
                if v_isShared_2414_ == 0 {
                    lean_ctor_set(v___x_2413_, 8, v___x_2415_);
                    v___x_2417_ = v___x_2413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_depth_2402_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_levelAssignDepth_2403_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_lmvarCounter_2404_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_mvarCounter_2405_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_lDecls_2406_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 5, v_decls_2407_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 6, v_userNames_2408_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 7, v_lAssignment_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 8, v___x_2415_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 9, v_dAssignment_2411_);
                    v___x_2417_ = v_reuseFailAlloc_2424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2401_ == 0 {
                    lean_ctor_set(v___x_2400_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2400_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_cache_2395_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_zetaDeltaFVarIds_2396_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_postponed_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_diag_2398_);
                    v___x_2419_ = v_reuseFailAlloc_2423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2420_ = lean_st_ref_set(v___y_2391_, v___x_2419_);
                v___x_2421_ = lean_box(0);
                v___x_2422_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2422_, 0, v___x_2421_);
                return v___x_2422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(
    mut v_mvarId_2427_: *mut LeanObject,
    mut v_val_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
        v_mvarId_2427_,
        v_val_2428_,
        v___y_2429_,
    );
    lean_dec(v___y_2429_);
    return v_res_2431_;
}
pub unsafe fn l_Lean_MVarId_assert___lam__0(
    mut v_mvarId_2432_: *mut LeanObject,
    mut v___x_2433_: *mut LeanObject,
    mut v_name_2434_: *mut LeanObject,
    mut v_type_2435_: *mut LeanObject,
    mut v_val_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
    mut v___y_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_unused_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2465_: u8 = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2469_: u8 = 0;
    let mut v_a_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v_a_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_a_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2432_);
                v___x_2442_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2432_,
                    v___x_2433_,
                    v___y_2437_,
                    v___y_2438_,
                    v___y_2439_,
                    v___y_2440_,
                );
                if lean_obj_tag(v___x_2442_) == 0 {
                    lean_dec_ref_known(v___x_2442_, 1);
                    lean_inc(v_mvarId_2432_);
                    v___x_2443_ = l_Lean_MVarId_getTag(
                        v_mvarId_2432_,
                        v___y_2437_,
                        v___y_2438_,
                        v___y_2439_,
                        v___y_2440_,
                    );
                    if lean_obj_tag(v___x_2443_) == 0 {
                        v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
                        lean_inc(v_a_2444_);
                        lean_dec_ref_known(v___x_2443_, 1);
                        lean_inc(v_mvarId_2432_);
                        v___x_2445_ = l_Lean_MVarId_getType(
                            v_mvarId_2432_,
                            v___y_2437_,
                            v___y_2438_,
                            v___y_2439_,
                            v___y_2440_,
                        );
                        if lean_obj_tag(v___x_2445_) == 0 {
                            v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
                            lean_inc(v_a_2446_);
                            lean_dec_ref_known(v___x_2445_, 1);
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
                            if lean_obj_tag(v___x_2449_) == 0 {
                                v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
                                lean_inc_n(v_a_2450_, 2);
                                lean_dec_ref_known(v___x_2449_, 1);
                                v___x_2451_ = l_Lean_Expr_app___override(v_a_2450_, v_val_2436_);
                                v___x_2452_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2432_, v___x_2451_, v___y_2438_);
                                v_isSharedCheck_2460_ = (!lean_is_exclusive(v___x_2452_)) as u8;
                                if v_isSharedCheck_2460_ == 0 {
                                    v_unused_2461_ = lean_ctor_get(v___x_2452_, 0);
                                    lean_dec(v_unused_2461_);
                                    v___x_2454_ = v___x_2452_;
                                    v_isShared_2455_ = v_isSharedCheck_2460_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_2452_);
                                    v___x_2454_ = lean_box(0);
                                    v_isShared_2455_ = v_isSharedCheck_2460_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_val_2436_);
                                lean_dec(v_mvarId_2432_);
                                v_a_2462_ = lean_ctor_get(v___x_2449_, 0);
                                v_isSharedCheck_2469_ = (!lean_is_exclusive(v___x_2449_)) as u8;
                                if v_isSharedCheck_2469_ == 0 {
                                    v___x_2464_ = v___x_2449_;
                                    v_isShared_2465_ = v_isSharedCheck_2469_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2462_);
                                    lean_dec(v___x_2449_);
                                    v___x_2464_ = lean_box(0);
                                    v_isShared_2465_ = v_isSharedCheck_2469_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2444_);
                            lean_dec_ref(v_val_2436_);
                            lean_dec_ref(v_type_2435_);
                            lean_dec(v_name_2434_);
                            lean_dec(v_mvarId_2432_);
                            v_a_2470_ = lean_ctor_get(v___x_2445_, 0);
                            v_isSharedCheck_2477_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                            if v_isSharedCheck_2477_ == 0 {
                                v___x_2472_ = v___x_2445_;
                                v_isShared_2473_ = v_isSharedCheck_2477_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2470_);
                                lean_dec(v___x_2445_);
                                v___x_2472_ = lean_box(0);
                                v_isShared_2473_ = v_isSharedCheck_2477_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_val_2436_);
                        lean_dec_ref(v_type_2435_);
                        lean_dec(v_name_2434_);
                        lean_dec(v_mvarId_2432_);
                        v_a_2478_ = lean_ctor_get(v___x_2443_, 0);
                        v_isSharedCheck_2485_ = (!lean_is_exclusive(v___x_2443_)) as u8;
                        if v_isSharedCheck_2485_ == 0 {
                            v___x_2480_ = v___x_2443_;
                            v_isShared_2481_ = v_isSharedCheck_2485_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2478_);
                            lean_dec(v___x_2443_);
                            v___x_2480_ = lean_box(0);
                            v_isShared_2481_ = v_isSharedCheck_2485_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_val_2436_);
                    lean_dec_ref(v_type_2435_);
                    lean_dec(v_name_2434_);
                    lean_dec(v_mvarId_2432_);
                    v_a_2486_ = lean_ctor_get(v___x_2442_, 0);
                    v_isSharedCheck_2493_ = (!lean_is_exclusive(v___x_2442_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2488_ = v___x_2442_;
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2486_);
                        lean_dec(v___x_2442_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2456_ = l_Lean_Expr_mvarId_x21(v_a_2450_);
                lean_dec(v_a_2450_);
                if v_isShared_2455_ == 0 {
                    lean_ctor_set(v___x_2454_, 0, v___x_2456_);
                    v___x_2458_ = v___x_2454_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
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
                    v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
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
                    v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
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
                    v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
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
                    v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
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
    mut v_mvarId_2494_: *mut LeanObject,
    mut v___x_2495_: *mut LeanObject,
    mut v_name_2496_: *mut LeanObject,
    mut v_type_2497_: *mut LeanObject,
    mut v_val_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2504_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2502_);
    lean_dec_ref(v___y_2501_);
    lean_dec(v___y_2500_);
    lean_dec_ref(v___y_2499_);
    return v_res_2504_;
}
pub unsafe fn l_Lean_MVarId_assert(
    mut v_mvarId_2508_: *mut LeanObject,
    mut v_name_2509_: *mut LeanObject,
    mut v_type_2510_: *mut LeanObject,
    mut v_val_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    v___x_2517_ = l_Lean_MVarId_assert___closed__1;
    lean_inc(v_mvarId_2508_);
    v___f_2518_ = lean_alloc_closure(
        l_Lean_MVarId_assert___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_2518_, 0, v_mvarId_2508_);
    lean_closure_set(v___f_2518_, 1, v___x_2517_);
    lean_closure_set(v___f_2518_, 2, v_name_2509_);
    lean_closure_set(v___f_2518_, 3, v_type_2510_);
    lean_closure_set(v___f_2518_, 4, v_val_2511_);
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
    mut v_mvarId_2520_: *mut LeanObject,
    mut v_name_2521_: *mut LeanObject,
    mut v_type_2522_: *mut LeanObject,
    mut v_val_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
    mut v_a_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2527_);
    lean_dec_ref(v_a_2526_);
    lean_dec(v_a_2525_);
    lean_dec_ref(v_a_2524_);
    return v_res_2529_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(
    mut v_mvarId_2530_: *mut LeanObject,
    mut v_val_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(
        v_mvarId_2530_,
        v_val_2531_,
        v___y_2533_,
    );
    return v___x_2537_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(
    mut v_mvarId_2538_: *mut LeanObject,
    mut v_val_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2545_: *mut LeanObject = core::ptr::null_mut();
    v_res_2545_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(
        v_mvarId_2538_,
        v_val_2539_,
        v___y_2540_,
        v___y_2541_,
        v___y_2542_,
        v___y_2543_,
    );
    lean_dec(v___y_2543_);
    lean_dec_ref(v___y_2542_);
    lean_dec(v___y_2541_);
    lean_dec_ref(v___y_2540_);
    return v_res_2545_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(
    mut v_00_u03b2_2546_: *mut LeanObject,
    mut v_x_2547_: *mut LeanObject,
    mut v_x_2548_: *mut LeanObject,
    mut v_x_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(v_x_2547_, v_x_2548_, v_x_2549_);
    return v___x_2550_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2551_: *mut LeanObject,
    mut v_x_2552_: *mut LeanObject,
    mut v_x_2553_: usize,
    mut v_x_2554_: usize,
    mut v_x_2555_: *mut LeanObject,
    mut v_x_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(v_x_2552_, v_x_2553_, v_x_2554_, v_x_2555_, v_x_2556_);
    return v___x_2557_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2558_: *mut LeanObject,
    mut v_x_2559_: *mut LeanObject,
    mut v_x_2560_: *mut LeanObject,
    mut v_x_2561_: *mut LeanObject,
    mut v_x_2562_: *mut LeanObject,
    mut v_x_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1711__boxed_2564_: usize = 0;
    let mut v_x_1712__boxed_2565_: usize = 0;
    let mut v_res_2566_: *mut LeanObject = core::ptr::null_mut();
    v_x_1711__boxed_2564_ = lean_unbox_usize(v_x_2560_);
    lean_dec(v_x_2560_);
    v_x_1712__boxed_2565_ = lean_unbox_usize(v_x_2561_);
    lean_dec(v_x_2561_);
    v_res_2566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(v_00_u03b2_2558_, v_x_2559_, v_x_1711__boxed_2564_, v_x_1712__boxed_2565_, v_x_2562_, v_x_2563_);
    return v_res_2566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_2567_: *mut LeanObject,
    mut v_n_2568_: *mut LeanObject,
    mut v_k_2569_: *mut LeanObject,
    mut v_v_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___x_2571_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(v_n_2568_, v_k_2569_, v_v_2570_);
    return v___x_2571_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_2572_: *mut LeanObject,
    mut v_depth_2573_: usize,
    mut v_keys_2574_: *mut LeanObject,
    mut v_vals_2575_: *mut LeanObject,
    mut v_heq_2576_: *mut LeanObject,
    mut v_i_2577_: *mut LeanObject,
    mut v_entries_2578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    v___x_2579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_2573_, v_keys_2574_, v_vals_2575_, v_i_2577_, v_entries_2578_);
    return v___x_2579_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_2580_: *mut LeanObject,
    mut v_depth_2581_: *mut LeanObject,
    mut v_keys_2582_: *mut LeanObject,
    mut v_vals_2583_: *mut LeanObject,
    mut v_heq_2584_: *mut LeanObject,
    mut v_i_2585_: *mut LeanObject,
    mut v_entries_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2587_ = lean_unbox_usize(v_depth_2581_);
    lean_dec(v_depth_2581_);
    v_res_2588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2580_, v_depth_boxed_2587_, v_keys_2582_, v_vals_2583_, v_heq_2584_, v_i_2585_, v_entries_2586_);
    lean_dec_ref(v_vals_2583_);
    lean_dec_ref(v_keys_2582_);
    return v_res_2588_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2589_: *mut LeanObject,
    mut v_x_2590_: *mut LeanObject,
    mut v_x_2591_: *mut LeanObject,
    mut v_x_2592_: *mut LeanObject,
    mut v_x_2593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2594_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_2590_, v_x_2591_, v_x_2592_, v_x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_Lean_MVarId_note(
    mut v_g_2595_: *mut LeanObject,
    mut v_h_2596_: *mut LeanObject,
    mut v_v_2597_: *mut LeanObject,
    mut v_t_x3f_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_a_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_val_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_x3f_2598_) == 0 {
                    lean_inc(v_a_2602_);
                    lean_inc_ref(v_a_2601_);
                    lean_inc(v_a_2600_);
                    lean_inc_ref(v_a_2599_);
                    lean_inc_ref(v_v_2597_);
                    v___x_2618_ =
                        lean_infer_type(v_v_2597_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
                    if lean_obj_tag(v___x_2618_) == 0 {
                        v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
                        lean_inc(v_a_2619_);
                        lean_dec_ref_known(v___x_2618_, 1);
                        v_a_2605_ = v_a_2619_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_v_2597_);
                        lean_dec(v_h_2596_);
                        lean_dec(v_g_2595_);
                        v_a_2620_ = lean_ctor_get(v___x_2618_, 0);
                        v_isSharedCheck_2627_ = (!lean_is_exclusive(v___x_2618_)) as u8;
                        if v_isSharedCheck_2627_ == 0 {
                            v___x_2622_ = v___x_2618_;
                            v_isShared_2623_ = v_isSharedCheck_2627_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2620_);
                            lean_dec(v___x_2618_);
                            v___x_2622_ = lean_box(0);
                            v_isShared_2623_ = v_isSharedCheck_2627_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_val_2628_ = lean_ctor_get(v_t_x3f_2598_, 0);
                    lean_inc(v_val_2628_);
                    lean_dec_ref_known(v_t_x3f_2598_, 1);
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
                if lean_obj_tag(v___x_2606_) == 0 {
                    v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
                    lean_inc(v_a_2607_);
                    lean_dec_ref_known(v___x_2606_, 1);
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
                    v_a_2610_ = lean_ctor_get(v___x_2606_, 0);
                    v_isSharedCheck_2617_ = (!lean_is_exclusive(v___x_2606_)) as u8;
                    if v_isSharedCheck_2617_ == 0 {
                        v___x_2612_ = v___x_2606_;
                        v_isShared_2613_ = v_isSharedCheck_2617_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2610_);
                        lean_dec(v___x_2606_);
                        v___x_2612_ = lean_box(0);
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
                    v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
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
                    v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
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
    mut v_g_2629_: *mut LeanObject,
    mut v_h_2630_: *mut LeanObject,
    mut v_v_2631_: *mut LeanObject,
    mut v_t_x3f_2632_: *mut LeanObject,
    mut v_a_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
    mut v_a_2635_: *mut LeanObject,
    mut v_a_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2636_);
    lean_dec_ref(v_a_2635_);
    lean_dec(v_a_2634_);
    lean_dec_ref(v_a_2633_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_MVarId_define___lam__0(
    mut v_mvarId_2639_: *mut LeanObject,
    mut v___x_2640_: *mut LeanObject,
    mut v_name_2641_: *mut LeanObject,
    mut v_type_2642_: *mut LeanObject,
    mut v_val_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
    mut v___y_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2661_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_unused_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_a_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2695_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2639_);
                v___x_2649_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2639_,
                    v___x_2640_,
                    v___y_2644_,
                    v___y_2645_,
                    v___y_2646_,
                    v___y_2647_,
                );
                if lean_obj_tag(v___x_2649_) == 0 {
                    lean_dec_ref_known(v___x_2649_, 1);
                    lean_inc(v_mvarId_2639_);
                    v___x_2650_ = l_Lean_MVarId_getTag(
                        v_mvarId_2639_,
                        v___y_2644_,
                        v___y_2645_,
                        v___y_2646_,
                        v___y_2647_,
                    );
                    if lean_obj_tag(v___x_2650_) == 0 {
                        v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
                        lean_inc(v_a_2651_);
                        lean_dec_ref_known(v___x_2650_, 1);
                        lean_inc(v_mvarId_2639_);
                        v___x_2652_ = l_Lean_MVarId_getType(
                            v_mvarId_2639_,
                            v___y_2644_,
                            v___y_2645_,
                            v___y_2646_,
                            v___y_2647_,
                        );
                        if lean_obj_tag(v___x_2652_) == 0 {
                            v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
                            lean_inc(v_a_2653_);
                            lean_dec_ref_known(v___x_2652_, 1);
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
                            if lean_obj_tag(v___x_2656_) == 0 {
                                v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                                lean_inc_n(v_a_2657_, 2);
                                lean_dec_ref_known(v___x_2656_, 1);
                                v___x_2658_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2639_, v_a_2657_, v___y_2645_);
                                v_isSharedCheck_2666_ = (!lean_is_exclusive(v___x_2658_)) as u8;
                                if v_isSharedCheck_2666_ == 0 {
                                    v_unused_2667_ = lean_ctor_get(v___x_2658_, 0);
                                    lean_dec(v_unused_2667_);
                                    v___x_2660_ = v___x_2658_;
                                    v_isShared_2661_ = v_isSharedCheck_2666_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_2658_);
                                    v___x_2660_ = lean_box(0);
                                    v_isShared_2661_ = v_isSharedCheck_2666_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_mvarId_2639_);
                                v_a_2668_ = lean_ctor_get(v___x_2656_, 0);
                                v_isSharedCheck_2675_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                                if v_isSharedCheck_2675_ == 0 {
                                    v___x_2670_ = v___x_2656_;
                                    v_isShared_2671_ = v_isSharedCheck_2675_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2668_);
                                    lean_dec(v___x_2656_);
                                    v___x_2670_ = lean_box(0);
                                    v_isShared_2671_ = v_isSharedCheck_2675_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2651_);
                            lean_dec_ref(v_val_2643_);
                            lean_dec_ref(v_type_2642_);
                            lean_dec(v_name_2641_);
                            lean_dec(v_mvarId_2639_);
                            v_a_2676_ = lean_ctor_get(v___x_2652_, 0);
                            v_isSharedCheck_2683_ = (!lean_is_exclusive(v___x_2652_)) as u8;
                            if v_isSharedCheck_2683_ == 0 {
                                v___x_2678_ = v___x_2652_;
                                v_isShared_2679_ = v_isSharedCheck_2683_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2676_);
                                lean_dec(v___x_2652_);
                                v___x_2678_ = lean_box(0);
                                v_isShared_2679_ = v_isSharedCheck_2683_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_val_2643_);
                        lean_dec_ref(v_type_2642_);
                        lean_dec(v_name_2641_);
                        lean_dec(v_mvarId_2639_);
                        v_a_2684_ = lean_ctor_get(v___x_2650_, 0);
                        v_isSharedCheck_2691_ = (!lean_is_exclusive(v___x_2650_)) as u8;
                        if v_isSharedCheck_2691_ == 0 {
                            v___x_2686_ = v___x_2650_;
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2684_);
                            lean_dec(v___x_2650_);
                            v___x_2686_ = lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2691_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_val_2643_);
                    lean_dec_ref(v_type_2642_);
                    lean_dec(v_name_2641_);
                    lean_dec(v_mvarId_2639_);
                    v_a_2692_ = lean_ctor_get(v___x_2649_, 0);
                    v_isSharedCheck_2699_ = (!lean_is_exclusive(v___x_2649_)) as u8;
                    if v_isSharedCheck_2699_ == 0 {
                        v___x_2694_ = v___x_2649_;
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2692_);
                        lean_dec(v___x_2649_);
                        v___x_2694_ = lean_box(0);
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2662_ = l_Lean_Expr_mvarId_x21(v_a_2657_);
                lean_dec(v_a_2657_);
                if v_isShared_2661_ == 0 {
                    lean_ctor_set(v___x_2660_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
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
                    v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
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
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
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
                    v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
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
                    v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
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
    mut v_mvarId_2700_: *mut LeanObject,
    mut v___x_2701_: *mut LeanObject,
    mut v_name_2702_: *mut LeanObject,
    mut v_type_2703_: *mut LeanObject,
    mut v_val_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2708_);
    lean_dec_ref(v___y_2707_);
    lean_dec(v___y_2706_);
    lean_dec_ref(v___y_2705_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_MVarId_define(
    mut v_mvarId_2714_: *mut LeanObject,
    mut v_name_2715_: *mut LeanObject,
    mut v_type_2716_: *mut LeanObject,
    mut v_val_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_MVarId_define___closed__1;
    lean_inc(v_mvarId_2714_);
    v___f_2724_ = lean_alloc_closure(
        l_Lean_MVarId_define___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_2724_, 0, v_mvarId_2714_);
    lean_closure_set(v___f_2724_, 1, v___x_2723_);
    lean_closure_set(v___f_2724_, 2, v_name_2715_);
    lean_closure_set(v___f_2724_, 3, v_type_2716_);
    lean_closure_set(v___f_2724_, 4, v_val_2717_);
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
    mut v_mvarId_2726_: *mut LeanObject,
    mut v_name_2727_: *mut LeanObject,
    mut v_type_2728_: *mut LeanObject,
    mut v_val_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_a_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
    mut v_a_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2733_);
    lean_dec_ref(v_a_2732_);
    lean_dec(v_a_2731_);
    lean_dec_ref(v_a_2730_);
    return v_res_2735_;
}
pub unsafe fn _init_l_Lean_MVarId_assertExt___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    v___x_2739_ = lean_unsigned_to_nat(0);
    v___x_2740_ = l_Lean_mkBVar(v___x_2739_);
    return v___x_2740_;
}
pub unsafe fn l_Lean_MVarId_assertExt___lam__0(
    mut v_mvarId_2741_: *mut LeanObject,
    mut v___x_2742_: *mut LeanObject,
    mut v_type_2743_: *mut LeanObject,
    mut v_val_2744_: *mut LeanObject,
    mut v_hName_2745_: *mut LeanObject,
    mut v_name_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_unused_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v_a_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_a_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2826_: u8 = 0;
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2741_);
                v___x_2752_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2741_,
                    v___x_2742_,
                    v___y_2747_,
                    v___y_2748_,
                    v___y_2749_,
                    v___y_2750_,
                );
                if lean_obj_tag(v___x_2752_) == 0 {
                    lean_dec_ref_known(v___x_2752_, 1);
                    lean_inc(v_mvarId_2741_);
                    v___x_2753_ = l_Lean_MVarId_getTag(
                        v_mvarId_2741_,
                        v___y_2747_,
                        v___y_2748_,
                        v___y_2749_,
                        v___y_2750_,
                    );
                    if lean_obj_tag(v___x_2753_) == 0 {
                        v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
                        lean_inc(v_a_2754_);
                        lean_dec_ref_known(v___x_2753_, 1);
                        lean_inc(v_mvarId_2741_);
                        v___x_2755_ = l_Lean_MVarId_getType(
                            v_mvarId_2741_,
                            v___y_2747_,
                            v___y_2748_,
                            v___y_2749_,
                            v___y_2750_,
                        );
                        if lean_obj_tag(v___x_2755_) == 0 {
                            v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
                            lean_inc(v_a_2756_);
                            lean_dec_ref_known(v___x_2755_, 1);
                            lean_inc_ref(v_type_2743_);
                            v___x_2757_ = l_Lean_Meta_getLevel(
                                v_type_2743_,
                                v___y_2747_,
                                v___y_2748_,
                                v___y_2749_,
                                v___y_2750_,
                            );
                            if lean_obj_tag(v___x_2757_) == 0 {
                                v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
                                lean_inc(v_a_2758_);
                                lean_dec_ref_known(v___x_2757_, 1);
                                v___x_2759_ = l_Lean_MVarId_assertExt___lam__0___closed__1;
                                v___x_2760_ = lean_box(0);
                                v___x_2761_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_2761_, 0, v_a_2758_);
                                lean_ctor_set(v___x_2761_, 1, v___x_2760_);
                                v___x_2762_ = l_Lean_mkConst(v___x_2759_, v___x_2761_);
                                v___x_2763_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_assertExt___lam__0___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_assertExt___lam__0___closed__2_once
                                    ),
                                    _init_l_Lean_MVarId_assertExt___lam__0___closed__2,
                                );
                                lean_inc_ref(v_val_2744_);
                                lean_inc_ref(v_type_2743_);
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
                                if lean_obj_tag(v___x_2768_) == 0 {
                                    v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
                                    lean_inc(v_a_2769_);
                                    lean_dec_ref_known(v___x_2768_, 1);
                                    lean_inc_ref(v_val_2744_);
                                    v___x_2770_ = l_Lean_Meta_mkEqRefl(
                                        v_val_2744_,
                                        v___y_2747_,
                                        v___y_2748_,
                                        v___y_2749_,
                                        v___y_2750_,
                                    );
                                    if lean_obj_tag(v___x_2770_) == 0 {
                                        v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
                                        lean_inc(v_a_2771_);
                                        lean_dec_ref_known(v___x_2770_, 1);
                                        lean_inc(v_a_2769_);
                                        v___x_2772_ =
                                            l_Lean_mkAppB(v_a_2769_, v_val_2744_, v_a_2771_);
                                        v___x_2773_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(v_mvarId_2741_, v___x_2772_, v___y_2748_);
                                        v_isSharedCheck_2781_ =
                                            (!lean_is_exclusive(v___x_2773_)) as u8;
                                        if v_isSharedCheck_2781_ == 0 {
                                            v_unused_2782_ = lean_ctor_get(v___x_2773_, 0);
                                            lean_dec(v_unused_2782_);
                                            v___x_2775_ = v___x_2773_;
                                            v_isShared_2776_ = v_isSharedCheck_2781_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v___x_2773_);
                                            v___x_2775_ = lean_box(0);
                                            v_isShared_2776_ = v_isSharedCheck_2781_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_2769_);
                                        lean_dec_ref(v_val_2744_);
                                        lean_dec(v_mvarId_2741_);
                                        v_a_2783_ = lean_ctor_get(v___x_2770_, 0);
                                        v_isSharedCheck_2790_ =
                                            (!lean_is_exclusive(v___x_2770_)) as u8;
                                        if v_isSharedCheck_2790_ == 0 {
                                            v___x_2785_ = v___x_2770_;
                                            v_isShared_2786_ = v_isSharedCheck_2790_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2783_);
                                            lean_dec(v___x_2770_);
                                            v___x_2785_ = lean_box(0);
                                            v_isShared_2786_ = v_isSharedCheck_2790_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_val_2744_);
                                    lean_dec(v_mvarId_2741_);
                                    v_a_2791_ = lean_ctor_get(v___x_2768_, 0);
                                    v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2768_)) as u8;
                                    if v_isSharedCheck_2798_ == 0 {
                                        v___x_2793_ = v___x_2768_;
                                        v_isShared_2794_ = v_isSharedCheck_2798_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2791_);
                                        lean_dec(v___x_2768_);
                                        v___x_2793_ = lean_box(0);
                                        v_isShared_2794_ = v_isSharedCheck_2798_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2756_);
                                lean_dec(v_a_2754_);
                                lean_dec(v_name_2746_);
                                lean_dec(v_hName_2745_);
                                lean_dec_ref(v_val_2744_);
                                lean_dec_ref(v_type_2743_);
                                lean_dec(v_mvarId_2741_);
                                v_a_2799_ = lean_ctor_get(v___x_2757_, 0);
                                v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2757_)) as u8;
                                if v_isSharedCheck_2806_ == 0 {
                                    v___x_2801_ = v___x_2757_;
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2799_);
                                    lean_dec(v___x_2757_);
                                    v___x_2801_ = lean_box(0);
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2754_);
                            lean_dec(v_name_2746_);
                            lean_dec(v_hName_2745_);
                            lean_dec_ref(v_val_2744_);
                            lean_dec_ref(v_type_2743_);
                            lean_dec(v_mvarId_2741_);
                            v_a_2807_ = lean_ctor_get(v___x_2755_, 0);
                            v_isSharedCheck_2814_ = (!lean_is_exclusive(v___x_2755_)) as u8;
                            if v_isSharedCheck_2814_ == 0 {
                                v___x_2809_ = v___x_2755_;
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2807_);
                                lean_dec(v___x_2755_);
                                v___x_2809_ = lean_box(0);
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_name_2746_);
                        lean_dec(v_hName_2745_);
                        lean_dec_ref(v_val_2744_);
                        lean_dec_ref(v_type_2743_);
                        lean_dec(v_mvarId_2741_);
                        v_a_2815_ = lean_ctor_get(v___x_2753_, 0);
                        v_isSharedCheck_2822_ = (!lean_is_exclusive(v___x_2753_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2753_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2815_);
                            lean_dec(v___x_2753_);
                            v___x_2817_ = lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_name_2746_);
                    lean_dec(v_hName_2745_);
                    lean_dec_ref(v_val_2744_);
                    lean_dec_ref(v_type_2743_);
                    lean_dec(v_mvarId_2741_);
                    v_a_2823_ = lean_ctor_get(v___x_2752_, 0);
                    v_isSharedCheck_2830_ = (!lean_is_exclusive(v___x_2752_)) as u8;
                    if v_isSharedCheck_2830_ == 0 {
                        v___x_2825_ = v___x_2752_;
                        v_isShared_2826_ = v_isSharedCheck_2830_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2823_);
                        lean_dec(v___x_2752_);
                        v___x_2825_ = lean_box(0);
                        v_isShared_2826_ = v_isSharedCheck_2830_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2777_ = l_Lean_Expr_mvarId_x21(v_a_2769_);
                lean_dec(v_a_2769_);
                if v_isShared_2776_ == 0 {
                    lean_ctor_set(v___x_2775_, 0, v___x_2777_);
                    v___x_2779_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
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
                    v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
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
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
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
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
                    v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
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
                    v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
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
                    v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
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
    mut v_mvarId_2831_: *mut LeanObject,
    mut v___x_2832_: *mut LeanObject,
    mut v_type_2833_: *mut LeanObject,
    mut v_val_2834_: *mut LeanObject,
    mut v_hName_2835_: *mut LeanObject,
    mut v_name_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
    mut v___y_2840_: *mut LeanObject,
    mut v___y_2841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2842_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2840_);
    lean_dec_ref(v___y_2839_);
    lean_dec(v___y_2838_);
    lean_dec_ref(v___y_2837_);
    return v_res_2842_;
}
pub unsafe fn l_Lean_MVarId_assertExt(
    mut v_mvarId_2843_: *mut LeanObject,
    mut v_name_2844_: *mut LeanObject,
    mut v_type_2845_: *mut LeanObject,
    mut v_val_2846_: *mut LeanObject,
    mut v_hName_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
    mut v_a_2849_: *mut LeanObject,
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_MVarId_assert___closed__1;
    lean_inc(v_mvarId_2843_);
    v___f_2854_ = lean_alloc_closure(
        l_Lean_MVarId_assertExt___lam__0___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___f_2854_, 0, v_mvarId_2843_);
    lean_closure_set(v___f_2854_, 1, v___x_2853_);
    lean_closure_set(v___f_2854_, 2, v_type_2845_);
    lean_closure_set(v___f_2854_, 3, v_val_2846_);
    lean_closure_set(v___f_2854_, 4, v_hName_2847_);
    lean_closure_set(v___f_2854_, 5, v_name_2844_);
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
    mut v_mvarId_2856_: *mut LeanObject,
    mut v_name_2857_: *mut LeanObject,
    mut v_type_2858_: *mut LeanObject,
    mut v_val_2859_: *mut LeanObject,
    mut v_hName_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2866_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2864_);
    lean_dec_ref(v_a_2863_);
    lean_dec(v_a_2862_);
    lean_dec_ref(v_a_2861_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(
    mut v_t_2867_: *mut LeanObject,
    mut v___y_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2872_: u8 = 0;
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v_enabled_2888_: u8 = 0;
    let mut v_assignment_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2870_ = lean_st_ref_get(v___y_2868_);
                v_infoState_2871_ = lean_ctor_get(v___x_2870_, 7);
                lean_inc_ref(v_infoState_2871_);
                lean_dec(v___x_2870_);
                v_enabled_2872_ = lean_ctor_get_uint8(
                    v_infoState_2871_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_2871_);
                if v_enabled_2872_ == 0 {
                    lean_dec_ref(v_t_2867_);
                    v___x_2873_ = lean_box(0);
                    v___x_2874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2874_, 0, v___x_2873_);
                    return v___x_2874_;
                } else {
                    v___x_2875_ = lean_st_ref_take(v___y_2868_);
                    v_infoState_2876_ = lean_ctor_get(v___x_2875_, 7);
                    v_env_2877_ = lean_ctor_get(v___x_2875_, 0);
                    v_nextMacroScope_2878_ = lean_ctor_get(v___x_2875_, 1);
                    v_ngen_2879_ = lean_ctor_get(v___x_2875_, 2);
                    v_auxDeclNGen_2880_ = lean_ctor_get(v___x_2875_, 3);
                    v_traceState_2881_ = lean_ctor_get(v___x_2875_, 4);
                    v_cache_2882_ = lean_ctor_get(v___x_2875_, 5);
                    v_messages_2883_ = lean_ctor_get(v___x_2875_, 6);
                    v_snapshotTasks_2884_ = lean_ctor_get(v___x_2875_, 8);
                    v_isSharedCheck_2906_ = (!lean_is_exclusive(v___x_2875_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2886_ = v___x_2875_;
                        v_isShared_2887_ = v_isSharedCheck_2906_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_2884_);
                        lean_inc(v_infoState_2876_);
                        lean_inc(v_messages_2883_);
                        lean_inc(v_cache_2882_);
                        lean_inc(v_traceState_2881_);
                        lean_inc(v_auxDeclNGen_2880_);
                        lean_inc(v_ngen_2879_);
                        lean_inc(v_nextMacroScope_2878_);
                        lean_inc(v_env_2877_);
                        lean_dec(v___x_2875_);
                        v___x_2886_ = lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2906_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_2888_ = lean_ctor_get_uint8(
                    v_infoState_2876_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_2889_ = lean_ctor_get(v_infoState_2876_, 0);
                v_lazyAssignment_2890_ = lean_ctor_get(v_infoState_2876_, 1);
                v_trees_2891_ = lean_ctor_get(v_infoState_2876_, 2);
                v_isSharedCheck_2905_ = (!lean_is_exclusive(v_infoState_2876_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v___x_2893_ = v_infoState_2876_;
                    v_isShared_2894_ = v_isSharedCheck_2905_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_2891_);
                    lean_inc(v_lazyAssignment_2890_);
                    lean_inc(v_assignment_2889_);
                    lean_dec(v_infoState_2876_);
                    v___x_2893_ = lean_box(0);
                    v_isShared_2894_ = v_isSharedCheck_2905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2895_ = l_Lean_PersistentArray_push___redArg(v_trees_2891_, v_t_2867_);
                if v_isShared_2894_ == 0 {
                    lean_ctor_set(v___x_2893_, 2, v___x_2895_);
                    v___x_2897_ = v___x_2893_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_assignment_2889_);
                    lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_lazyAssignment_2890_);
                    lean_ctor_set(v_reuseFailAlloc_2904_, 2, v___x_2895_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_2888_,
                    );
                    v___x_2897_ = v_reuseFailAlloc_2904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2887_ == 0 {
                    lean_ctor_set(v___x_2886_, 7, v___x_2897_);
                    v___x_2899_ = v___x_2886_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2880_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_traceState_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2882_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_messages_2883_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 7, v___x_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_snapshotTasks_2884_);
                    v___x_2899_ = v_reuseFailAlloc_2903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2900_ = lean_st_ref_set(v___y_2868_, v___x_2899_);
                v___x_2901_ = lean_box(0);
                v___x_2902_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2902_, 0, v___x_2901_);
                return v___x_2902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg___boxed(
    mut v_t_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2910_: *mut LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_2907_, v___y_2908_);
    lean_dec(v___y_2908_);
    return v_res_2910_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    v___x_2911_ = lean_unsigned_to_nat(32);
    v___x_2912_ = lean_mk_empty_array_with_capacity(v___x_2911_);
    v___x_2913_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2913_, 0, v___x_2912_);
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2914_: usize = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = 5usize;
    v___x_2915_ = lean_unsigned_to_nat(0);
    v___x_2916_ = lean_unsigned_to_nat(32);
    v___x_2917_ = lean_mk_empty_array_with_capacity(v___x_2916_);
    v___x_2918_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0_once
        ),
        _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__0,
    );
    v___x_2919_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2919_, 0, v___x_2918_);
    lean_ctor_set(v___x_2919_, 1, v___x_2917_);
    lean_ctor_set(v___x_2919_, 2, v___x_2915_);
    lean_ctor_set(v___x_2919_, 3, v___x_2915_);
    lean_ctor_set_usize(v___x_2919_, 4, v___x_2914_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
    mut v_t_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_2928_: u8 = 0;
    v___x_2926_ = lean_st_ref_get(v___y_2924_);
    v_infoState_2927_ = lean_ctor_get(v___x_2926_, 7);
    lean_inc_ref(v_infoState_2927_);
    lean_dec(v___x_2926_);
    v_enabled_2928_ = lean_ctor_get_uint8(
        v_infoState_2927_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_2927_);
    if v_enabled_2928_ == 0 {
        let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_2920_);
        v___x_2929_ = lean_box(0);
        v___x_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2930_, 0, v___x_2929_);
        return v___x_2930_;
    } else {
        let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
        v___x_2931_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1_once
            ),
            _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___closed__1,
        );
        v___x_2932_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2932_, 0, v_t_2920_);
        lean_ctor_set(v___x_2932_, 1, v___x_2931_);
        v___x_2933_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v___x_2932_, v___y_2924_);
        return v___x_2933_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0___boxed(
    mut v_t_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
        v_t_2934_,
        v___y_2935_,
        v___y_2936_,
        v___y_2937_,
        v___y_2938_,
    );
    lean_dec(v___y_2938_);
    lean_dec_ref(v___y_2937_);
    lean_dec(v___y_2936_);
    lean_dec_ref(v___y_2935_);
    return v_res_2940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(
    mut v___x_2941_: *mut LeanObject,
    mut v_as_2942_: *mut LeanObject,
    mut v_sz_2943_: usize,
    mut v_i_2944_: usize,
    mut v_b_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v_array_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v_reuseFailAlloc_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2992_: u8 = 0;
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_unused_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2951_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
                if v___x_2951_ == 0 {
                    lean_dec_ref(v___x_2941_);
                    v___x_2952_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2952_, 0, v_b_2945_);
                    return v___x_2952_;
                } else {
                    v_snd_2953_ = lean_ctor_get(v_b_2945_, 1);
                    v_fst_2954_ = lean_ctor_get(v_b_2945_, 0);
                    v_isSharedCheck_3001_ = (!lean_is_exclusive(v_b_2945_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2956_ = v_b_2945_;
                        v_isShared_2957_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2953_);
                        lean_inc(v_fst_2954_);
                        lean_dec(v_b_2945_);
                        v___x_2956_ = lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_2958_ = lean_ctor_get(v_snd_2953_, 0);
                v_start_2959_ = lean_ctor_get(v_snd_2953_, 1);
                v_stop_2960_ = lean_ctor_get(v_snd_2953_, 2);
                v___x_2961_ = lean_nat_dec_lt(v_start_2959_, v_stop_2960_);
                if v___x_2961_ == 0 {
                    lean_dec_ref(v___x_2941_);
                    if v_isShared_2957_ == 0 {
                        v___x_2963_ = v___x_2956_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_fst_2954_);
                        lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2953_);
                        v___x_2963_ = v_reuseFailAlloc_2965_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_2960_);
                    lean_inc(v_start_2959_);
                    lean_inc_ref(v_array_2958_);
                    v_isSharedCheck_2997_ = (!lean_is_exclusive(v_snd_2953_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v_unused_2998_ = lean_ctor_get(v_snd_2953_, 2);
                        lean_dec(v_unused_2998_);
                        v_unused_2999_ = lean_ctor_get(v_snd_2953_, 1);
                        lean_dec(v_unused_2999_);
                        v_unused_3000_ = lean_ctor_get(v_snd_2953_, 0);
                        lean_dec(v_unused_3000_);
                        v___x_2967_ = v_snd_2953_;
                        v_isShared_2968_ = v_isSharedCheck_2997_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_snd_2953_);
                        v___x_2967_ = lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_2997_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2964_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2964_, 0, v___x_2963_);
                return v___x_2964_;
            }
            3 => {
                v_a_2969_ = lean_array_uget_borrowed(v_as_2942_, v_i_2944_);
                v___x_2970_ = lean_array_fget_borrowed(v_array_2958_, v_start_2959_);
                lean_inc_n(v___x_2970_, 3);
                v___x_2971_ = l_Lean_mkFVar(v___x_2970_);
                lean_inc_n(v_a_2969_, 2);
                v___x_2972_ = l_Lean_Meta_FVarSubst_insert(v_fst_2954_, v_a_2969_, v___x_2971_);
                lean_inc_ref(v___x_2941_);
                v___x_2973_ = l_Lean_LocalContext_get_x21(v___x_2941_, v___x_2970_);
                v___x_2974_ = l_Lean_LocalDecl_userName(v___x_2973_);
                lean_dec_ref(v___x_2973_);
                v___x_2975_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2975_, 0, v___x_2974_);
                lean_ctor_set(v___x_2975_, 1, v___x_2970_);
                lean_ctor_set(v___x_2975_, 2, v_a_2969_);
                v___x_2976_ = lean_alloc_ctor(11, 1, (0) as u32);
                lean_ctor_set(v___x_2976_, 0, v___x_2975_);
                v___x_2977_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0(
                    v___x_2976_,
                    v___y_2946_,
                    v___y_2947_,
                    v___y_2948_,
                    v___y_2949_,
                );
                if lean_obj_tag(v___x_2977_) == 0 {
                    lean_dec_ref_known(v___x_2977_, 1);
                    v___x_2978_ = lean_unsigned_to_nat(1);
                    v___x_2979_ = lean_nat_add(v_start_2959_, v___x_2978_);
                    lean_dec(v_start_2959_);
                    if v_isShared_2968_ == 0 {
                        lean_ctor_set(v___x_2967_, 1, v___x_2979_);
                        v___x_2981_ = v___x_2967_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_array_2958_);
                        lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2979_);
                        lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_stop_2960_);
                        v___x_2981_ = v_reuseFailAlloc_2988_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2972_);
                    lean_del_object(v___x_2967_);
                    lean_dec(v_stop_2960_);
                    lean_dec(v_start_2959_);
                    lean_dec_ref(v_array_2958_);
                    lean_del_object(v___x_2956_);
                    lean_dec_ref(v___x_2941_);
                    v_a_2989_ = lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_2996_ = (!lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v___x_2991_ = v___x_2977_;
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2989_);
                        lean_dec(v___x_2977_);
                        v___x_2991_ = lean_box(0);
                        v_isShared_2992_ = v_isSharedCheck_2996_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2957_ == 0 {
                    lean_ctor_set(v___x_2956_, 1, v___x_2981_);
                    lean_ctor_set(v___x_2956_, 0, v___x_2972_);
                    v___x_2983_ = v___x_2956_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2972_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2981_);
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
                    v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
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
    mut v___x_3002_: *mut LeanObject,
    mut v_as_3003_: *mut LeanObject,
    mut v_sz_3004_: *mut LeanObject,
    mut v_i_3005_: *mut LeanObject,
    mut v_b_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3012_: usize = 0;
    let mut v_i_boxed_3013_: usize = 0;
    let mut v_res_3014_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3012_ = lean_unbox_usize(v_sz_3004_);
    lean_dec(v_sz_3004_);
    v_i_boxed_3013_ = lean_unbox_usize(v_i_3005_);
    lean_dec(v_i_3005_);
    v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__1(v___x_3002_, v_as_3003_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
    lean_dec(v___y_3010_);
    lean_dec_ref(v___y_3009_);
    lean_dec(v___y_3008_);
    lean_dec_ref(v___y_3007_);
    lean_dec_ref(v_as_3003_);
    return v_res_3014_;
}
pub unsafe fn l_Lean_MVarId_assertAfter(
    mut v_mvarId_3018_: *mut LeanObject,
    mut v_fvarId_3019_: *mut LeanObject,
    mut v_userName_3020_: *mut LeanObject,
    mut v_type_3021_: *mut LeanObject,
    mut v_val_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u8 = 0;
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v_fst_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_a_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_reuseFailAlloc_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_a_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_a_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut v_a_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut v_a_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3118_: u8 = 0;
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3028_ = l_Lean_MVarId_assertAfter___closed__1;
                lean_inc(v_mvarId_3018_);
                v___x_3029_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3018_,
                    v___x_3028_,
                    v_a_3023_,
                    v_a_3024_,
                    v_a_3025_,
                    v_a_3026_,
                );
                if lean_obj_tag(v___x_3029_) == 0 {
                    lean_dec_ref_known(v___x_3029_, 1);
                    v___x_3030_ = l_Lean_MVarId_revertAfter(
                        v_mvarId_3018_,
                        v_fvarId_3019_,
                        v_a_3023_,
                        v_a_3024_,
                        v_a_3025_,
                        v_a_3026_,
                    );
                    if lean_obj_tag(v___x_3030_) == 0 {
                        v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
                        lean_inc(v_a_3031_);
                        lean_dec_ref_known(v___x_3030_, 1);
                        v_fst_3032_ = lean_ctor_get(v_a_3031_, 0);
                        lean_inc(v_fst_3032_);
                        v_snd_3033_ = lean_ctor_get(v_a_3031_, 1);
                        lean_inc(v_snd_3033_);
                        lean_dec(v_a_3031_);
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
                        if lean_obj_tag(v___x_3034_) == 0 {
                            v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
                            lean_inc(v_a_3035_);
                            lean_dec_ref_known(v___x_3034_, 1);
                            v___x_3036_ = 1;
                            v___x_3037_ = l_Lean_Meta_intro1Core(
                                v_a_3035_,
                                v___x_3036_,
                                v_a_3023_,
                                v_a_3024_,
                                v_a_3025_,
                                v_a_3026_,
                            );
                            if lean_obj_tag(v___x_3037_) == 0 {
                                v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
                                lean_inc(v_a_3038_);
                                lean_dec_ref_known(v___x_3037_, 1);
                                v_fst_3039_ = lean_ctor_get(v_a_3038_, 0);
                                lean_inc(v_fst_3039_);
                                v_snd_3040_ = lean_ctor_get(v_a_3038_, 1);
                                lean_inc(v_snd_3040_);
                                lean_dec(v_a_3038_);
                                v___x_3041_ = lean_array_get_size(v_fst_3032_);
                                v___x_3042_ = lean_box(0);
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
                                if lean_obj_tag(v___x_3044_) == 0 {
                                    v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
                                    lean_inc(v_a_3045_);
                                    lean_dec_ref_known(v___x_3044_, 1);
                                    v_fst_3046_ = lean_ctor_get(v_a_3045_, 0);
                                    v_snd_3047_ = lean_ctor_get(v_a_3045_, 1);
                                    v_isSharedCheck_3090_ = (!lean_is_exclusive(v_a_3045_)) as u8;
                                    if v_isSharedCheck_3090_ == 0 {
                                        v___x_3049_ = v_a_3045_;
                                        v_isShared_3050_ = v_isSharedCheck_3090_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_3047_);
                                        lean_inc(v_fst_3046_);
                                        lean_dec(v_a_3045_);
                                        v___x_3049_ = lean_box(0);
                                        v_isShared_3050_ = v_isSharedCheck_3090_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_fst_3039_);
                                    lean_dec(v_fst_3032_);
                                    v_a_3091_ = lean_ctor_get(v___x_3044_, 0);
                                    v_isSharedCheck_3098_ = (!lean_is_exclusive(v___x_3044_)) as u8;
                                    if v_isSharedCheck_3098_ == 0 {
                                        v___x_3093_ = v___x_3044_;
                                        v_isShared_3094_ = v_isSharedCheck_3098_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3091_);
                                        lean_dec(v___x_3044_);
                                        v___x_3093_ = lean_box(0);
                                        v_isShared_3094_ = v_isSharedCheck_3098_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_fst_3032_);
                                v_a_3099_ = lean_ctor_get(v___x_3037_, 0);
                                v_isSharedCheck_3106_ = (!lean_is_exclusive(v___x_3037_)) as u8;
                                if v_isSharedCheck_3106_ == 0 {
                                    v___x_3101_ = v___x_3037_;
                                    v_isShared_3102_ = v_isSharedCheck_3106_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_3099_);
                                    lean_dec(v___x_3037_);
                                    v___x_3101_ = lean_box(0);
                                    v_isShared_3102_ = v_isSharedCheck_3106_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_fst_3032_);
                            v_a_3107_ = lean_ctor_get(v___x_3034_, 0);
                            v_isSharedCheck_3114_ = (!lean_is_exclusive(v___x_3034_)) as u8;
                            if v_isSharedCheck_3114_ == 0 {
                                v___x_3109_ = v___x_3034_;
                                v_isShared_3110_ = v_isSharedCheck_3114_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_3107_);
                                lean_dec(v___x_3034_);
                                v___x_3109_ = lean_box(0);
                                v_isShared_3110_ = v_isSharedCheck_3114_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_val_3022_);
                        lean_dec_ref(v_type_3021_);
                        lean_dec(v_userName_3020_);
                        v_a_3115_ = lean_ctor_get(v___x_3030_, 0);
                        v_isSharedCheck_3122_ = (!lean_is_exclusive(v___x_3030_)) as u8;
                        if v_isSharedCheck_3122_ == 0 {
                            v___x_3117_ = v___x_3030_;
                            v_isShared_3118_ = v_isSharedCheck_3122_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3115_);
                            lean_dec(v___x_3030_);
                            v___x_3117_ = lean_box(0);
                            v_isShared_3118_ = v_isSharedCheck_3122_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_val_3022_);
                    lean_dec_ref(v_type_3021_);
                    lean_dec(v_userName_3020_);
                    lean_dec(v_fvarId_3019_);
                    lean_dec(v_mvarId_3018_);
                    v_a_3123_ = lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3130_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3130_ == 0 {
                        v___x_3125_ = v___x_3029_;
                        v_isShared_3126_ = v_isSharedCheck_3130_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3123_);
                        lean_dec(v___x_3029_);
                        v___x_3125_ = lean_box(0);
                        v_isShared_3126_ = v_isSharedCheck_3130_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_snd_3047_);
                v___x_3051_ =
                    l_Lean_MVarId_getDecl(v_snd_3047_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
                if lean_obj_tag(v___x_3051_) == 0 {
                    v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
                    lean_inc(v_a_3052_);
                    lean_dec_ref_known(v___x_3051_, 1);
                    v_lctx_3053_ = lean_ctor_get(v_a_3052_, 1);
                    lean_inc_ref(v_lctx_3053_);
                    lean_dec(v_a_3052_);
                    v___x_3054_ = lean_box(0);
                    v___x_3055_ = lean_unsigned_to_nat(0);
                    v___x_3056_ = lean_array_get_size(v_fst_3046_);
                    v___x_3057_ =
                        l_Array_toSubarray___redArg(v_fst_3046_, v___x_3055_, v___x_3056_);
                    if v_isShared_3050_ == 0 {
                        lean_ctor_set(v___x_3049_, 1, v___x_3057_);
                        lean_ctor_set(v___x_3049_, 0, v___x_3054_);
                        v___x_3059_ = v___x_3049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3054_);
                        lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3057_);
                        v___x_3059_ = v_reuseFailAlloc_3081_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3049_);
                    lean_dec(v_snd_3047_);
                    lean_dec(v_fst_3046_);
                    lean_dec(v_fst_3039_);
                    lean_dec(v_fst_3032_);
                    v_a_3082_ = lean_ctor_get(v___x_3051_, 0);
                    v_isSharedCheck_3089_ = (!lean_is_exclusive(v___x_3051_)) as u8;
                    if v_isSharedCheck_3089_ == 0 {
                        v___x_3084_ = v___x_3051_;
                        v_isShared_3085_ = v_isSharedCheck_3089_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3082_);
                        lean_dec(v___x_3051_);
                        v___x_3084_ = lean_box(0);
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
                lean_dec(v_fst_3032_);
                if lean_obj_tag(v___x_3062_) == 0 {
                    v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3072_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3072_ == 0 {
                        v___x_3065_ = v___x_3062_;
                        v_isShared_3066_ = v_isSharedCheck_3072_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3063_);
                        lean_dec(v___x_3062_);
                        v___x_3065_ = lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3072_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_3047_);
                    lean_dec(v_fst_3039_);
                    v_a_3073_ = lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3080_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3075_ = v___x_3062_;
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3073_);
                        lean_dec(v___x_3062_);
                        v___x_3075_ = lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3067_ = lean_ctor_get(v_a_3063_, 0);
                lean_inc(v_fst_3067_);
                lean_dec(v_a_3063_);
                v___x_3068_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3068_, 0, v_fst_3039_);
                lean_ctor_set(v___x_3068_, 1, v_snd_3047_);
                lean_ctor_set(v___x_3068_, 2, v_fst_3067_);
                if v_isShared_3066_ == 0 {
                    lean_ctor_set(v___x_3065_, 0, v___x_3068_);
                    v___x_3070_ = v___x_3065_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
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
                    v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
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
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
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
                    v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
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
                    v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
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
                    v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
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
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
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
                    v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
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
    mut v_mvarId_3131_: *mut LeanObject,
    mut v_fvarId_3132_: *mut LeanObject,
    mut v_userName_3133_: *mut LeanObject,
    mut v_type_3134_: *mut LeanObject,
    mut v_val_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3141_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3139_);
    lean_dec_ref(v_a_3138_);
    lean_dec(v_a_3137_);
    lean_dec_ref(v_a_3136_);
    return v_res_3141_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(
    mut v_t_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___redArg(v_t_3142_, v___y_3146_);
    return v___x_3148_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0___boxed(
    mut v_t_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3155_: *mut LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_assertAfter_spec__0_spec__0(v_t_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    lean_dec(v___y_3153_);
    lean_dec_ref(v___y_3152_);
    lean_dec(v___y_3151_);
    lean_dec_ref(v___y_3150_);
    return v_res_3155_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
    mut v_ldecl_x27_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3159_ = lean_st_ref_take(v_a_3157_);
                v___x_3165_ = lean_box(0);
                v___x_3166_ = l_Lean_LocalDecl_index(v___x_3159_);
                v___x_3167_ = l_Lean_LocalDecl_index(v_ldecl_x27_3156_);
                v___x_3168_ = lean_nat_dec_lt(v___x_3166_, v___x_3167_);
                lean_dec(v___x_3167_);
                lean_dec(v___x_3166_);
                if v___x_3168_ == 0 {
                    lean_dec_ref(v_ldecl_x27_3156_);
                    v_fst_3161_ = v___x_3165_;
                    v_snd_3162_ = v___x_3159_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_3159_);
                    v_fst_3161_ = v___x_3165_;
                    v_snd_3162_ = v_ldecl_x27_3156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3163_ = lean_st_ref_set(v_a_3157_, v_snd_3162_);
                v___x_3164_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3164_, 0, v_fst_3161_);
                return v___x_3164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg___boxed(
    mut v_ldecl_x27_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3172_: *mut LeanObject = core::ptr::null_mut();
    v_res_3172_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
            v_ldecl_x27_3169_,
            v_a_3170_,
        );
    lean_dec(v_a_3170_);
    return v_res_3172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(
    mut v_ldecl_x27_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    v___x_3180_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(
            v_ldecl_x27_3173_,
            v_a_3174_,
        );
    return v___x_3180_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___boxed(
    mut v_ldecl_x27_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3188_: *mut LeanObject = core::ptr::null_mut();
    v_res_3188_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl(
        v_ldecl_x27_3181_,
        v_a_3182_,
        v_a_3183_,
        v_a_3184_,
        v_a_3185_,
        v_a_3186_,
    );
    lean_dec(v_a_3186_);
    lean_dec_ref(v_a_3185_);
    lean_dec(v_a_3184_);
    lean_dec_ref(v_a_3183_);
    lean_dec(v_a_3182_);
    return v_res_3188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_as_3189_: *mut LeanObject,
    mut v_i_3190_: usize,
    mut v_stop_3191_: usize,
    mut v_b_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: usize = 0;
    let mut v___x_3201_: usize = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3203_ = lean_usize_dec_eq(v_i_3190_, v_stop_3191_);
                if v___x_3203_ == 0 {
                    v___x_3204_ = lean_array_uget_borrowed(v_as_3189_, v_i_3190_);
                    if lean_obj_tag(v___x_3204_) == 0 {
                        v___x_3205_ = lean_box(0);
                        v_a_3199_ = v___x_3205_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3206_ = lean_ctor_get(v___x_3204_, 0);
                        v___x_3207_ = l_Lean_LocalDecl_fvarId(v_val_3206_);
                        v___x_3208_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_3207_,
                            v___y_3194_,
                            v___y_3195_,
                            v___y_3196_,
                        );
                        if lean_obj_tag(v___x_3208_) == 0 {
                            v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
                            lean_inc(v_a_3209_);
                            lean_dec_ref_known(v___x_3208_, 1);
                            v___x_3210_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3209_, v___y_3193_);
                            if lean_obj_tag(v___x_3210_) == 0 {
                                v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
                                lean_inc(v_a_3211_);
                                lean_dec_ref_known(v___x_3210_, 1);
                                v_a_3199_ = v_a_3211_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3210_;
                            }
                        } else {
                            v_a_3212_ = lean_ctor_get(v___x_3208_, 0);
                            v_isSharedCheck_3219_ = (!lean_is_exclusive(v___x_3208_)) as u8;
                            if v_isSharedCheck_3219_ == 0 {
                                v___x_3214_ = v___x_3208_;
                                v_isShared_3215_ = v_isSharedCheck_3219_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3212_);
                                lean_dec(v___x_3208_);
                                v___x_3214_ = lean_box(0);
                                v_isShared_3215_ = v_isSharedCheck_3219_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3220_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3220_, 0, v_b_3192_);
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
                    v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
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
    mut v_as_3221_: *mut LeanObject,
    mut v_i_3222_: *mut LeanObject,
    mut v_stop_3223_: *mut LeanObject,
    mut v_b_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
    mut v___y_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3230_: usize = 0;
    let mut v_stop_boxed_3231_: usize = 0;
    let mut v_res_3232_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3230_ = lean_unbox_usize(v_i_3222_);
    lean_dec(v_i_3222_);
    v_stop_boxed_3231_ = lean_unbox_usize(v_stop_3223_);
    lean_dec(v_stop_3223_);
    v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_3221_, v_i_boxed_3230_, v_stop_boxed_3231_, v_b_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
    lean_dec(v___y_3228_);
    lean_dec_ref(v___y_3227_);
    lean_dec_ref(v___y_3226_);
    lean_dec(v___y_3225_);
    lean_dec_ref(v_as_3221_);
    return v_res_3232_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(
    mut v_as_3233_: *mut LeanObject,
    mut v_i_3234_: usize,
    mut v_stop_3235_: usize,
    mut v_b_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: usize = 0;
    let mut v___x_3246_: usize = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3248_ = lean_usize_dec_eq(v_i_3234_, v_stop_3235_);
                if v___x_3248_ == 0 {
                    v___x_3249_ = lean_array_uget_borrowed(v_as_3233_, v_i_3234_);
                    if lean_obj_tag(v___x_3249_) == 0 {
                        v___x_3250_ = lean_box(0);
                        v_a_3244_ = v___x_3250_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3251_ = lean_ctor_get(v___x_3249_, 0);
                        v___x_3252_ = l_Lean_LocalDecl_fvarId(v_val_3251_);
                        v___x_3253_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_3252_,
                            v___y_3238_,
                            v___y_3240_,
                            v___y_3241_,
                        );
                        if lean_obj_tag(v___x_3253_) == 0 {
                            v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
                            lean_inc(v_a_3254_);
                            lean_dec_ref_known(v___x_3253_, 1);
                            v___x_3255_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3254_, v___y_3237_);
                            if lean_obj_tag(v___x_3255_) == 0 {
                                v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
                                lean_inc(v_a_3256_);
                                lean_dec_ref_known(v___x_3255_, 1);
                                v_a_3244_ = v_a_3256_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3255_;
                            }
                        } else {
                            v_a_3257_ = lean_ctor_get(v___x_3253_, 0);
                            v_isSharedCheck_3264_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                            if v_isSharedCheck_3264_ == 0 {
                                v___x_3259_ = v___x_3253_;
                                v_isShared_3260_ = v_isSharedCheck_3264_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3257_);
                                lean_dec(v___x_3253_);
                                v___x_3259_ = lean_box(0);
                                v_isShared_3260_ = v_isSharedCheck_3264_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3265_, 0, v_b_3236_);
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
                    v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
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
    mut v_as_3266_: *mut LeanObject,
    mut v_i_3267_: *mut LeanObject,
    mut v_stop_3268_: *mut LeanObject,
    mut v_b_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3276_: usize = 0;
    let mut v_stop_boxed_3277_: usize = 0;
    let mut v_res_3278_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3276_ = lean_unbox_usize(v_i_3267_);
    lean_dec(v_i_3267_);
    v_stop_boxed_3277_ = lean_unbox_usize(v_stop_3268_);
    lean_dec(v_stop_3268_);
    v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_as_3266_, v_i_boxed_3276_, v_stop_boxed_3277_, v_b_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
    lean_dec(v___y_3274_);
    lean_dec_ref(v___y_3273_);
    lean_dec(v___y_3272_);
    lean_dec_ref(v___y_3271_);
    lean_dec(v___y_3270_);
    lean_dec_ref(v_as_3266_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(
    mut v_x_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: usize = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: usize = 0;
    let mut v___x_3305_: usize = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v_vs_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3311_: u8 = 0;
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: usize = 0;
    let mut v___x_3324_: usize = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3279_) == 0 {
                    v_cs_3286_ = lean_ctor_get(v_x_3279_, 0);
                    v_isSharedCheck_3307_ = (!lean_is_exclusive(v_x_3279_)) as u8;
                    if v_isSharedCheck_3307_ == 0 {
                        v___x_3288_ = v_x_3279_;
                        v_isShared_3289_ = v_isSharedCheck_3307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_3286_);
                        lean_dec(v_x_3279_);
                        v___x_3288_ = lean_box(0);
                        v_isShared_3289_ = v_isSharedCheck_3307_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3308_ = lean_ctor_get(v_x_3279_, 0);
                    v_isSharedCheck_3329_ = (!lean_is_exclusive(v_x_3279_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3310_ = v_x_3279_;
                        v_isShared_3311_ = v_isSharedCheck_3329_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_3308_);
                        lean_dec(v_x_3279_);
                        v___x_3310_ = lean_box(0);
                        v_isShared_3311_ = v_isSharedCheck_3329_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3290_ = lean_unsigned_to_nat(0);
                v___x_3291_ = lean_array_get_size(v_cs_3286_);
                v___x_3292_ = lean_box(0);
                v___x_3293_ = lean_nat_dec_lt(v___x_3290_, v___x_3291_);
                if v___x_3293_ == 0 {
                    lean_dec_ref(v_cs_3286_);
                    if v_isShared_3289_ == 0 {
                        lean_ctor_set(v___x_3288_, 0, v___x_3292_);
                        v___x_3295_ = v___x_3288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3292_);
                        v___x_3295_ = v_reuseFailAlloc_3296_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3297_ = lean_nat_dec_le(v___x_3291_, v___x_3291_);
                    if v___x_3297_ == 0 {
                        if v___x_3293_ == 0 {
                            lean_dec_ref(v_cs_3286_);
                            if v_isShared_3289_ == 0 {
                                lean_ctor_set(v___x_3288_, 0, v___x_3292_);
                                v___x_3299_ = v___x_3288_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3292_);
                                v___x_3299_ = v_reuseFailAlloc_3300_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3288_);
                            v___x_3301_ = 0usize;
                            v___x_3302_ = lean_usize_of_nat(v___x_3291_);
                            v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3286_, v___x_3301_, v___x_3302_, v___x_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                            lean_dec_ref(v_cs_3286_);
                            return v___x_3303_;
                        }
                    } else {
                        lean_del_object(v___x_3288_);
                        v___x_3304_ = 0usize;
                        v___x_3305_ = lean_usize_of_nat(v___x_3291_);
                        v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3286_, v___x_3304_, v___x_3305_, v___x_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                        lean_dec_ref(v_cs_3286_);
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
                v___x_3312_ = lean_unsigned_to_nat(0);
                v___x_3313_ = lean_array_get_size(v_vs_3308_);
                v___x_3314_ = lean_box(0);
                v___x_3315_ = lean_nat_dec_lt(v___x_3312_, v___x_3313_);
                if v___x_3315_ == 0 {
                    lean_dec_ref(v_vs_3308_);
                    if v_isShared_3311_ == 0 {
                        lean_ctor_set_tag(v___x_3310_, 0);
                        lean_ctor_set(v___x_3310_, 0, v___x_3314_);
                        v___x_3317_ = v___x_3310_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3314_);
                        v___x_3317_ = v_reuseFailAlloc_3318_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3319_ = lean_nat_dec_le(v___x_3313_, v___x_3313_);
                    if v___x_3319_ == 0 {
                        if v___x_3315_ == 0 {
                            lean_dec_ref(v_vs_3308_);
                            if v_isShared_3311_ == 0 {
                                lean_ctor_set_tag(v___x_3310_, 0);
                                lean_ctor_set(v___x_3310_, 0, v___x_3314_);
                                v___x_3321_ = v___x_3310_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3314_);
                                v___x_3321_ = v_reuseFailAlloc_3322_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3310_);
                            v___x_3323_ = 0usize;
                            v___x_3324_ = lean_usize_of_nat(v___x_3313_);
                            v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3308_, v___x_3323_, v___x_3324_, v___x_3314_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                            lean_dec_ref(v_vs_3308_);
                            return v___x_3325_;
                        }
                    } else {
                        lean_del_object(v___x_3310_);
                        v___x_3326_ = 0usize;
                        v___x_3327_ = lean_usize_of_nat(v___x_3313_);
                        v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3308_, v___x_3326_, v___x_3327_, v___x_3314_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
                        lean_dec_ref(v_vs_3308_);
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
    mut v_as_3330_: *mut LeanObject,
    mut v_i_3331_: usize,
    mut v_stop_3332_: usize,
    mut v_b_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3340_ = lean_usize_dec_eq(v_i_3331_, v_stop_3332_);
                if v___x_3340_ == 0 {
                    v___x_3341_ = lean_array_uget_borrowed(v_as_3330_, v_i_3331_);
                    lean_inc(v___x_3341_);
                    v___x_3342_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v___x_3341_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
                    if lean_obj_tag(v___x_3342_) == 0 {
                        v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
                        lean_inc(v_a_3343_);
                        lean_dec_ref_known(v___x_3342_, 1);
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
                    v___x_3347_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3347_, 0, v_b_3333_);
                    return v___x_3347_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_as_3348_: *mut LeanObject,
    mut v_i_3349_: *mut LeanObject,
    mut v_stop_3350_: *mut LeanObject,
    mut v_b_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3358_: usize = 0;
    let mut v_stop_boxed_3359_: usize = 0;
    let mut v_res_3360_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3358_ = lean_unbox_usize(v_i_3349_);
    lean_dec(v_i_3349_);
    v_stop_boxed_3359_ = lean_unbox_usize(v_stop_3350_);
    lean_dec(v_stop_3350_);
    v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_as_3348_, v_i_boxed_3358_, v_stop_boxed_3359_, v_b_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
    lean_dec(v___y_3356_);
    lean_dec_ref(v___y_3355_);
    lean_dec(v___y_3354_);
    lean_dec_ref(v___y_3353_);
    lean_dec(v___y_3352_);
    lean_dec_ref(v_as_3348_);
    return v_res_3360_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_x_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    lean_dec(v___y_3364_);
    lean_dec_ref(v___y_3363_);
    lean_dec(v___y_3362_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(
    mut v_t_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: usize = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: usize = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_unused_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3376_ = lean_ctor_get(v_t_3369_, 0);
                lean_inc_ref(v_root_3376_);
                v_tail_3377_ = lean_ctor_get(v_t_3369_, 1);
                lean_inc_ref(v_tail_3377_);
                lean_dec_ref(v_t_3369_);
                v___x_3378_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__3(v_root_3376_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                if lean_obj_tag(v___x_3378_) == 0 {
                    v_isSharedCheck_3399_ = (!lean_is_exclusive(v___x_3378_)) as u8;
                    if v_isSharedCheck_3399_ == 0 {
                        v_unused_3400_ = lean_ctor_get(v___x_3378_, 0);
                        lean_dec(v_unused_3400_);
                        v___x_3380_ = v___x_3378_;
                        v_isShared_3381_ = v_isSharedCheck_3399_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3378_);
                        v___x_3380_ = lean_box(0);
                        v_isShared_3381_ = v_isSharedCheck_3399_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_tail_3377_);
                    return v___x_3378_;
                }
            }
            1 => {
                v___x_3382_ = lean_unsigned_to_nat(0);
                v___x_3383_ = lean_array_get_size(v_tail_3377_);
                v___x_3384_ = lean_box(0);
                v___x_3385_ = lean_nat_dec_lt(v___x_3382_, v___x_3383_);
                if v___x_3385_ == 0 {
                    lean_dec_ref(v_tail_3377_);
                    if v_isShared_3381_ == 0 {
                        lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3387_ = v___x_3380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3384_);
                        v___x_3387_ = v_reuseFailAlloc_3388_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3389_ = lean_nat_dec_le(v___x_3383_, v___x_3383_);
                    if v___x_3389_ == 0 {
                        if v___x_3385_ == 0 {
                            lean_dec_ref(v_tail_3377_);
                            if v_isShared_3381_ == 0 {
                                lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                                v___x_3391_ = v___x_3380_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3384_);
                                v___x_3391_ = v_reuseFailAlloc_3392_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3380_);
                            v___x_3393_ = 0usize;
                            v___x_3394_ = lean_usize_of_nat(v___x_3383_);
                            v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3377_, v___x_3393_, v___x_3394_, v___x_3384_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                            lean_dec_ref(v_tail_3377_);
                            return v___x_3395_;
                        }
                    } else {
                        lean_del_object(v___x_3380_);
                        v___x_3396_ = 0usize;
                        v___x_3397_ = lean_usize_of_nat(v___x_3383_);
                        v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3377_, v___x_3396_, v___x_3397_, v___x_3384_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
                        lean_dec_ref(v_tail_3377_);
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
    mut v_t_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3408_: *mut LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__3(v_t_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
    lean_dec(v___y_3406_);
    lean_dec_ref(v___y_3405_);
    lean_dec(v___y_3404_);
    lean_dec_ref(v___y_3403_);
    lean_dec(v___y_3402_);
    return v_res_3408_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_3409_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(
    mut v_x_3410_: *mut LeanObject,
    mut v_x_3411_: usize,
    mut v_x_3412_: usize,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: usize = 0;
    let mut v_j_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: usize = 0;
    let mut v___x_3425_: usize = 0;
    let mut v___x_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: usize = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_unused_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: usize = 0;
    let mut v___x_3473_: usize = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3410_) == 0 {
                    v_cs_3419_ = lean_ctor_get(v_x_3410_, 0);
                    lean_inc_ref(v_cs_3419_);
                    lean_dec_ref_known(v_x_3410_, 1);
                    v___x_3420_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1___closed__0);
                    v___x_3421_ = lean_usize_shift_right(v_x_3411_, v_x_3412_);
                    v_j_3422_ = lean_usize_to_nat(v___x_3421_);
                    v___x_3423_ = lean_array_get_borrowed(v___x_3420_, v_cs_3419_, v_j_3422_);
                    v___x_3424_ = 1usize;
                    v___x_3425_ = lean_usize_shift_left(v___x_3424_, v_x_3412_);
                    v___x_3426_ = lean_usize_sub(v___x_3425_, v___x_3424_);
                    v___x_3427_ = lean_usize_land(v_x_3411_, v___x_3426_);
                    v___x_3428_ = 5usize;
                    v___x_3429_ = lean_usize_sub(v_x_3412_, v___x_3428_);
                    lean_inc(v___x_3423_);
                    v___x_3430_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v___x_3423_, v___x_3427_, v___x_3429_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                    if lean_obj_tag(v___x_3430_) == 0 {
                        v_isSharedCheck_3452_ = (!lean_is_exclusive(v___x_3430_)) as u8;
                        if v_isSharedCheck_3452_ == 0 {
                            v_unused_3453_ = lean_ctor_get(v___x_3430_, 0);
                            lean_dec(v_unused_3453_);
                            v___x_3432_ = v___x_3430_;
                            v_isShared_3433_ = v_isSharedCheck_3452_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3430_);
                            v___x_3432_ = lean_box(0);
                            v_isShared_3433_ = v_isSharedCheck_3452_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_j_3422_);
                        lean_dec_ref(v_cs_3419_);
                        return v___x_3430_;
                    }
                } else {
                    v_vs_3454_ = lean_ctor_get(v_x_3410_, 0);
                    v_isSharedCheck_3475_ = (!lean_is_exclusive(v_x_3410_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3456_ = v_x_3410_;
                        v_isShared_3457_ = v_isSharedCheck_3475_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_3454_);
                        lean_dec(v_x_3410_);
                        v___x_3456_ = lean_box(0);
                        v_isShared_3457_ = v_isSharedCheck_3475_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3434_ = lean_unsigned_to_nat(1);
                v___x_3435_ = lean_nat_add(v_j_3422_, v___x_3434_);
                lean_dec(v_j_3422_);
                v___x_3436_ = lean_array_get_size(v_cs_3419_);
                v___x_3437_ = lean_box(0);
                v___x_3438_ = lean_nat_dec_lt(v___x_3435_, v___x_3436_);
                if v___x_3438_ == 0 {
                    lean_dec(v___x_3435_);
                    lean_dec_ref(v_cs_3419_);
                    if v_isShared_3433_ == 0 {
                        lean_ctor_set(v___x_3432_, 0, v___x_3437_);
                        v___x_3440_ = v___x_3432_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3437_);
                        v___x_3440_ = v_reuseFailAlloc_3441_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3442_ = lean_nat_dec_le(v___x_3436_, v___x_3436_);
                    if v___x_3442_ == 0 {
                        if v___x_3438_ == 0 {
                            lean_dec(v___x_3435_);
                            lean_dec_ref(v_cs_3419_);
                            if v_isShared_3433_ == 0 {
                                lean_ctor_set(v___x_3432_, 0, v___x_3437_);
                                v___x_3444_ = v___x_3432_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3437_);
                                v___x_3444_ = v_reuseFailAlloc_3445_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3432_);
                            v___x_3446_ = lean_usize_of_nat(v___x_3435_);
                            lean_dec(v___x_3435_);
                            v___x_3447_ = lean_usize_of_nat(v___x_3436_);
                            v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3419_, v___x_3446_, v___x_3447_, v___x_3437_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                            lean_dec_ref(v_cs_3419_);
                            return v___x_3448_;
                        }
                    } else {
                        lean_del_object(v___x_3432_);
                        v___x_3449_ = lean_usize_of_nat(v___x_3435_);
                        lean_dec(v___x_3435_);
                        v___x_3450_ = lean_usize_of_nat(v___x_3436_);
                        v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1_spec__4(v_cs_3419_, v___x_3449_, v___x_3450_, v___x_3437_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                        lean_dec_ref(v_cs_3419_);
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
                v___x_3460_ = lean_box(0);
                v___x_3461_ = lean_nat_dec_lt(v___x_3458_, v___x_3459_);
                if v___x_3461_ == 0 {
                    lean_dec(v___x_3458_);
                    lean_dec_ref(v_vs_3454_);
                    if v_isShared_3457_ == 0 {
                        lean_ctor_set_tag(v___x_3456_, 0);
                        lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                        v___x_3463_ = v___x_3456_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3465_ = lean_nat_dec_le(v___x_3459_, v___x_3459_);
                    if v___x_3465_ == 0 {
                        if v___x_3461_ == 0 {
                            lean_dec(v___x_3458_);
                            lean_dec_ref(v_vs_3454_);
                            if v_isShared_3457_ == 0 {
                                lean_ctor_set_tag(v___x_3456_, 0);
                                lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                                v___x_3467_ = v___x_3456_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
                                v___x_3467_ = v_reuseFailAlloc_3468_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3456_);
                            v___x_3469_ = lean_usize_of_nat(v___x_3458_);
                            lean_dec(v___x_3458_);
                            v___x_3470_ = lean_usize_of_nat(v___x_3459_);
                            v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3454_, v___x_3469_, v___x_3470_, v___x_3460_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                            lean_dec_ref(v_vs_3454_);
                            return v___x_3471_;
                        }
                    } else {
                        lean_del_object(v___x_3456_);
                        v___x_3472_ = lean_usize_of_nat(v___x_3458_);
                        lean_dec(v___x_3458_);
                        v___x_3473_ = lean_usize_of_nat(v___x_3459_);
                        v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_vs_3454_, v___x_3472_, v___x_3473_, v___x_3460_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
                        lean_dec_ref(v_vs_3454_);
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
    mut v_x_3476_: *mut LeanObject,
    mut v_x_3477_: *mut LeanObject,
    mut v_x_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9426__boxed_3485_: usize = 0;
    let mut v_x_9427__boxed_3486_: usize = 0;
    let mut v_res_3487_: *mut LeanObject = core::ptr::null_mut();
    v_x_9426__boxed_3485_ = lean_unbox_usize(v_x_3477_);
    lean_dec(v_x_3477_);
    v_x_9427__boxed_3486_ = lean_unbox_usize(v_x_3478_);
    lean_dec(v_x_3478_);
    v_res_3487_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_x_3476_, v_x_9426__boxed_3485_, v_x_9427__boxed_3486_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
    lean_dec(v___y_3483_);
    lean_dec_ref(v___y_3482_);
    lean_dec(v___y_3481_);
    lean_dec_ref(v___y_3480_);
    lean_dec(v___y_3479_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(
    mut v_t_3488_: *mut LeanObject,
    mut v_start_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v_root_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3500_: usize = 0;
    let mut v_tailOff_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: usize = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: usize = 0;
    let mut v___x_3534_: usize = 0;
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = lean_unsigned_to_nat(0);
                v___x_3497_ = lean_nat_dec_eq(v_start_3489_, v___x_3496_);
                if v___x_3497_ == 0 {
                    v_root_3498_ = lean_ctor_get(v_t_3488_, 0);
                    lean_inc_ref(v_root_3498_);
                    v_tail_3499_ = lean_ctor_get(v_t_3488_, 1);
                    lean_inc_ref(v_tail_3499_);
                    v_shift_3500_ = lean_ctor_get_usize(v_t_3488_, 4);
                    v_tailOff_3501_ = lean_ctor_get(v_t_3488_, 3);
                    lean_inc(v_tailOff_3501_);
                    lean_dec_ref(v_t_3488_);
                    v___x_3502_ = lean_nat_dec_le(v_tailOff_3501_, v_start_3489_);
                    if v___x_3502_ == 0 {
                        lean_dec(v_tailOff_3501_);
                        v___x_3503_ = lean_usize_of_nat(v_start_3489_);
                        v___x_3504_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__1(v_root_3498_, v___x_3503_, v_shift_3500_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                        if lean_obj_tag(v___x_3504_) == 0 {
                            v_isSharedCheck_3524_ = (!lean_is_exclusive(v___x_3504_)) as u8;
                            if v_isSharedCheck_3524_ == 0 {
                                v_unused_3525_ = lean_ctor_get(v___x_3504_, 0);
                                lean_dec(v_unused_3525_);
                                v___x_3506_ = v___x_3504_;
                                v_isShared_3507_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_3504_);
                                v___x_3506_ = lean_box(0);
                                v_isShared_3507_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_tail_3499_);
                            return v___x_3504_;
                        }
                    } else {
                        lean_dec_ref(v_root_3498_);
                        v___x_3526_ = lean_nat_sub(v_start_3489_, v_tailOff_3501_);
                        lean_dec(v_tailOff_3501_);
                        v___x_3527_ = lean_array_get_size(v_tail_3499_);
                        v___x_3528_ = lean_box(0);
                        v___x_3529_ = lean_nat_dec_lt(v___x_3526_, v___x_3527_);
                        if v___x_3529_ == 0 {
                            lean_dec(v___x_3526_);
                            lean_dec_ref(v_tail_3499_);
                            v___x_3530_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3530_, 0, v___x_3528_);
                            return v___x_3530_;
                        } else {
                            v___x_3531_ = lean_nat_dec_le(v___x_3527_, v___x_3527_);
                            if v___x_3531_ == 0 {
                                if v___x_3529_ == 0 {
                                    lean_dec(v___x_3526_);
                                    lean_dec_ref(v_tail_3499_);
                                    v___x_3532_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_3532_, 0, v___x_3528_);
                                    return v___x_3532_;
                                } else {
                                    v___x_3533_ = lean_usize_of_nat(v___x_3526_);
                                    lean_dec(v___x_3526_);
                                    v___x_3534_ = lean_usize_of_nat(v___x_3527_);
                                    v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3533_, v___x_3534_, v___x_3528_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                                    lean_dec_ref(v_tail_3499_);
                                    return v___x_3535_;
                                }
                            } else {
                                v___x_3536_ = lean_usize_of_nat(v___x_3526_);
                                lean_dec(v___x_3526_);
                                v___x_3537_ = lean_usize_of_nat(v___x_3527_);
                                v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3536_, v___x_3537_, v___x_3528_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                                lean_dec_ref(v_tail_3499_);
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
                v___x_3509_ = lean_box(0);
                v___x_3510_ = lean_nat_dec_lt(v___x_3496_, v___x_3508_);
                if v___x_3510_ == 0 {
                    lean_dec_ref(v_tail_3499_);
                    if v_isShared_3507_ == 0 {
                        lean_ctor_set(v___x_3506_, 0, v___x_3509_);
                        v___x_3512_ = v___x_3506_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3509_);
                        v___x_3512_ = v_reuseFailAlloc_3513_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3514_ = lean_nat_dec_le(v___x_3508_, v___x_3508_);
                    if v___x_3514_ == 0 {
                        if v___x_3510_ == 0 {
                            lean_dec_ref(v_tail_3499_);
                            if v_isShared_3507_ == 0 {
                                lean_ctor_set(v___x_3506_, 0, v___x_3509_);
                                v___x_3516_ = v___x_3506_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3509_);
                                v___x_3516_ = v_reuseFailAlloc_3517_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3506_);
                            v___x_3518_ = 0usize;
                            v___x_3519_ = lean_usize_of_nat(v___x_3508_);
                            v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3518_, v___x_3519_, v___x_3509_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                            lean_dec_ref(v_tail_3499_);
                            return v___x_3520_;
                        }
                    } else {
                        lean_del_object(v___x_3506_);
                        v___x_3521_ = 0usize;
                        v___x_3522_ = lean_usize_of_nat(v___x_3508_);
                        v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2(v_tail_3499_, v___x_3521_, v___x_3522_, v___x_3509_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
                        lean_dec_ref(v_tail_3499_);
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
    mut v_t_3540_: *mut LeanObject,
    mut v_start_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
    mut v___y_3547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3548_: *mut LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_t_3540_, v_start_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
    lean_dec(v___y_3546_);
    lean_dec_ref(v___y_3545_);
    lean_dec(v___y_3544_);
    lean_dec_ref(v___y_3543_);
    lean_dec(v___y_3542_);
    lean_dec(v_start_3541_);
    return v_res_3548_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(
    mut v_lctx_3549_: *mut LeanObject,
    mut v_start_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    v_decls_3557_ = lean_ctor_get(v_lctx_3549_, 1);
    lean_inc_ref(v_decls_3557_);
    lean_dec_ref(v_lctx_3549_);
    v___x_3558_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0(v_decls_3557_, v_start_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
    return v___x_3558_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0___boxed(
    mut v_lctx_3559_: *mut LeanObject,
    mut v_start_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3567_: *mut LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_3559_, v_start_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
    lean_dec(v___y_3565_);
    lean_dec_ref(v___y_3564_);
    lean_dec(v___y_3563_);
    lean_dec_ref(v___y_3562_);
    lean_dec(v___y_3561_);
    lean_dec(v_start_3560_);
    return v_res_3567_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(
    mut v_e_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3581_: u8 = 0;
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3587_: u8 = 0;
    let mut v_unused_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut v_mvarId_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3605_: u8 = 0;
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3611_: u8 = 0;
    let mut v_unused_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut v_a_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3568_) == 1 {
                    v_fvarId_3575_ = lean_ctor_get(v_e_3568_, 0);
                    lean_inc(v_fvarId_3575_);
                    lean_dec_ref_known(v_e_3568_, 1);
                    v___x_3576_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_3575_,
                        v___y_3570_,
                        v___y_3572_,
                        v___y_3573_,
                    );
                    if lean_obj_tag(v___x_3576_) == 0 {
                        v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
                        lean_inc(v_a_3577_);
                        lean_dec_ref_known(v___x_3576_, 1);
                        v___x_3578_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_visitLocalDecl___redArg(v_a_3577_, v___y_3569_);
                        v_isSharedCheck_3587_ = (!lean_is_exclusive(v___x_3578_)) as u8;
                        if v_isSharedCheck_3587_ == 0 {
                            v_unused_3588_ = lean_ctor_get(v___x_3578_, 0);
                            lean_dec(v_unused_3588_);
                            v___x_3580_ = v___x_3578_;
                            v_isShared_3581_ = v_isSharedCheck_3587_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3578_);
                            v___x_3580_ = lean_box(0);
                            v_isShared_3581_ = v_isSharedCheck_3587_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3589_ = lean_ctor_get(v___x_3576_, 0);
                        v_isSharedCheck_3596_ = (!lean_is_exclusive(v___x_3576_)) as u8;
                        if v_isSharedCheck_3596_ == 0 {
                            v___x_3591_ = v___x_3576_;
                            v_isShared_3592_ = v_isSharedCheck_3596_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3589_);
                            lean_dec(v___x_3576_);
                            v___x_3591_ = lean_box(0);
                            v_isShared_3592_ = v_isSharedCheck_3596_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_e_3568_) == 2 {
                        v_mvarId_3597_ = lean_ctor_get(v_e_3568_, 0);
                        lean_inc(v_mvarId_3597_);
                        lean_dec_ref_known(v_e_3568_, 1);
                        v___x_3598_ = l_Lean_MVarId_getDecl(
                            v_mvarId_3597_,
                            v___y_3570_,
                            v___y_3571_,
                            v___y_3572_,
                            v___y_3573_,
                        );
                        if lean_obj_tag(v___x_3598_) == 0 {
                            v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
                            lean_inc(v_a_3599_);
                            lean_dec_ref_known(v___x_3598_, 1);
                            v_lctx_3600_ = lean_ctor_get(v_a_3599_, 1);
                            lean_inc_ref(v_lctx_3600_);
                            lean_dec(v_a_3599_);
                            v___x_3601_ = lean_unsigned_to_nat(0);
                            v___x_3602_ = l_Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0(v_lctx_3600_, v___x_3601_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
                            if lean_obj_tag(v___x_3602_) == 0 {
                                v_isSharedCheck_3611_ = (!lean_is_exclusive(v___x_3602_)) as u8;
                                if v_isSharedCheck_3611_ == 0 {
                                    v_unused_3612_ = lean_ctor_get(v___x_3602_, 0);
                                    lean_dec(v_unused_3612_);
                                    v___x_3604_ = v___x_3602_;
                                    v_isShared_3605_ = v_isSharedCheck_3611_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_3602_);
                                    v___x_3604_ = lean_box(0);
                                    v_isShared_3605_ = v_isSharedCheck_3611_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_3613_ = lean_ctor_get(v___x_3602_, 0);
                                v_isSharedCheck_3620_ = (!lean_is_exclusive(v___x_3602_)) as u8;
                                if v_isSharedCheck_3620_ == 0 {
                                    v___x_3615_ = v___x_3602_;
                                    v_isShared_3616_ = v_isSharedCheck_3620_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3613_);
                                    lean_dec(v___x_3602_);
                                    v___x_3615_ = lean_box(0);
                                    v_isShared_3616_ = v_isSharedCheck_3620_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3621_ = lean_ctor_get(v___x_3598_, 0);
                            v_isSharedCheck_3628_ = (!lean_is_exclusive(v___x_3598_)) as u8;
                            if v_isSharedCheck_3628_ == 0 {
                                v___x_3623_ = v___x_3598_;
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3621_);
                                lean_dec(v___x_3598_);
                                v___x_3623_ = lean_box(0);
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        v___x_3629_ = l_Lean_Expr_hasFVar(v_e_3568_);
                        if v___x_3629_ == 0 {
                            v___x_3630_ = l_Lean_Expr_hasExprMVar(v_e_3568_);
                            lean_dec_ref(v_e_3568_);
                            v___x_3631_ = lean_box((v___x_3630_) as usize);
                            v___x_3632_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3632_, 0, v___x_3631_);
                            return v___x_3632_;
                        } else {
                            lean_dec_ref(v_e_3568_);
                            v___x_3633_ = lean_box((v___x_3629_) as usize);
                            v___x_3634_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3634_, 0, v___x_3633_);
                            return v___x_3634_;
                        }
                    }
                }
            }
            1 => {
                v___x_3582_ = 0;
                v___x_3583_ = lean_box((v___x_3582_) as usize);
                if v_isShared_3581_ == 0 {
                    lean_ctor_set(v___x_3580_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
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
                    v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
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
                v___x_3607_ = lean_box((v___x_3606_) as usize);
                if v_isShared_3605_ == 0 {
                    lean_ctor_set(v___x_3604_, 0, v___x_3607_);
                    v___x_3609_ = v___x_3604_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
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
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
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
                    v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
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
    mut v_e_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3642_: *mut LeanObject = core::ptr::null_mut();
    v_res_3642_ =
        l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___lam__0(
            v_e_3635_,
            v___y_3636_,
            v___y_3637_,
            v___y_3638_,
            v___y_3639_,
            v___y_3640_,
        );
    lean_dec(v___y_3640_);
    lean_dec_ref(v___y_3639_);
    lean_dec(v___y_3638_);
    lean_dec_ref(v___y_3637_);
    lean_dec(v___y_3636_);
    return v_res_3642_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(
    mut v_a_3643_: *mut LeanObject,
    mut v_x_3644_: *mut LeanObject,
) -> u8 {
    let mut v___x_3645_: u8 = 0;
    let mut v_key_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3644_) == 0 {
                    v___x_3645_ = 0;
                    return v___x_3645_;
                } else {
                    v_key_3646_ = lean_ctor_get(v_x_3644_, 0);
                    v_tail_3647_ = lean_ctor_get(v_x_3644_, 2);
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
    mut v_a_3650_: *mut LeanObject,
    mut v_x_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: u8 = 0;
    let mut v_r_3653_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_3650_, v_x_3651_);
    lean_dec(v_x_3651_);
    lean_dec_ref(v_a_3650_);
    v_r_3653_ = lean_box((v_res_3652_) as usize);
    return v_r_3653_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(
    mut v_x_3654_: *mut LeanObject,
    mut v_x_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3655_) == 0 {
                    return v_x_3654_;
                } else {
                    v_key_3656_ = lean_ctor_get(v_x_3655_, 0);
                    v_value_3657_ = lean_ctor_get(v_x_3655_, 1);
                    v_tail_3658_ = lean_ctor_get(v_x_3655_, 2);
                    v_isSharedCheck_3681_ = (!lean_is_exclusive(v_x_3655_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3660_ = v_x_3655_;
                        v_isShared_3661_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3658_);
                        lean_inc(v_value_3657_);
                        lean_inc(v_key_3656_);
                        lean_dec(v_x_3655_);
                        v___x_3660_ = lean_box(0);
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
                lean_inc(v___x_3675_);
                if v_isShared_3661_ == 0 {
                    lean_ctor_set(v___x_3660_, 2, v___x_3675_);
                    v___x_3677_ = v___x_3660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_key_3656_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_value_3657_);
                    lean_ctor_set(v_reuseFailAlloc_3680_, 2, v___x_3675_);
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
    mut v_i_3682_: *mut LeanObject,
    mut v_source_3683_: *mut LeanObject,
    mut v_target_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: u8 = 0;
    let mut v_es_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3685_ = lean_array_get_size(v_source_3683_);
                v___x_3686_ = lean_nat_dec_lt(v_i_3682_, v___x_3685_);
                if v___x_3686_ == 0 {
                    lean_dec_ref(v_source_3683_);
                    lean_dec(v_i_3682_);
                    return v_target_3684_;
                } else {
                    v_es_3687_ = lean_array_fget(v_source_3683_, v_i_3682_);
                    v___x_3688_ = lean_box(0);
                    v_source_3689_ = lean_array_fset(v_source_3683_, v_i_3682_, v___x_3688_);
                    v_target_3690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_target_3684_, v_es_3687_);
                    v___x_3691_ = lean_unsigned_to_nat(1);
                    v___x_3692_ = lean_nat_add(v_i_3682_, v___x_3691_);
                    lean_dec(v_i_3682_);
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
    mut v_data_3694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = lean_array_get_size(v_data_3694_);
    v___x_3696_ = lean_unsigned_to_nat(2);
    v_nbuckets_3697_ = lean_nat_mul(v___x_3695_, v___x_3696_);
    v___x_3698_ = lean_unsigned_to_nat(0);
    v___x_3699_ = lean_box(0);
    v___x_3700_ = lean_mk_array(v_nbuckets_3697_, v___x_3699_);
    v___x_3701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v___x_3698_, v_data_3694_, v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(
    mut v_a_3702_: *mut LeanObject,
    mut v_b_3703_: *mut LeanObject,
    mut v_x_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3704_) == 0 {
                    lean_dec(v_b_3703_);
                    lean_dec_ref(v_a_3702_);
                    return v_x_3704_;
                } else {
                    v_key_3705_ = lean_ctor_get(v_x_3704_, 0);
                    v_value_3706_ = lean_ctor_get(v_x_3704_, 1);
                    v_tail_3707_ = lean_ctor_get(v_x_3704_, 2);
                    v_isSharedCheck_3719_ = (!lean_is_exclusive(v_x_3704_)) as u8;
                    if v_isSharedCheck_3719_ == 0 {
                        v___x_3709_ = v_x_3704_;
                        v_isShared_3710_ = v_isSharedCheck_3719_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3707_);
                        lean_inc(v_value_3706_);
                        lean_inc(v_key_3705_);
                        lean_dec(v_x_3704_);
                        v___x_3709_ = lean_box(0);
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
                        lean_ctor_set(v___x_3709_, 2, v___x_3712_);
                        v___x_3714_ = v___x_3709_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_key_3705_);
                        lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_value_3706_);
                        lean_ctor_set(v_reuseFailAlloc_3715_, 2, v___x_3712_);
                        v___x_3714_ = v_reuseFailAlloc_3715_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3706_);
                    lean_dec(v_key_3705_);
                    if v_isShared_3710_ == 0 {
                        lean_ctor_set(v___x_3709_, 1, v_b_3703_);
                        lean_ctor_set(v___x_3709_, 0, v_a_3702_);
                        v___x_3717_ = v___x_3709_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3702_);
                        lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_b_3703_);
                        lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_tail_3707_);
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
    mut v_m_3720_: *mut LeanObject,
    mut v_a_3721_: *mut LeanObject,
    mut v_b_3722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v_val_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3723_ = lean_ctor_get(v_m_3720_, 0);
                v_buckets_3724_ = lean_ctor_get(v_m_3720_, 1);
                v_isSharedCheck_3767_ = (!lean_is_exclusive(v_m_3720_)) as u8;
                if v_isSharedCheck_3767_ == 0 {
                    v___x_3726_ = v_m_3720_;
                    v_isShared_3727_ = v_isSharedCheck_3767_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3724_);
                    lean_inc(v_size_3723_);
                    lean_dec(v_m_3720_);
                    v___x_3726_ = lean_box(0);
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
                    v___x_3743_ = lean_unsigned_to_nat(1);
                    v_size_x27_3744_ = lean_nat_add(v_size_3723_, v___x_3743_);
                    lean_dec(v_size_3723_);
                    lean_inc(v_bkt_3741_);
                    v___x_3745_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3745_, 0, v_a_3721_);
                    lean_ctor_set(v___x_3745_, 1, v_b_3722_);
                    lean_ctor_set(v___x_3745_, 2, v_bkt_3741_);
                    v_buckets_x27_3746_ =
                        lean_array_uset(v_buckets_3724_, v___x_3740_, v___x_3745_);
                    v___x_3747_ = lean_unsigned_to_nat(4);
                    v___x_3748_ = lean_nat_mul(v_size_x27_3744_, v___x_3747_);
                    v___x_3749_ = lean_unsigned_to_nat(3);
                    v___x_3750_ = lean_nat_div(v___x_3748_, v___x_3749_);
                    lean_dec(v___x_3748_);
                    v___x_3751_ = lean_array_get_size(v_buckets_x27_3746_);
                    v___x_3752_ = lean_nat_dec_le(v___x_3750_, v___x_3751_);
                    lean_dec(v___x_3750_);
                    if v___x_3752_ == 0 {
                        v_val_3753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_buckets_x27_3746_);
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set(v___x_3726_, 1, v_val_3753_);
                            lean_ctor_set(v___x_3726_, 0, v_size_x27_3744_);
                            v___x_3755_ = v___x_3726_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_size_x27_3744_);
                            lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_val_3753_);
                            v___x_3755_ = v_reuseFailAlloc_3756_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3727_ == 0 {
                            lean_ctor_set(v___x_3726_, 1, v_buckets_x27_3746_);
                            lean_ctor_set(v___x_3726_, 0, v_size_x27_3744_);
                            v___x_3758_ = v___x_3726_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_size_x27_3744_);
                            lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_buckets_x27_3746_);
                            v___x_3758_ = v_reuseFailAlloc_3759_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3741_);
                    v___x_3760_ = lean_box(0);
                    v_buckets_x27_3761_ =
                        lean_array_uset(v_buckets_3724_, v___x_3740_, v___x_3760_);
                    v___x_3762_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_3721_, v_b_3722_, v_bkt_3741_);
                    v___x_3763_ = lean_array_uset(v_buckets_x27_3761_, v___x_3740_, v___x_3762_);
                    if v_isShared_3727_ == 0 {
                        lean_ctor_set(v___x_3726_, 1, v___x_3763_);
                        v___x_3765_ = v___x_3726_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_size_3723_);
                        lean_ctor_set(v_reuseFailAlloc_3766_, 1, v___x_3763_);
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
    mut v_a_3768_: *mut LeanObject,
    mut v_x_3769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3769_) == 0 {
                    v___x_3770_ = lean_box(0);
                    return v___x_3770_;
                } else {
                    v_key_3771_ = lean_ctor_get(v_x_3769_, 0);
                    v_value_3772_ = lean_ctor_get(v_x_3769_, 1);
                    v_tail_3773_ = lean_ctor_get(v_x_3769_, 2);
                    v___x_3774_ = lean_expr_eqv(v_key_3771_, v_a_3768_);
                    if v___x_3774_ == 0 {
                        v_x_3769_ = v_tail_3773_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3772_);
                        v___x_3776_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3776_, 0, v_value_3772_);
                        return v___x_3776_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_a_3777_: *mut LeanObject,
    mut v_x_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3779_: *mut LeanObject = core::ptr::null_mut();
    v_res_3779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_3777_, v_x_3778_);
    lean_dec(v_x_3778_);
    lean_dec_ref(v_a_3777_);
    return v_res_3779_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(
    mut v_m_3780_: *mut LeanObject,
    mut v_a_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3782_ = lean_ctor_get(v_m_3780_, 1);
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
    mut v_m_3798_: *mut LeanObject,
    mut v_a_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3800_: *mut LeanObject = core::ptr::null_mut();
    v_res_3800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_3798_, v_a_3799_);
    lean_dec_ref(v_a_3799_);
    lean_dec_ref(v_m_3798_);
    return v_res_3800_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(
    mut v_g_3801_: *mut LeanObject,
    mut v_e_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
    mut v___y_3805_: *mut LeanObject,
    mut v___y_3806_: *mut LeanObject,
    mut v___y_3807_: *mut LeanObject,
    mut v___y_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut v_val_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = lean_st_ref_get(v_a_3803_);
                v___x_3820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v___x_3819_, v_e_3802_);
                lean_dec(v___x_3819_);
                if lean_obj_tag(v___x_3820_) == 0 {
                    lean_inc_ref(v_g_3801_);
                    lean_inc(v___y_3808_);
                    lean_inc_ref(v___y_3807_);
                    lean_inc(v___y_3806_);
                    lean_inc_ref(v___y_3805_);
                    lean_inc(v___y_3804_);
                    lean_inc_ref(v_e_3802_);
                    v___x_3821_ = lean_apply_7(
                        v_g_3801_,
                        v_e_3802_,
                        v___y_3804_,
                        v___y_3805_,
                        v___y_3806_,
                        v___y_3807_,
                        v___y_3808_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3821_) == 0 {
                        v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
                        lean_inc(v_a_3822_);
                        lean_dec_ref_known(v___x_3821_, 1);
                        v___x_3829_ = (lean_unbox(v_a_3822_) as u8);
                        lean_dec(v_a_3822_);
                        if v___x_3829_ == 0 {
                            lean_dec_ref(v_g_3801_);
                            v___x_3830_ = lean_box(0);
                            v_a_3811_ = v___x_3830_;
                            state = 1;
                            continue;
                        } else {
                            match lean_obj_tag(v_e_3802_) {
                                7 => {
                                    v_binderType_3831_ = lean_ctor_get(v_e_3802_, 1);
                                    v_body_3832_ = lean_ctor_get(v_e_3802_, 2);
                                    lean_inc_ref(v_body_3832_);
                                    lean_inc_ref(v_binderType_3831_);
                                    v_d_3824_ = v_binderType_3831_;
                                    v_b_3825_ = v_body_3832_;
                                    v___y_3826_ = v_a_3803_;
                                    state = 3;
                                    continue;
                                }
                                6 => {
                                    v_binderType_3833_ = lean_ctor_get(v_e_3802_, 1);
                                    v_body_3834_ = lean_ctor_get(v_e_3802_, 2);
                                    lean_inc_ref(v_body_3834_);
                                    lean_inc_ref(v_binderType_3833_);
                                    v_d_3824_ = v_binderType_3833_;
                                    v_b_3825_ = v_body_3834_;
                                    v___y_3826_ = v_a_3803_;
                                    state = 3;
                                    continue;
                                }
                                8 => {
                                    v_type_3835_ = lean_ctor_get(v_e_3802_, 1);
                                    v_value_3836_ = lean_ctor_get(v_e_3802_, 2);
                                    v_body_3837_ = lean_ctor_get(v_e_3802_, 3);
                                    lean_inc_ref(v_type_3835_);
                                    lean_inc_ref(v_g_3801_);
                                    v___x_3838_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_type_3835_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    if lean_obj_tag(v___x_3838_) == 0 {
                                        lean_dec_ref_known(v___x_3838_, 1);
                                        lean_inc_ref(v_value_3836_);
                                        lean_inc_ref(v_g_3801_);
                                        v___x_3839_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_value_3836_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                        if lean_obj_tag(v___x_3839_) == 0 {
                                            lean_dec_ref_known(v___x_3839_, 1);
                                            lean_inc_ref(v_body_3837_);
                                            v___x_3840_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_body_3837_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                            v___y_3817_ = v___x_3840_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_g_3801_);
                                            v___y_3817_ = v___x_3839_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_g_3801_);
                                        v___y_3817_ = v___x_3838_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                5 => {
                                    v_fn_3841_ = lean_ctor_get(v_e_3802_, 0);
                                    v_arg_3842_ = lean_ctor_get(v_e_3802_, 1);
                                    lean_inc_ref(v_fn_3841_);
                                    lean_inc_ref(v_g_3801_);
                                    v___x_3843_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_fn_3841_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    if lean_obj_tag(v___x_3843_) == 0 {
                                        lean_dec_ref_known(v___x_3843_, 1);
                                        lean_inc_ref(v_arg_3842_);
                                        v___x_3844_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_arg_3842_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                        v___y_3817_ = v___x_3844_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_g_3801_);
                                        v___y_3817_ = v___x_3843_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                10 => {
                                    v_expr_3845_ = lean_ctor_get(v_e_3802_, 1);
                                    lean_inc_ref(v_expr_3845_);
                                    v___x_3846_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_expr_3845_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    v___y_3817_ = v___x_3846_;
                                    state = 2;
                                    continue;
                                }
                                11 => {
                                    v_struct_3847_ = lean_ctor_get(v_e_3802_, 2);
                                    lean_inc_ref(v_struct_3847_);
                                    v___x_3848_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_struct_3847_, v_a_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                                    v___y_3817_ = v___x_3848_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    lean_dec_ref(v_g_3801_);
                                    v___x_3849_ = lean_box(0);
                                    v_a_3811_ = v___x_3849_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_3802_);
                        lean_dec_ref(v_g_3801_);
                        v_a_3850_ = lean_ctor_get(v___x_3821_, 0);
                        v_isSharedCheck_3857_ = (!lean_is_exclusive(v___x_3821_)) as u8;
                        if v_isSharedCheck_3857_ == 0 {
                            v___x_3852_ = v___x_3821_;
                            v_isShared_3853_ = v_isSharedCheck_3857_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3850_);
                            lean_dec(v___x_3821_);
                            v___x_3852_ = lean_box(0);
                            v_isShared_3853_ = v_isSharedCheck_3857_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3802_);
                    lean_dec_ref(v_g_3801_);
                    v_val_3858_ = lean_ctor_get(v___x_3820_, 0);
                    v_isSharedCheck_3865_ = (!lean_is_exclusive(v___x_3820_)) as u8;
                    if v_isSharedCheck_3865_ == 0 {
                        v___x_3860_ = v___x_3820_;
                        v_isShared_3861_ = v_isSharedCheck_3865_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_3858_);
                        lean_dec(v___x_3820_);
                        v___x_3860_ = lean_box(0);
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
                v___x_3815_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3815_, 0, v_a_3811_);
                return v___x_3815_;
            }
            2 => {
                if lean_obj_tag(v___y_3817_) == 0 {
                    v_a_3818_ = lean_ctor_get(v___y_3817_, 0);
                    lean_inc(v_a_3818_);
                    lean_dec_ref_known(v___y_3817_, 1);
                    v_a_3811_ = v_a_3818_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_e_3802_);
                    return v___y_3817_;
                }
            }
            3 => {
                lean_inc_ref(v_g_3801_);
                v___x_3827_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_d_3824_, v___y_3826_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                if lean_obj_tag(v___x_3827_) == 0 {
                    lean_dec_ref_known(v___x_3827_, 1);
                    v___x_3828_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3801_, v_b_3825_, v___y_3826_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
                    v___y_3817_ = v___x_3828_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_b_3825_);
                    lean_dec_ref(v_g_3801_);
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
                    v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
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
                    lean_ctor_set_tag(v___x_3860_, 0);
                    v___x_3863_ = v___x_3860_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_val_3858_);
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
    mut v_g_3866_: *mut LeanObject,
    mut v_e_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v_g_3866_, v_e_3867_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
    lean_dec(v___y_3873_);
    lean_dec_ref(v___y_3872_);
    lean_dec(v___y_3871_);
    lean_dec_ref(v___y_3870_);
    lean_dec(v___y_3869_);
    lean_dec(v_a_3868_);
    return v_res_3875_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0()
-> *mut LeanObject {
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    v___x_3876_ = lean_box(0);
    v___x_3877_ = lean_unsigned_to_nat(16);
    v___x_3878_ = lean_mk_array(v___x_3877_, v___x_3876_);
    return v___x_3878_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1()
-> *mut LeanObject {
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    v___x_3879_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0_once), _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__0);
    v___x_3880_ = lean_unsigned_to_nat(0);
    v___x_3881_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3881_, 0, v___x_3880_);
    lean_ctor_set(v___x_3881_, 1, v___x_3879_);
    return v___x_3881_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(
    mut v_e_3883_: *mut LeanObject,
    mut v_a_3884_: *mut LeanObject,
    mut v_a_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
    mut v_a_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1_once), _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__1);
                v___x_3891_ = lean_st_mk_ref(v___x_3890_);
                v___f_3892_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar___closed__2;
                v___x_3893_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1(v___f_3892_, v_e_3883_, v___x_3891_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
                if lean_obj_tag(v___x_3893_) == 0 {
                    v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
                    v_isSharedCheck_3902_ = (!lean_is_exclusive(v___x_3893_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3896_ = v___x_3893_;
                        v_isShared_3897_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3894_);
                        lean_dec(v___x_3893_);
                        v___x_3896_ = lean_box(0);
                        v_isShared_3897_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3891_);
                    return v___x_3893_;
                }
            }
            1 => {
                v___x_3898_ = lean_st_ref_get(v___x_3891_);
                lean_dec(v___x_3891_);
                lean_dec(v___x_3898_);
                if v_isShared_3897_ == 0 {
                    v___x_3900_ = v___x_3896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3894_);
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
    mut v_e_3903_: *mut LeanObject,
    mut v_a_3904_: *mut LeanObject,
    mut v_a_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_a_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3910_: *mut LeanObject = core::ptr::null_mut();
    v_res_3910_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(
        v_e_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_,
    );
    lean_dec(v_a_3908_);
    lean_dec_ref(v_a_3907_);
    lean_dec(v_a_3906_);
    lean_dec_ref(v_a_3905_);
    lean_dec(v_a_3904_);
    return v_res_3910_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(
    mut v_00_u03b2_3911_: *mut LeanObject,
    mut v_m_3912_: *mut LeanObject,
    mut v_a_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___redArg(v_m_3912_, v_a_3913_);
    return v___x_3914_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_3915_: *mut LeanObject,
    mut v_m_3916_: *mut LeanObject,
    mut v_a_3917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3918_: *mut LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2(v_00_u03b2_3915_, v_m_3916_, v_a_3917_);
    lean_dec_ref(v_a_3917_);
    lean_dec_ref(v_m_3916_);
    return v_res_3918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3(
    mut v_00_u03b2_3919_: *mut LeanObject,
    mut v_m_3920_: *mut LeanObject,
    mut v_a_3921_: *mut LeanObject,
    mut v_b_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3___redArg(v_m_3920_, v_a_3921_, v_b_3922_);
    return v___x_3923_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(
    mut v_00_u03b2_3924_: *mut LeanObject,
    mut v_a_3925_: *mut LeanObject,
    mut v_x_3926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v___x_3927_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___redArg(v_a_3925_, v_x_3926_);
    return v___x_3927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_3928_: *mut LeanObject,
    mut v_a_3929_: *mut LeanObject,
    mut v_x_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3931_: *mut LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__2_spec__6(v_00_u03b2_3928_, v_a_3929_, v_x_3930_);
    lean_dec(v_x_3930_);
    lean_dec_ref(v_a_3929_);
    return v_res_3931_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(
    mut v_00_u03b2_3932_: *mut LeanObject,
    mut v_a_3933_: *mut LeanObject,
    mut v_x_3934_: *mut LeanObject,
) -> u8 {
    let mut v___x_3935_: u8 = 0;
    v___x_3935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___redArg(v_a_3933_, v_x_3934_);
    return v___x_3935_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_x_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3939_: u8 = 0;
    let mut v_r_3940_: *mut LeanObject = core::ptr::null_mut();
    v_res_3939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__8(v_00_u03b2_3936_, v_a_3937_, v_x_3938_);
    lean_dec(v_x_3938_);
    lean_dec_ref(v_a_3937_);
    v_r_3940_ = lean_box((v_res_3939_) as usize);
    return v_r_3940_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9(
    mut v_00_u03b2_3941_: *mut LeanObject,
    mut v_data_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9___redArg(v_data_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10(
    mut v_00_u03b2_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_b_3946_: *mut LeanObject,
    mut v_x_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__10___redArg(v_a_3945_, v_b_3946_, v_x_3947_);
    return v___x_3948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(
    mut v_as_3949_: *mut LeanObject,
    mut v_i_3950_: usize,
    mut v_stop_3951_: usize,
    mut v_b_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___redArg(v_as_3949_, v_i_3950_, v_stop_3951_, v_b_3952_, v___y_3953_, v___y_3954_, v___y_3956_, v___y_3957_);
    return v___x_3959_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_as_3960_: *mut LeanObject,
    mut v_i_3961_: *mut LeanObject,
    mut v_stop_3962_: *mut LeanObject,
    mut v_b_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3970_: usize = 0;
    let mut v_stop_boxed_3971_: usize = 0;
    let mut v_res_3972_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3970_ = lean_unbox_usize(v_i_3961_);
    lean_dec(v_i_3961_);
    v_stop_boxed_3971_ = lean_unbox_usize(v_stop_3962_);
    lean_dec(v_stop_3962_);
    v_res_3972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__0_spec__0_spec__2_spec__6(v_as_3960_, v_i_boxed_3970_, v_stop_boxed_3971_, v_b_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
    lean_dec(v___y_3968_);
    lean_dec_ref(v___y_3967_);
    lean_dec(v___y_3966_);
    lean_dec_ref(v___y_3965_);
    lean_dec(v___y_3964_);
    lean_dec_ref(v_as_3960_);
    return v_res_3972_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13(
    mut v_00_u03b2_3973_: *mut LeanObject,
    mut v_i_3974_: *mut LeanObject,
    mut v_source_3975_: *mut LeanObject,
    mut v_target_3976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    v___x_3977_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13___redArg(v_i_3974_, v_source_3975_, v_target_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14(
    mut v_00_u03b2_3978_: *mut LeanObject,
    mut v_x_3979_: *mut LeanObject,
    mut v_x_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar_spec__1_spec__3_spec__9_spec__13_spec__14___redArg(v_x_3979_, v_x_3980_);
    return v___x_3981_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
    mut v_e_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: u8 = 0;
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4005_: u8 = 0;
    let mut v_unused_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3985_ = l_Lean_Expr_hasMVar(v_e_3982_);
                if v___x_3985_ == 0 {
                    v___x_3986_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3986_, 0, v_e_3982_);
                    return v___x_3986_;
                } else {
                    v___x_3987_ = lean_st_ref_get(v___y_3983_);
                    v_mctx_3988_ = lean_ctor_get(v___x_3987_, 0);
                    lean_inc_ref(v_mctx_3988_);
                    lean_dec(v___x_3987_);
                    v___x_3989_ = l_Lean_instantiateMVarsCore(v_mctx_3988_, v_e_3982_);
                    v_fst_3990_ = lean_ctor_get(v___x_3989_, 0);
                    lean_inc(v_fst_3990_);
                    v_snd_3991_ = lean_ctor_get(v___x_3989_, 1);
                    lean_inc(v_snd_3991_);
                    lean_dec_ref(v___x_3989_);
                    v___x_3992_ = lean_st_ref_take(v___y_3983_);
                    v_cache_3993_ = lean_ctor_get(v___x_3992_, 1);
                    v_zetaDeltaFVarIds_3994_ = lean_ctor_get(v___x_3992_, 2);
                    v_postponed_3995_ = lean_ctor_get(v___x_3992_, 3);
                    v_diag_3996_ = lean_ctor_get(v___x_3992_, 4);
                    v_isSharedCheck_4005_ = (!lean_is_exclusive(v___x_3992_)) as u8;
                    if v_isSharedCheck_4005_ == 0 {
                        v_unused_4006_ = lean_ctor_get(v___x_3992_, 0);
                        lean_dec(v_unused_4006_);
                        v___x_3998_ = v___x_3992_;
                        v_isShared_3999_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3996_);
                        lean_inc(v_postponed_3995_);
                        lean_inc(v_zetaDeltaFVarIds_3994_);
                        lean_inc(v_cache_3993_);
                        lean_dec(v___x_3992_);
                        v___x_3998_ = lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3999_ == 0 {
                    lean_ctor_set(v___x_3998_, 0, v_snd_3991_);
                    v___x_4001_ = v___x_3998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_snd_3991_);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_cache_3993_);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_zetaDeltaFVarIds_3994_);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_postponed_3995_);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_diag_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4002_ = lean_st_ref_set(v___y_3983_, v___x_4001_);
                v___x_4003_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4003_, 0, v_fst_3990_);
                return v___x_4003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg___boxed(
    mut v_e_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4010_: *mut LeanObject = core::ptr::null_mut();
    v_res_4010_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
        v_e_4007_,
        v___y_4008_,
    );
    lean_dec(v___y_4008_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(
    mut v_e_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
    mut v___y_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___redArg(
        v_e_4011_,
        v___y_4013_,
    );
    return v___x_4017_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0___boxed(
    mut v_e_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_Lean_instantiateMVars___at___00Lean_MVarId_assertAfter_x27_spec__0(
        v_e_4018_,
        v___y_4019_,
        v___y_4020_,
        v___y_4021_,
        v___y_4022_,
    );
    lean_dec(v___y_4022_);
    lean_dec_ref(v___y_4021_);
    lean_dec(v___y_4020_);
    lean_dec_ref(v___y_4019_);
    return v_res_4024_;
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27___lam__0(
    mut v_type_4025_: *mut LeanObject,
    mut v_fvarId_4026_: *mut LeanObject,
    mut v_mvarId_4027_: *mut LeanObject,
    mut v_userName_4028_: *mut LeanObject,
    mut v_val_4029_: *mut LeanObject,
    mut v___y_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_a_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4058_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
                lean_inc(v_a_4036_);
                lean_dec_ref(v___x_4035_);
                v___x_4037_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_4026_,
                    v___y_4030_,
                    v___y_4032_,
                    v___y_4033_,
                );
                if lean_obj_tag(v___x_4037_) == 0 {
                    v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
                    lean_inc(v_a_4038_);
                    lean_dec_ref_known(v___x_4037_, 1);
                    v___x_4039_ = lean_st_mk_ref(v_a_4038_);
                    lean_inc(v_a_4036_);
                    v___x_4040_ = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_assertAfter_x27_findMaxFVar(v_a_4036_, v___x_4039_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
                    if lean_obj_tag(v___x_4040_) == 0 {
                        lean_dec_ref_known(v___x_4040_, 1);
                        v___x_4041_ = lean_st_ref_get(v___x_4039_);
                        lean_dec(v___x_4039_);
                        v___x_4042_ = l_Lean_LocalDecl_fvarId(v___x_4041_);
                        lean_dec(v___x_4041_);
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
                        lean_dec(v___x_4039_);
                        lean_dec(v_a_4036_);
                        lean_dec_ref(v_val_4029_);
                        lean_dec(v_userName_4028_);
                        lean_dec(v_mvarId_4027_);
                        v_a_4044_ = lean_ctor_get(v___x_4040_, 0);
                        v_isSharedCheck_4051_ = (!lean_is_exclusive(v___x_4040_)) as u8;
                        if v_isSharedCheck_4051_ == 0 {
                            v___x_4046_ = v___x_4040_;
                            v_isShared_4047_ = v_isSharedCheck_4051_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4044_);
                            lean_dec(v___x_4040_);
                            v___x_4046_ = lean_box(0);
                            v_isShared_4047_ = v_isSharedCheck_4051_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4036_);
                    lean_dec_ref(v_val_4029_);
                    lean_dec(v_userName_4028_);
                    lean_dec(v_mvarId_4027_);
                    v_a_4052_ = lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4059_ = (!lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4059_ == 0 {
                        v___x_4054_ = v___x_4037_;
                        v_isShared_4055_ = v_isSharedCheck_4059_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4052_);
                        lean_dec(v___x_4037_);
                        v___x_4054_ = lean_box(0);
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
                    v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
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
                    v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
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
    mut v_type_4060_: *mut LeanObject,
    mut v_fvarId_4061_: *mut LeanObject,
    mut v_mvarId_4062_: *mut LeanObject,
    mut v_userName_4063_: *mut LeanObject,
    mut v_val_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4070_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4068_);
    lean_dec_ref(v___y_4067_);
    lean_dec(v___y_4066_);
    lean_dec_ref(v___y_4065_);
    return v_res_4070_;
}
pub unsafe fn l_Lean_MVarId_assertAfter_x27(
    mut v_mvarId_4071_: *mut LeanObject,
    mut v_fvarId_4072_: *mut LeanObject,
    mut v_userName_4073_: *mut LeanObject,
    mut v_type_4074_: *mut LeanObject,
    mut v_val_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_4071_);
    v___f_4081_ = lean_alloc_closure(
        l_Lean_MVarId_assertAfter_x27___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___f_4081_, 0, v_type_4074_);
    lean_closure_set(v___f_4081_, 1, v_fvarId_4072_);
    lean_closure_set(v___f_4081_, 2, v_mvarId_4071_);
    lean_closure_set(v___f_4081_, 3, v_userName_4073_);
    lean_closure_set(v___f_4081_, 4, v_val_4075_);
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
    mut v_mvarId_4083_: *mut LeanObject,
    mut v_fvarId_4084_: *mut LeanObject,
    mut v_userName_4085_: *mut LeanObject,
    mut v_type_4086_: *mut LeanObject,
    mut v_val_4087_: *mut LeanObject,
    mut v_a_4088_: *mut LeanObject,
    mut v_a_4089_: *mut LeanObject,
    mut v_a_4090_: *mut LeanObject,
    mut v_a_4091_: *mut LeanObject,
    mut v_a_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4093_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4091_);
    lean_dec_ref(v_a_4090_);
    lean_dec(v_a_4089_);
    lean_dec_ref(v_a_4088_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
    mut v_mvarId_4094_: *mut LeanObject,
    mut v_f_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4098_ = lean_st_ref_take(v___y_4096_);
                v_mctx_4099_ = lean_ctor_get(v___x_4098_, 0);
                v_cache_4100_ = lean_ctor_get(v___x_4098_, 1);
                v_zetaDeltaFVarIds_4101_ = lean_ctor_get(v___x_4098_, 2);
                v_postponed_4102_ = lean_ctor_get(v___x_4098_, 3);
                v_diag_4103_ = lean_ctor_get(v___x_4098_, 4);
                v_isSharedCheck_4114_ = (!lean_is_exclusive(v___x_4098_)) as u8;
                if v_isSharedCheck_4114_ == 0 {
                    v___x_4105_ = v___x_4098_;
                    v_isShared_4106_ = v_isSharedCheck_4114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4103_);
                    lean_inc(v_postponed_4102_);
                    lean_inc(v_zetaDeltaFVarIds_4101_);
                    lean_inc(v_cache_4100_);
                    lean_inc(v_mctx_4099_);
                    lean_dec(v___x_4098_);
                    v___x_4105_ = lean_box(0);
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
                    lean_ctor_set(v___x_4105_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4107_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_cache_4100_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_zetaDeltaFVarIds_4101_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 3, v_postponed_4102_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_diag_4103_);
                    v___x_4109_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4110_ = lean_st_ref_set(v___y_4096_, v___x_4109_);
                v___x_4111_ = lean_box(0);
                v___x_4112_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4112_, 0, v___x_4111_);
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(
    mut v_mvarId_4115_: *mut LeanObject,
    mut v_f_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
        v_mvarId_4115_,
        v_f_4116_,
        v___y_4117_,
    );
    lean_dec(v___y_4117_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(
    mut v_mvarId_4120_: *mut LeanObject,
    mut v_f_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(
        v_mvarId_4120_,
        v_f_4121_,
        v___y_4123_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(
    mut v_mvarId_4128_: *mut LeanObject,
    mut v_f_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4135_: *mut LeanObject = core::ptr::null_mut();
    v_res_4135_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(
        v_mvarId_4128_,
        v_f_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
    );
    lean_dec(v___y_4133_);
    lean_dec_ref(v___y_4132_);
    lean_dec(v___y_4131_);
    lean_dec_ref(v___y_4130_);
    return v_res_4135_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
    mut v_upperBound_4136_: *mut LeanObject,
    mut v_hs_4137_: *mut LeanObject,
    mut v_fst_4138_: *mut LeanObject,
    mut v___x_4139_: *mut LeanObject,
    mut v_a_4140_: *mut LeanObject,
    mut v_b_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4149_: u8 = 0;
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: u8 = 0;
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4147_ = lean_nat_dec_lt(v_a_4140_, v_upperBound_4136_);
                if v___x_4147_ == 0 {
                    lean_dec(v_a_4140_);
                    return v_b_4141_;
                } else {
                    v___x_4148_ = lean_array_fget_borrowed(v_hs_4137_, v_a_4140_);
                    v_kind_4149_ = lean_ctor_get_uint8(
                        v___x_4148_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v___x_4154_ = 0;
                    v___x_4155_ = l_Lean_instDecidableEqLocalDeclKind(v_kind_4149_, v___x_4154_);
                    if v___x_4155_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_4156_ = lean_unsigned_to_nat(0);
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
                v___x_4144_ = lean_unsigned_to_nat(1);
                v___x_4145_ = lean_nat_add(v_a_4140_, v___x_4144_);
                lean_dec(v_a_4140_);
                v_a_4140_ = v___x_4145_;
                v_b_4141_ = v_a_4143_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4151_ = lean_box(0);
                v___x_4152_ = lean_array_get_borrowed(v___x_4151_, v_fst_4138_, v_a_4140_);
                lean_inc(v___x_4152_);
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
    mut v_upperBound_4158_: *mut LeanObject,
    mut v_hs_4159_: *mut LeanObject,
    mut v_fst_4160_: *mut LeanObject,
    mut v___x_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_b_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4164_: *mut LeanObject = core::ptr::null_mut();
    v_res_4164_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(
            v_upperBound_4158_,
            v_hs_4159_,
            v_fst_4160_,
            v___x_4161_,
            v_a_4162_,
            v_b_4163_,
        );
    lean_dec(v___x_4161_);
    lean_dec_ref(v_fst_4160_);
    lean_dec_ref(v_hs_4159_);
    lean_dec(v_upperBound_4158_);
    return v_res_4164_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__0(
    mut v___x_4165_: *mut LeanObject,
    mut v_hs_4166_: *mut LeanObject,
    mut v_fst_4167_: *mut LeanObject,
    mut v___x_4168_: *mut LeanObject,
    mut v_lctx_4169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_4171_: *mut LeanObject,
    mut v_hs_4172_: *mut LeanObject,
    mut v_fst_4173_: *mut LeanObject,
    mut v___x_4174_: *mut LeanObject,
    mut v_lctx_4175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4176_: *mut LeanObject = core::ptr::null_mut();
    v_res_4176_ = l_Lean_MVarId_assertHypotheses___lam__0(
        v___x_4171_,
        v_hs_4172_,
        v_fst_4173_,
        v___x_4174_,
        v_lctx_4175_,
    );
    lean_dec_ref(v_fst_4173_);
    lean_dec_ref(v_hs_4172_);
    lean_dec(v___x_4171_);
    return v_res_4176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(
    mut v_as_4177_: *mut LeanObject,
    mut v_i_4178_: usize,
    mut v_stop_4179_: usize,
    mut v_b_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: usize = 0;
    let mut v___x_4183_: usize = 0;
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4187_: u8 = 0;
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4181_ = lean_usize_dec_eq(v_i_4178_, v_stop_4179_);
                if v___x_4181_ == 0 {
                    v___x_4182_ = 1usize;
                    v___x_4183_ = lean_usize_sub(v_i_4178_, v___x_4182_);
                    v___x_4184_ = lean_array_uget_borrowed(v_as_4177_, v___x_4183_);
                    v_userName_4185_ = lean_ctor_get(v___x_4184_, 0);
                    v_type_4186_ = lean_ctor_get(v___x_4184_, 1);
                    v_binderInfo_4187_ = lean_ctor_get_uint8(
                        v___x_4184_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_inc_ref(v_type_4186_);
                    lean_inc(v_userName_4185_);
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
    mut v_as_4190_: *mut LeanObject,
    mut v_i_4191_: *mut LeanObject,
    mut v_stop_4192_: *mut LeanObject,
    mut v_b_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4194_: usize = 0;
    let mut v_stop_boxed_4195_: usize = 0;
    let mut v_res_4196_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4194_ = lean_unbox_usize(v_i_4191_);
    lean_dec(v_i_4191_);
    v_stop_boxed_4195_ = lean_unbox_usize(v_stop_4192_);
    lean_dec(v_stop_4192_);
    v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(v_as_4190_, v_i_boxed_4194_, v_stop_boxed_4195_, v_b_4193_);
    lean_dec_ref(v_as_4190_);
    return v_res_4196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(
    mut v_as_4197_: *mut LeanObject,
    mut v_i_4198_: usize,
    mut v_stop_4199_: usize,
    mut v_b_4200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: usize = 0;
    let mut v___x_4206_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4201_ = lean_usize_dec_eq(v_i_4198_, v_stop_4199_);
                if v___x_4201_ == 0 {
                    v___x_4202_ = lean_array_uget_borrowed(v_as_4197_, v_i_4198_);
                    v_value_4203_ = lean_ctor_get(v___x_4202_, 2);
                    lean_inc_ref(v_value_4203_);
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
    mut v_as_4208_: *mut LeanObject,
    mut v_i_4209_: *mut LeanObject,
    mut v_stop_4210_: *mut LeanObject,
    mut v_b_4211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4212_: usize = 0;
    let mut v_stop_boxed_4213_: usize = 0;
    let mut v_res_4214_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4212_ = lean_unbox_usize(v_i_4209_);
    lean_dec(v_i_4209_);
    v_stop_boxed_4213_ = lean_unbox_usize(v_stop_4210_);
    lean_dec(v_stop_4210_);
    v_res_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_as_4208_, v_i_boxed_4212_, v_stop_boxed_4213_, v_b_4211_);
    lean_dec_ref(v_as_4208_);
    return v_res_4214_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___lam__1(
    mut v_mvarId_4215_: *mut LeanObject,
    mut v___x_4216_: *mut LeanObject,
    mut v___x_4217_: *mut LeanObject,
    mut v___x_4218_: u8,
    mut v_hs_4219_: *mut LeanObject,
    mut v___x_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_unused_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: usize = 0;
    let mut v___x_4259_: usize = 0;
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: usize = 0;
    let mut v___x_4262_: usize = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4267_: u8 = 0;
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4271_: u8 = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: usize = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_4215_);
                v___x_4247_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4215_,
                    v___x_4216_,
                    v___y_4221_,
                    v___y_4222_,
                    v___y_4223_,
                    v___y_4224_,
                );
                if lean_obj_tag(v___x_4247_) == 0 {
                    lean_dec_ref_known(v___x_4247_, 1);
                    lean_inc(v_mvarId_4215_);
                    v___x_4248_ = l_Lean_MVarId_getTag(
                        v_mvarId_4215_,
                        v___y_4221_,
                        v___y_4222_,
                        v___y_4223_,
                        v___y_4224_,
                    );
                    if lean_obj_tag(v___x_4248_) == 0 {
                        v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
                        lean_inc(v_a_4249_);
                        lean_dec_ref_known(v___x_4248_, 1);
                        lean_inc(v_mvarId_4215_);
                        v___x_4250_ = l_Lean_MVarId_getType(
                            v_mvarId_4215_,
                            v___y_4221_,
                            v___y_4222_,
                            v___y_4223_,
                            v___y_4224_,
                        );
                        if lean_obj_tag(v___x_4250_) == 0 {
                            v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
                            lean_inc(v_a_4251_);
                            lean_dec_ref_known(v___x_4250_, 1);
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
                            lean_dec(v_a_4249_);
                            lean_dec(v___x_4220_);
                            lean_dec_ref(v_hs_4219_);
                            lean_dec(v___x_4217_);
                            lean_dec(v_mvarId_4215_);
                            v_a_4276_ = lean_ctor_get(v___x_4250_, 0);
                            v_isSharedCheck_4283_ = (!lean_is_exclusive(v___x_4250_)) as u8;
                            if v_isSharedCheck_4283_ == 0 {
                                v___x_4278_ = v___x_4250_;
                                v_isShared_4279_ = v_isSharedCheck_4283_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4276_);
                                lean_dec(v___x_4250_);
                                v___x_4278_ = lean_box(0);
                                v_isShared_4279_ = v_isSharedCheck_4283_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4220_);
                        lean_dec_ref(v_hs_4219_);
                        lean_dec(v___x_4217_);
                        lean_dec(v_mvarId_4215_);
                        v_a_4284_ = lean_ctor_get(v___x_4248_, 0);
                        v_isSharedCheck_4291_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                        if v_isSharedCheck_4291_ == 0 {
                            v___x_4286_ = v___x_4248_;
                            v_isShared_4287_ = v_isSharedCheck_4291_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4284_);
                            lean_dec(v___x_4248_);
                            v___x_4286_ = lean_box(0);
                            v_isShared_4287_ = v_isSharedCheck_4291_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4220_);
                    lean_dec_ref(v_hs_4219_);
                    lean_dec(v___x_4217_);
                    lean_dec(v_mvarId_4215_);
                    v_a_4292_ = lean_ctor_get(v___x_4247_, 0);
                    v_isSharedCheck_4299_ = (!lean_is_exclusive(v___x_4247_)) as u8;
                    if v_isSharedCheck_4299_ == 0 {
                        v___x_4294_ = v___x_4247_;
                        v_isShared_4295_ = v_isSharedCheck_4299_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4292_);
                        lean_dec(v___x_4247_);
                        v___x_4294_ = lean_box(0);
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
                lean_dec_ref(v___x_4229_);
                v___x_4230_ = l_Lean_Expr_mvarId_x21(v___y_4227_);
                lean_dec_ref(v___y_4227_);
                v___x_4231_ = lean_box(0);
                v___x_4232_ = 1;
                lean_inc(v___x_4217_);
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
                if lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
                    lean_inc(v_a_4234_);
                    lean_dec_ref_known(v___x_4233_, 1);
                    v_fst_4235_ = lean_ctor_get(v_a_4234_, 0);
                    v_snd_4236_ = lean_ctor_get(v_a_4234_, 1);
                    lean_inc(v_fst_4235_);
                    v___f_4237_ = lean_alloc_closure(
                        l_Lean_MVarId_assertHypotheses___lam__0___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    lean_closure_set(v___f_4237_, 0, v___x_4217_);
                    lean_closure_set(v___f_4237_, 1, v_hs_4219_);
                    lean_closure_set(v___f_4237_, 2, v_fst_4235_);
                    lean_closure_set(v___f_4237_, 3, v___x_4220_);
                    lean_inc(v_snd_4236_);
                    v___x_4238_ = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(v_snd_4236_, v___f_4237_, v___y_4222_);
                    v_isSharedCheck_4245_ = (!lean_is_exclusive(v___x_4238_)) as u8;
                    if v_isSharedCheck_4245_ == 0 {
                        v_unused_4246_ = lean_ctor_get(v___x_4238_, 0);
                        lean_dec(v_unused_4246_);
                        v___x_4240_ = v___x_4238_;
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_4238_);
                        v___x_4240_ = lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4220_);
                    lean_dec_ref(v_hs_4219_);
                    lean_dec(v___x_4217_);
                    return v___x_4233_;
                }
            }
            2 => {
                if v_isShared_4241_ == 0 {
                    lean_ctor_set(v___x_4240_, 0, v_a_4234_);
                    v___x_4243_ = v___x_4240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4234_);
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
                if lean_obj_tag(v___x_4254_) == 0 {
                    v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
                    lean_inc(v_a_4255_);
                    lean_dec_ref_known(v___x_4254_, 1);
                    v___x_4256_ = lean_nat_dec_lt(v___x_4220_, v___x_4217_);
                    if v___x_4256_ == 0 {
                        lean_inc(v_a_4255_);
                        v___y_4227_ = v_a_4255_;
                        v___y_4228_ = v_a_4255_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4257_ = lean_nat_dec_le(v___x_4217_, v___x_4217_);
                        if v___x_4257_ == 0 {
                            if v___x_4256_ == 0 {
                                lean_inc(v_a_4255_);
                                v___y_4227_ = v_a_4255_;
                                v___y_4228_ = v_a_4255_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4258_ = 0usize;
                                v___x_4259_ = lean_usize_of_nat(v___x_4217_);
                                lean_inc(v_a_4255_);
                                v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_4219_, v___x_4258_, v___x_4259_, v_a_4255_);
                                v___y_4227_ = v_a_4255_;
                                v___y_4228_ = v___x_4260_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4261_ = 0usize;
                            v___x_4262_ = lean_usize_of_nat(v___x_4217_);
                            lean_inc(v_a_4255_);
                            v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(v_hs_4219_, v___x_4261_, v___x_4262_, v_a_4255_);
                            v___y_4227_ = v_a_4255_;
                            v___y_4228_ = v___x_4263_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4220_);
                    lean_dec_ref(v_hs_4219_);
                    lean_dec(v___x_4217_);
                    lean_dec(v_mvarId_4215_);
                    v_a_4264_ = lean_ctor_get(v___x_4254_, 0);
                    v_isSharedCheck_4271_ = (!lean_is_exclusive(v___x_4254_)) as u8;
                    if v_isSharedCheck_4271_ == 0 {
                        v___x_4266_ = v___x_4254_;
                        v_isShared_4267_ = v_isSharedCheck_4271_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4264_);
                        lean_dec(v___x_4254_);
                        v___x_4266_ = lean_box(0);
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
                    v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
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
                    v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
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
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
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
                    v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
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
    mut v_mvarId_4300_: *mut LeanObject,
    mut v___x_4301_: *mut LeanObject,
    mut v___x_4302_: *mut LeanObject,
    mut v___x_4303_: *mut LeanObject,
    mut v_hs_4304_: *mut LeanObject,
    mut v___x_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3359__boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3359__boxed_4311_ = (lean_unbox(v___x_4303_) as u8);
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
    lean_dec(v___y_4309_);
    lean_dec_ref(v___y_4308_);
    lean_dec(v___y_4307_);
    lean_dec_ref(v___y_4306_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_MVarId_assertHypotheses(
    mut v_mvarId_4318_: *mut LeanObject,
    mut v_hs_4319_: *mut LeanObject,
    mut v_a_4320_: *mut LeanObject,
    mut v_a_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: u8 = 0;
    v___x_4325_ = lean_array_get_size(v_hs_4319_);
    v___x_4326_ = lean_unsigned_to_nat(0);
    v___x_4327_ = lean_nat_dec_eq(v___x_4325_, v___x_4326_);
    if v___x_4327_ == 0 {
        let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
        v___x_4328_ = l_Lean_MVarId_assertHypotheses___closed__1;
        v___x_4329_ = lean_box((v___x_4327_) as usize);
        lean_inc(v_mvarId_4318_);
        v___f_4330_ = lean_alloc_closure(
            l_Lean_MVarId_assertHypotheses___lam__1___boxed as *mut core::ffi::c_void,
            11,
            6,
        );
        lean_closure_set(v___f_4330_, 0, v_mvarId_4318_);
        lean_closure_set(v___f_4330_, 1, v___x_4328_);
        lean_closure_set(v___f_4330_, 2, v___x_4325_);
        lean_closure_set(v___f_4330_, 3, v___x_4329_);
        lean_closure_set(v___f_4330_, 4, v_hs_4319_);
        lean_closure_set(v___f_4330_, 5, v___x_4326_);
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
        let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_hs_4319_);
        v___x_4332_ = l_Lean_MVarId_assertHypotheses___closed__2;
        v___x_4333_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4333_, 0, v___x_4332_);
        lean_ctor_set(v___x_4333_, 1, v_mvarId_4318_);
        v___x_4334_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4334_, 0, v___x_4333_);
        return v___x_4334_;
    }
}
pub unsafe fn l_Lean_MVarId_assertHypotheses___boxed(
    mut v_mvarId_4335_: *mut LeanObject,
    mut v_hs_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4342_: *mut LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_MVarId_assertHypotheses(
        v_mvarId_4335_,
        v_hs_4336_,
        v_a_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
    );
    lean_dec(v_a_4340_);
    lean_dec_ref(v_a_4339_);
    lean_dec(v_a_4338_);
    lean_dec_ref(v_a_4337_);
    return v_res_4342_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(
    mut v_upperBound_4343_: *mut LeanObject,
    mut v_hs_4344_: *mut LeanObject,
    mut v_fst_4345_: *mut LeanObject,
    mut v___x_4346_: *mut LeanObject,
    mut v_inst_4347_: *mut LeanObject,
    mut v_R_4348_: *mut LeanObject,
    mut v_a_4349_: *mut LeanObject,
    mut v_b_4350_: *mut LeanObject,
    mut v_c_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_upperBound_4353_: *mut LeanObject,
    mut v_hs_4354_: *mut LeanObject,
    mut v_fst_4355_: *mut LeanObject,
    mut v___x_4356_: *mut LeanObject,
    mut v_inst_4357_: *mut LeanObject,
    mut v_R_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
    mut v_b_4360_: *mut LeanObject,
    mut v_c_4361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4362_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___x_4356_);
    lean_dec_ref(v_fst_4355_);
    lean_dec_ref(v_hs_4354_);
    lean_dec(v_upperBound_4353_);
    return v_res_4362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Assert(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Assert(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Assert(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Assert(builtin);
}
