// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Acyclic Lean.Meta.Tactic.UnifyEq Lean.Meta.Constructions.SparseCasesOn Lean.Meta.Constructions.CtorIdx Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_append, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_maxRecDepthErrorMessage, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkCasesOnName;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_find_x3f};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isFVar, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkEM, l_Lean_mkFVar, l_Lean_mkNot,
    l_Lean_mkOr,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_inlineExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkFreshExprMVarAt, l_Lean_Meta_saveState___redArg, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdxName,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::Constructions::SparseCasesOn::{
    initialize_Lean_Meta_Constructions_SparseCasesOn, l_Lean_Meta_mkSparseCasesOn,
    runtime_initialize_Lean_Meta_Constructions_SparseCasesOn,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Tactic::Acyclic::{
    initialize_Lean_Meta_Tactic_Acyclic, l_Lean_MVarId_acyclic___boxed,
    runtime_initialize_Lean_Meta_Tactic_Acyclic,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_clear;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    l_Lean_Meta_FVarSubst_apply, l_Lean_Meta_FVarSubst_erase, l_Lean_Meta_FVarSubst_get,
    l_Lean_Meta_FVarSubst_insert,
};
use crate::r#gen::Lean::Meta::Tactic::Induction::{
    initialize_Lean_Meta_Tactic_Induction, l_Lean_MVarId_induction,
    runtime_initialize_Lean_Meta_Tactic_Induction,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_Meta_intro1Core, l_Lean_Meta_introNCore};
use crate::r#gen::Lean::Meta::Tactic::UnifyEq::{
    initialize_Lean_Meta_Tactic_UnifyEq, l_Lean_Meta_unifyEq_x3f,
    runtime_initialize_Lean_Meta_Tactic_UnifyEq,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_ensureAtMostOne, l_Lean_Meta_exactlyOne,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_saturate,
    l_Lean_Meta_throwNestedTacticEx___redArg, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::{
    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::Recognizers::{l_Lean_Expr_isEq, l_Lean_Expr_isHEq};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0_value: leanh::LeanStringObject<74> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 109, 112, 105, 108, 101, 32, 112, 97, 116, 116, 101, 114, 110, 32, 109, 97, 116, 99, 104, 105, 110, 103, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getInductiveUniverseAndParams___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [72, 69, 113, 0],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value
        ) as *mut leanh::LeanObject,
        13589827700912665667 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [114, 101, 102, 108, 0],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value_aux_0:
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
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value
        ) as *mut leanh::LeanObject,
        13589827700912665667 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value
        ) as *mut leanh::LeanObject,
        2990354745633524404 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5_value:
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
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value_aux_0:
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
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value
        ) as *mut leanh::LeanObject,
        13480818501600609864 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_withNewEqs___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_withNewEqs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_withNewEqs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116,
        97, 114, 103, 101, 116, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        32, 116, 97, 114, 103, 101, 116, 115, 32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32,
        98, 117, 116, 32, 109, 111, 116, 105, 118, 101, 32, 111, 110, 108, 121, 32, 116, 97, 107,
        101, 115, 32, 0,
    ],
};
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_generalizeTargetsEq___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 84, 97, 114, 103, 101, 116, 115, 0,
        ],
    };
static mut l_Lean_Meta_generalizeTargetsEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_generalizeTargetsEq___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_generalizeTargetsEq___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_generalizeTargetsEq___closed__0_value)
                as *mut leanh::LeanObject,
            6768243827530277195 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_generalizeTargetsEq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_generalizeTargetsEq___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value) as *mut leanh::LeanObject,13655884332201764339 as *mut leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 73, 110, 100, 105, 99, 101, 115, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value) as *mut leanh::LeanObject,6079868770024146942 as *mut leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [105, 110, 100, 101, 120, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 115, 79, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Cases_unifyEqs_x3f___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_acyclic___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Cases_unifyEqs_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 97, 115, 101, 115, 65, 117, 120, 79, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value) as *mut leanh::LeanObject,8726737828311244833 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [104, 97, 115, 78, 111, 116, 66, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value) as *mut leanh::LeanObject,6351501397486105973 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__0_value: leanh::LeanStringObject<39> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            110, 111, 116, 32, 97, 112, 112, 108, 105, 99, 97, 98, 108, 101, 32, 116, 111, 32, 116,
            104, 101, 32, 103, 105, 118, 101, 110, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105,
            115, 0,
        ],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Cases_cases___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Cases_cases___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Cases_cases___lam__0___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__5_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__6_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___lam__0___closed__8_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            97, 102, 116, 101, 114, 32, 103, 101, 110, 101, 114, 97, 108, 105, 122, 101, 73, 110,
            100, 105, 99, 101, 115, 10, 0,
        ],
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Cases_cases___lam__0___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Cases_cases___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Cases_cases___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Meta_Cases_cases___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Cases_cases___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Cases_cases___closed__0_value)
                as *mut leanh::LeanObject,
            13724376360221892060 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Cases_cases___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Cases_cases___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesRec___lam__0___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_casesRec___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesRec___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesAnd___lam__0___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [65, 110, 100, 0],
    };
static mut l_Lean_MVarId_casesAnd___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesAnd___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesAnd___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_casesAnd___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            9743492140944907313 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_casesAnd___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesAnd___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesAnd___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_casesAnd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_casesAnd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesAnd___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesAnd___closed__1_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32,
            111, 102, 32, 103, 111, 97, 108, 115, 0,
        ],
    };
static mut l_Lean_MVarId_casesAnd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesAnd___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_casesAnd___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_casesAnd___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_casesAnd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_casesAnd___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_MVarId_casesAnd___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_casesAnd___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_substEqs___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_substEqs___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_substEqs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_substEqs___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0_value:
    leanh::LeanStringObject<51> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        84, 97, 99, 116, 105, 99, 32, 96, 98, 121, 67, 97, 115, 101, 115, 96, 32, 102, 97, 105,
        108, 101, 100, 58, 32, 85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 101, 119,
        32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_byCases___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [104, 66, 121, 67, 97, 115, 101, 115, 0],
    };
static mut l_Lean_MVarId_byCases___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCases___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byCases___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_byCases___closed__0_value)
                as *mut leanh::LeanObject,
            7976273870079538797 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byCases___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCases___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byCases___closed__2_value: leanh::LeanStringObject<35> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            84, 97, 99, 116, 105, 99, 32, 96, 98, 121, 67, 97, 115, 101, 115, 96, 32, 102, 97, 105,
            108, 101, 100, 58, 32, 67, 97, 115, 105, 110, 103, 32, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_byCases___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCases___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byCases___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byCases___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_byCases___closed__4_value: leanh::LeanStringObject<40> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 108, 121, 32, 100, 105, 100, 32, 110,
            111, 116, 32, 121, 105, 101, 108, 100, 32, 116, 119, 111, 32, 115, 117, 98, 103, 111,
            97, 108, 115, 0,
        ],
    };
static mut l_Lean_MVarId_byCases___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCases___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byCases___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byCases___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_byCasesDec___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
    };
static mut l_Lean_MVarId_byCasesDec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCasesDec___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byCasesDec___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_byCasesDec___closed__0_value)
                as *mut leanh::LeanObject,
            4342836574150310743 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byCasesDec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCasesDec___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byCasesDec___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byCasesDec___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_byCasesDec___closed__3_value: leanh::LeanStringObject<38> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            84, 97, 99, 116, 105, 99, 32, 96, 98, 121, 67, 97, 115, 101, 115, 68, 101, 99, 96, 32,
            102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 115, 105, 110, 103, 32, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_byCasesDec___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byCasesDec___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byCasesDec___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byCasesDec___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__4_value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__5_value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___closed__0_value) as *mut leanh::LeanObject,7224461172283023161 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__4_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__5_value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10680097662825256564 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,13356237302220060405 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16024330702836273248 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__4_value) as *mut leanh::LeanObject,5474680779669491276 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,182551077741069625 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17535385057476482292 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12475335850064310261 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__4_value) as *mut leanh::LeanObject,4273396726122129853 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Cases_cases___lam__0___closed__5_value) as *mut leanh::LeanObject,12323279633044374500 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4231967549453985599 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(
    mut v_msgData_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = lean_st_ref_get(v___y_4636_);
    v_env_4639_ = leanh::lean_ctor_get(v___x_4638_, 0);
    leanh::lean_inc_ref(v_env_4639_);
    leanh::lean_dec(v___x_4638_);
    v___x_4640_ = lean_st_ref_get(v___y_4634_);
    v_mctx_4641_ = leanh::lean_ctor_get(v___x_4640_, 0);
    leanh::lean_inc_ref(v_mctx_4641_);
    leanh::lean_dec(v___x_4640_);
    v_lctx_4642_ = leanh::lean_ctor_get(v___y_4633_, 2);
    v_options_4643_ = leanh::lean_ctor_get(v___y_4635_, 2);
    leanh::lean_inc_ref(v_options_4643_);
    leanh::lean_inc_ref(v_lctx_4642_);
    v___x_4644_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4644_, 0, v_env_4639_);
    leanh::lean_ctor_set(v___x_4644_, 1, v_mctx_4641_);
    leanh::lean_ctor_set(v___x_4644_, 2, v_lctx_4642_);
    leanh::lean_ctor_set(v___x_4644_, 3, v_options_4643_);
    v___x_4645_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4645_, 0, v___x_4644_);
    leanh::lean_ctor_set(v___x_4645_, 1, v_msgData_4632_);
    v___x_4646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4646_, 0, v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(
    mut v_msgData_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
    leanh::lean_dec(v___y_4651_);
    leanh::lean_dec_ref(v___y_4650_);
    leanh::lean_dec(v___y_4649_);
    leanh::lean_dec_ref(v___y_4648_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(
    mut v_msg_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4665_: u8 = 0;
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4660_ = leanh::lean_ctor_get(v___y_4657_, 5);
                v___x_4661_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
                v_a_4662_ = leanh::lean_ctor_get(v___x_4661_, 0);
                v_isSharedCheck_4670_ = (!leanh::lean_is_exclusive(v___x_4661_)) as u8;
                if v_isSharedCheck_4670_ == 0 {
                    v___x_4664_ = v___x_4661_;
                    v_isShared_4665_ = v_isSharedCheck_4670_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4662_);
                    leanh::lean_dec(v___x_4661_);
                    v___x_4664_ = leanh::lean_box(0);
                    v_isShared_4665_ = v_isSharedCheck_4670_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4660_);
                v___x_4666_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4666_, 0, v_ref_4660_);
                leanh::lean_ctor_set(v___x_4666_, 1, v_a_4662_);
                if v_isShared_4665_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4664_, 1);
                    leanh::lean_ctor_set(v___x_4664_, 0, v___x_4666_);
                    v___x_4668_ = v___x_4664_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4666_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(
    mut v_msg_4671_: *mut leanh::LeanObject,
    mut v___y_4672_: *mut leanh::LeanObject,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
    mut v___y_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4677_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
    leanh::lean_dec(v___y_4675_);
    leanh::lean_dec_ref(v___y_4674_);
    leanh::lean_dec(v___y_4673_);
    leanh::lean_dec_ref(v___y_4672_);
    return v_res_4677_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0;
    v___x_4680_ = l_Lean_stringToMessageData(v___x_4679_);
    return v___x_4680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(
    mut v_type_4681_: *mut leanh::LeanObject,
    mut v_a_4682_: *mut leanh::LeanObject,
    mut v_a_4683_: *mut leanh::LeanObject,
    mut v_a_4684_: *mut leanh::LeanObject,
    mut v_a_4685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
    v___x_4688_ = l_Lean_indentExpr(v_type_4681_);
    v___x_4689_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4689_, 0, v___x_4687_);
    leanh::lean_ctor_set(v___x_4689_, 1, v___x_4688_);
    v___x_4690_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4689_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
    return v___x_4690_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(
    mut v_type_4691_: *mut leanh::LeanObject,
    mut v_a_4692_: *mut leanh::LeanObject,
    mut v_a_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
    mut v_a_4696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4697_ =
        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(
            v_type_4691_,
            v_a_4692_,
            v_a_4693_,
            v_a_4694_,
            v_a_4695_,
        );
    leanh::lean_dec(v_a_4695_);
    leanh::lean_dec_ref(v_a_4694_);
    leanh::lean_dec(v_a_4693_);
    leanh::lean_dec_ref(v_a_4692_);
    return v_res_4697_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(
    mut v_00_u03b1_4698_: *mut leanh::LeanObject,
    mut v_type_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ =
        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(
            v_type_4699_,
            v_a_4700_,
            v_a_4701_,
            v_a_4702_,
            v_a_4703_,
        );
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(
    mut v_00_u03b1_4706_: *mut leanh::LeanObject,
    mut v_type_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
    mut v_a_4709_: *mut leanh::LeanObject,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4713_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(
        v_00_u03b1_4706_,
        v_type_4707_,
        v_a_4708_,
        v_a_4709_,
        v_a_4710_,
        v_a_4711_,
    );
    leanh::lean_dec(v_a_4711_);
    leanh::lean_dec_ref(v_a_4710_);
    leanh::lean_dec(v_a_4709_);
    leanh::lean_dec_ref(v_a_4708_);
    return v_res_4713_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(
    mut v_00_u03b1_4714_: *mut leanh::LeanObject,
    mut v_msg_4715_: *mut leanh::LeanObject,
    mut v___y_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
    mut v___y_4718_: *mut leanh::LeanObject,
    mut v___y_4719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4721_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
    return v___x_4721_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(
    mut v_00_u03b1_4722_: *mut leanh::LeanObject,
    mut v_msg_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(v_00_u03b1_4722_, v_msg_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
    leanh::lean_dec(v___y_4727_);
    leanh::lean_dec_ref(v___y_4726_);
    leanh::lean_dec(v___y_4725_);
    leanh::lean_dec_ref(v___y_4724_);
    return v_res_4729_;
}
pub unsafe fn _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = leanh::lean_box(0);
    v_dummy_4731_ = l_Lean_Expr_sort___override(v___x_4730_);
    return v_dummy_4731_;
}
pub unsafe fn l_Lean_Meta_getInductiveUniverseAndParams(
    mut v_type_4732_: *mut leanh::LeanObject,
    mut v_a_4733_: *mut leanh::LeanObject,
    mut v_a_4734_: *mut leanh::LeanObject,
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_a_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut v_a_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4772_: u8 = 0;
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4738_ =
                    l_Lean_Meta_whnfD(v_type_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
                if leanh::lean_obj_tag(v___x_4738_) == 0 {
                    v_a_4739_ = leanh::lean_ctor_get(v___x_4738_, 0);
                    v_isSharedCheck_4768_ = (!leanh::lean_is_exclusive(v___x_4738_)) as u8;
                    if v_isSharedCheck_4768_ == 0 {
                        v___x_4741_ = v___x_4738_;
                        v_isShared_4742_ = v_isSharedCheck_4768_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4739_);
                        leanh::lean_dec(v___x_4738_);
                        v___x_4741_ = leanh::lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4768_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4769_ = leanh::lean_ctor_get(v___x_4738_, 0);
                    v_isSharedCheck_4776_ = (!leanh::lean_is_exclusive(v___x_4738_)) as u8;
                    if v_isSharedCheck_4776_ == 0 {
                        v___x_4771_ = v___x_4738_;
                        v_isShared_4772_ = v_isSharedCheck_4776_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4769_);
                        leanh::lean_dec(v___x_4738_);
                        v___x_4771_ = leanh::lean_box(0);
                        v_isShared_4772_ = v_isSharedCheck_4776_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4743_ = l_Lean_Expr_getAppFn(v_a_4739_);
                if leanh::lean_obj_tag(v___x_4743_) == 4 {
                    v_declName_4744_ = leanh::lean_ctor_get(v___x_4743_, 0);
                    leanh::lean_inc(v_declName_4744_);
                    v_us_4745_ = leanh::lean_ctor_get(v___x_4743_, 1);
                    leanh::lean_inc(v_us_4745_);
                    leanh::lean_dec_ref_known(v___x_4743_, 2);
                    v___x_4746_ = lean_st_ref_get(v_a_4736_);
                    v_env_4747_ = leanh::lean_ctor_get(v___x_4746_, 0);
                    leanh::lean_inc_ref(v_env_4747_);
                    leanh::lean_dec(v___x_4746_);
                    v___x_4748_ = 0;
                    v___x_4749_ =
                        l_Lean_Environment_find_x3f(v_env_4747_, v_declName_4744_, v___x_4748_);
                    if leanh::lean_obj_tag(v___x_4749_) == 0 {
                        leanh::lean_dec(v_us_4745_);
                        leanh::lean_del_object(v___x_4741_);
                        v___x_4750_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_4739_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
                        return v___x_4750_;
                    } else {
                        v_val_4751_ = leanh::lean_ctor_get(v___x_4749_, 0);
                        leanh::lean_inc(v_val_4751_);
                        leanh::lean_dec_ref_known(v___x_4749_, 1);
                        if leanh::lean_obj_tag(v_val_4751_) == 5 {
                            v_val_4752_ = leanh::lean_ctor_get(v_val_4751_, 0);
                            leanh::lean_inc_ref(v_val_4752_);
                            leanh::lean_dec_ref_known(v_val_4751_, 1);
                            v_numParams_4753_ = leanh::lean_ctor_get(v_val_4752_, 1);
                            leanh::lean_inc(v_numParams_4753_);
                            leanh::lean_dec_ref(v_val_4752_);
                            v_nargs_4754_ = l_Lean_Expr_getAppNumArgs(v_a_4739_);
                            v_dummy_4755_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getInductiveUniverseAndParams___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once
                                ),
                                _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0,
                            );
                            leanh::lean_inc(v_nargs_4754_);
                            v___x_4756_ = lean_mk_array(v_nargs_4754_, v_dummy_4755_);
                            v___x_4757_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4758_ = lean_nat_sub(v_nargs_4754_, v___x_4757_);
                            leanh::lean_dec(v_nargs_4754_);
                            v___x_4759_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_a_4739_,
                                v___x_4756_,
                                v___x_4758_,
                            );
                            v___x_4760_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4761_ = l_Array_extract___redArg(
                                v___x_4759_,
                                v___x_4760_,
                                v_numParams_4753_,
                            );
                            leanh::lean_dec_ref(v___x_4759_);
                            v___x_4762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4762_, 0, v_us_4745_);
                            leanh::lean_ctor_set(v___x_4762_, 1, v___x_4761_);
                            if v_isShared_4742_ == 0 {
                                leanh::lean_ctor_set(v___x_4741_, 0, v___x_4762_);
                                v___x_4764_ = v___x_4741_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4765_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
                                v___x_4764_ = v_reuseFailAlloc_4765_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_4751_);
                            leanh::lean_dec(v_us_4745_);
                            leanh::lean_del_object(v___x_4741_);
                            v___x_4766_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_4739_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
                            return v___x_4766_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4743_);
                    leanh::lean_del_object(v___x_4741_);
                    v___x_4767_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_4739_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
                    return v___x_4767_;
                }
            }
            2 => {
                return v___x_4764_;
            }
            3 => {
                if v_isShared_4772_ == 0 {
                    v___x_4774_ = v___x_4771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
                    v___x_4774_ = v_reuseFailAlloc_4775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getInductiveUniverseAndParams___boxed(
    mut v_type_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Meta_getInductiveUniverseAndParams(
        v_type_4777_,
        v_a_4778_,
        v_a_4779_,
        v_a_4780_,
        v_a_4781_,
    );
    leanh::lean_dec(v_a_4781_);
    leanh::lean_dec_ref(v_a_4780_);
    leanh::lean_dec(v_a_4779_);
    leanh::lean_dec_ref(v_a_4778_);
    return v_res_4783_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(
    mut v_lhs_4797_: *mut leanh::LeanObject,
    mut v_rhs_4798_: *mut leanh::LeanObject,
    mut v_a_4799_: *mut leanh::LeanObject,
    mut v_a_4800_: *mut leanh::LeanObject,
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4840_: u8 = 0;
    let mut v_a_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_a_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4864_: u8 = 0;
    let mut v_a_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4802_);
                leanh::lean_inc_ref(v_a_4801_);
                leanh::lean_inc(v_a_4800_);
                leanh::lean_inc_ref(v_a_4799_);
                leanh::lean_inc_ref(v_lhs_4797_);
                v___x_4804_ =
                    lean_infer_type(v_lhs_4797_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
                if leanh::lean_obj_tag(v___x_4804_) == 0 {
                    v_a_4805_ = leanh::lean_ctor_get(v___x_4804_, 0);
                    leanh::lean_inc(v_a_4805_);
                    leanh::lean_dec_ref_known(v___x_4804_, 1);
                    leanh::lean_inc(v_a_4802_);
                    leanh::lean_inc_ref(v_a_4801_);
                    leanh::lean_inc(v_a_4800_);
                    leanh::lean_inc_ref(v_a_4799_);
                    leanh::lean_inc_ref(v_rhs_4798_);
                    v___x_4806_ =
                        lean_infer_type(v_rhs_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
                    if leanh::lean_obj_tag(v___x_4806_) == 0 {
                        v_a_4807_ = leanh::lean_ctor_get(v___x_4806_, 0);
                        leanh::lean_inc(v_a_4807_);
                        leanh::lean_dec_ref_known(v___x_4806_, 1);
                        leanh::lean_inc(v_a_4805_);
                        v___x_4808_ = l_Lean_Meta_getLevel(
                            v_a_4805_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_,
                        );
                        if leanh::lean_obj_tag(v___x_4808_) == 0 {
                            v_a_4809_ = leanh::lean_ctor_get(v___x_4808_, 0);
                            leanh::lean_inc(v_a_4809_);
                            leanh::lean_dec_ref_known(v___x_4808_, 1);
                            leanh::lean_inc(v_a_4807_);
                            leanh::lean_inc(v_a_4805_);
                            v___x_4810_ = l_Lean_Meta_isExprDefEq(
                                v_a_4805_, v_a_4807_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_,
                            );
                            if leanh::lean_obj_tag(v___x_4810_) == 0 {
                                v_a_4811_ = leanh::lean_ctor_get(v___x_4810_, 0);
                                v_isSharedCheck_4840_ =
                                    (!leanh::lean_is_exclusive(v___x_4810_)) as u8;
                                if v_isSharedCheck_4840_ == 0 {
                                    v___x_4813_ = v___x_4810_;
                                    v_isShared_4814_ = v_isSharedCheck_4840_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4811_);
                                    leanh::lean_dec(v___x_4810_);
                                    v___x_4813_ = leanh::lean_box(0);
                                    v_isShared_4814_ = v_isSharedCheck_4840_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4809_);
                                leanh::lean_dec(v_a_4807_);
                                leanh::lean_dec(v_a_4805_);
                                leanh::lean_dec_ref(v_rhs_4798_);
                                leanh::lean_dec_ref(v_lhs_4797_);
                                v_a_4841_ = leanh::lean_ctor_get(v___x_4810_, 0);
                                v_isSharedCheck_4848_ =
                                    (!leanh::lean_is_exclusive(v___x_4810_)) as u8;
                                if v_isSharedCheck_4848_ == 0 {
                                    v___x_4843_ = v___x_4810_;
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4841_);
                                    leanh::lean_dec(v___x_4810_);
                                    v___x_4843_ = leanh::lean_box(0);
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4807_);
                            leanh::lean_dec(v_a_4805_);
                            leanh::lean_dec_ref(v_rhs_4798_);
                            leanh::lean_dec_ref(v_lhs_4797_);
                            v_a_4849_ = leanh::lean_ctor_get(v___x_4808_, 0);
                            v_isSharedCheck_4856_ =
                                (!leanh::lean_is_exclusive(v___x_4808_)) as u8;
                            if v_isSharedCheck_4856_ == 0 {
                                v___x_4851_ = v___x_4808_;
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4849_);
                                leanh::lean_dec(v___x_4808_);
                                v___x_4851_ = leanh::lean_box(0);
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4805_);
                        leanh::lean_dec_ref(v_rhs_4798_);
                        leanh::lean_dec_ref(v_lhs_4797_);
                        v_a_4857_ = leanh::lean_ctor_get(v___x_4806_, 0);
                        v_isSharedCheck_4864_ =
                            (!leanh::lean_is_exclusive(v___x_4806_)) as u8;
                        if v_isSharedCheck_4864_ == 0 {
                            v___x_4859_ = v___x_4806_;
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4857_);
                            leanh::lean_dec(v___x_4806_);
                            v___x_4859_ = leanh::lean_box(0);
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_rhs_4798_);
                    leanh::lean_dec_ref(v_lhs_4797_);
                    v_a_4865_ = leanh::lean_ctor_get(v___x_4804_, 0);
                    v_isSharedCheck_4872_ = (!leanh::lean_is_exclusive(v___x_4804_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v___x_4867_ = v___x_4804_;
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4865_);
                        leanh::lean_dec(v___x_4804_);
                        v___x_4867_ = leanh::lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4872_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4815_ = (leanh::lean_unbox(v_a_4811_) as u8);
                leanh::lean_dec(v_a_4811_);
                if v___x_4815_ == 0 {
                    v___x_4816_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
                    v___x_4817_ = leanh::lean_box(0);
                    v___x_4818_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4818_, 0, v_a_4809_);
                    leanh::lean_ctor_set(v___x_4818_, 1, v___x_4817_);
                    leanh::lean_inc_ref(v___x_4818_);
                    v___x_4819_ = l_Lean_mkConst(v___x_4816_, v___x_4818_);
                    leanh::lean_inc_ref(v_lhs_4797_);
                    leanh::lean_inc(v_a_4805_);
                    v___x_4820_ =
                        l_Lean_mkApp4(v___x_4819_, v_a_4805_, v_lhs_4797_, v_a_4807_, v_rhs_4798_);
                    v___x_4821_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
                    v___x_4822_ = l_Lean_mkConst(v___x_4821_, v___x_4818_);
                    v___x_4823_ = l_Lean_mkAppB(v___x_4822_, v_a_4805_, v_lhs_4797_);
                    v___x_4824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4824_, 0, v___x_4820_);
                    leanh::lean_ctor_set(v___x_4824_, 1, v___x_4823_);
                    if v_isShared_4814_ == 0 {
                        leanh::lean_ctor_set(v___x_4813_, 0, v___x_4824_);
                        v___x_4826_ = v___x_4813_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4824_);
                        v___x_4826_ = v_reuseFailAlloc_4827_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4807_);
                    v___x_4828_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
                    v___x_4829_ = leanh::lean_box(0);
                    v___x_4830_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4830_, 0, v_a_4809_);
                    leanh::lean_ctor_set(v___x_4830_, 1, v___x_4829_);
                    leanh::lean_inc_ref(v___x_4830_);
                    v___x_4831_ = l_Lean_mkConst(v___x_4828_, v___x_4830_);
                    leanh::lean_inc_ref(v_lhs_4797_);
                    leanh::lean_inc(v_a_4805_);
                    v___x_4832_ = l_Lean_mkApp3(v___x_4831_, v_a_4805_, v_lhs_4797_, v_rhs_4798_);
                    v___x_4833_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
                    v___x_4834_ = l_Lean_mkConst(v___x_4833_, v___x_4830_);
                    v___x_4835_ = l_Lean_mkAppB(v___x_4834_, v_a_4805_, v_lhs_4797_);
                    v___x_4836_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4836_, 0, v___x_4832_);
                    leanh::lean_ctor_set(v___x_4836_, 1, v___x_4835_);
                    if v_isShared_4814_ == 0 {
                        leanh::lean_ctor_set(v___x_4813_, 0, v___x_4836_);
                        v___x_4838_ = v___x_4813_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4839_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
                        v___x_4838_ = v_reuseFailAlloc_4839_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4826_;
            }
            3 => {
                return v___x_4838_;
            }
            4 => {
                if v_isShared_4844_ == 0 {
                    v___x_4846_ = v___x_4843_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
                    v___x_4846_ = v_reuseFailAlloc_4847_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4846_;
            }
            6 => {
                if v_isShared_4852_ == 0 {
                    v___x_4854_ = v___x_4851_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
                    v___x_4854_ = v_reuseFailAlloc_4855_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4854_;
            }
            8 => {
                if v_isShared_4860_ == 0 {
                    v___x_4862_ = v___x_4859_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
                    v___x_4862_ = v_reuseFailAlloc_4863_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4862_;
            }
            10 => {
                if v_isShared_4868_ == 0 {
                    v___x_4870_ = v___x_4867_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
                    v___x_4870_ = v_reuseFailAlloc_4871_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(
    mut v_lhs_4873_: *mut leanh::LeanObject,
    mut v_rhs_4874_: *mut leanh::LeanObject,
    mut v_a_4875_: *mut leanh::LeanObject,
    mut v_a_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_a_4878_: *mut leanh::LeanObject,
    mut v_a_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4880_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(
        v_lhs_4873_,
        v_rhs_4874_,
        v_a_4875_,
        v_a_4876_,
        v_a_4877_,
        v_a_4878_,
    );
    leanh::lean_dec(v_a_4878_);
    leanh::lean_dec_ref(v_a_4877_);
    leanh::lean_dec(v_a_4876_);
    leanh::lean_dec_ref(v_a_4875_);
    return v_res_4880_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(
    mut v_k_4881_: *mut leanh::LeanObject,
    mut v_b_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
    mut v___y_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4886_);
    leanh::lean_inc_ref(v___y_4885_);
    leanh::lean_inc(v___y_4884_);
    leanh::lean_inc_ref(v___y_4883_);
    v___x_4888_ = leanh::lean_apply_6(
        v_k_4881_,
        v_b_4882_,
        v___y_4883_,
        v___y_4884_,
        v___y_4885_,
        v___y_4886_,
        leanh::lean_box(0),
    );
    return v___x_4888_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_4889_: *mut leanh::LeanObject,
    mut v_b_4890_: *mut leanh::LeanObject,
    mut v___y_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
    mut v___y_4895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4896_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_4889_, v_b_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
    leanh::lean_dec(v___y_4894_);
    leanh::lean_dec_ref(v___y_4893_);
    leanh::lean_dec(v___y_4892_);
    leanh::lean_dec_ref(v___y_4891_);
    return v_res_4896_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(
    mut v_name_4897_: *mut leanh::LeanObject,
    mut v_bi_4898_: u8,
    mut v_type_4899_: *mut leanh::LeanObject,
    mut v_k_4900_: *mut leanh::LeanObject,
    mut v_kind_4901_: u8,
    mut v___y_4902_: *mut leanh::LeanObject,
    mut v___y_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut v_a_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4920_: u8 = 0;
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4907_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_4907_, 0, v_k_4900_);
                v___x_4908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_4897_,
                    v_bi_4898_,
                    v_type_4899_,
                    v___f_4907_,
                    v_kind_4901_,
                    v___y_4902_,
                    v___y_4903_,
                    v___y_4904_,
                    v___y_4905_,
                );
                if leanh::lean_obj_tag(v___x_4908_) == 0 {
                    v_a_4909_ = leanh::lean_ctor_get(v___x_4908_, 0);
                    v_isSharedCheck_4916_ = (!leanh::lean_is_exclusive(v___x_4908_)) as u8;
                    if v_isSharedCheck_4916_ == 0 {
                        v___x_4911_ = v___x_4908_;
                        v_isShared_4912_ = v_isSharedCheck_4916_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4909_);
                        leanh::lean_dec(v___x_4908_);
                        v___x_4911_ = leanh::lean_box(0);
                        v_isShared_4912_ = v_isSharedCheck_4916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4917_ = leanh::lean_ctor_get(v___x_4908_, 0);
                    v_isSharedCheck_4924_ = (!leanh::lean_is_exclusive(v___x_4908_)) as u8;
                    if v_isSharedCheck_4924_ == 0 {
                        v___x_4919_ = v___x_4908_;
                        v_isShared_4920_ = v_isSharedCheck_4924_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4917_);
                        leanh::lean_dec(v___x_4908_);
                        v___x_4919_ = leanh::lean_box(0);
                        v_isShared_4920_ = v_isSharedCheck_4924_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4912_ == 0 {
                    v___x_4914_ = v___x_4911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
                    v___x_4914_ = v_reuseFailAlloc_4915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4914_;
            }
            3 => {
                if v_isShared_4920_ == 0 {
                    v___x_4922_ = v___x_4919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
                    v___x_4922_ = v_reuseFailAlloc_4923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(
    mut v_name_4925_: *mut leanh::LeanObject,
    mut v_bi_4926_: *mut leanh::LeanObject,
    mut v_type_4927_: *mut leanh::LeanObject,
    mut v_k_4928_: *mut leanh::LeanObject,
    mut v_kind_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
    mut v___y_4933_: *mut leanh::LeanObject,
    mut v___y_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4935_: u8 = 0;
    let mut v_kind_boxed_4936_: u8 = 0;
    let mut v_res_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4935_ = (leanh::lean_unbox(v_bi_4926_) as u8);
    v_kind_boxed_4936_ = (leanh::lean_unbox(v_kind_4929_) as u8);
    v_res_4937_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_4925_, v_bi_boxed_4935_, v_type_4927_, v_k_4928_, v_kind_boxed_4936_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
    leanh::lean_dec(v___y_4933_);
    leanh::lean_dec_ref(v___y_4932_);
    leanh::lean_dec(v___y_4931_);
    leanh::lean_dec_ref(v___y_4930_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(
    mut v_name_4938_: *mut leanh::LeanObject,
    mut v_type_4939_: *mut leanh::LeanObject,
    mut v_k_4940_: *mut leanh::LeanObject,
    mut v___y_4941_: *mut leanh::LeanObject,
    mut v___y_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4946_: u8 = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = 0;
    v___x_4947_ = 0;
    v___x_4948_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_4938_, v___x_4946_, v_type_4939_, v_k_4940_, v___x_4947_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
    return v___x_4948_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(
    mut v_name_4949_: *mut leanh::LeanObject,
    mut v_type_4950_: *mut leanh::LeanObject,
    mut v_k_4951_: *mut leanh::LeanObject,
    mut v___y_4952_: *mut leanh::LeanObject,
    mut v___y_4953_: *mut leanh::LeanObject,
    mut v___y_4954_: *mut leanh::LeanObject,
    mut v___y_4955_: *mut leanh::LeanObject,
    mut v___y_4956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_4949_, v_type_4950_, v_k_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    leanh::lean_dec(v___y_4955_);
    leanh::lean_dec_ref(v___y_4954_);
    leanh::lean_dec(v___y_4953_);
    leanh::lean_dec_ref(v___y_4952_);
    return v_res_4957_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(
    mut v_i_4958_: *mut leanh::LeanObject,
    mut v_newEqs_4959_: *mut leanh::LeanObject,
    mut v_newRefls_4960_: *mut leanh::LeanObject,
    mut v_snd_4961_: *mut leanh::LeanObject,
    mut v_targets_4962_: *mut leanh::LeanObject,
    mut v_targetsNew_4963_: *mut leanh::LeanObject,
    mut v_k_4964_: *mut leanh::LeanObject,
    mut v_newEq_4965_: *mut leanh::LeanObject,
    mut v___y_4966_: *mut leanh::LeanObject,
    mut v___y_4967_: *mut leanh::LeanObject,
    mut v___y_4968_: *mut leanh::LeanObject,
    mut v___y_4969_: *mut leanh::LeanObject,
    mut v___y_4970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4971_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(
        v_i_4958_,
        v_newEqs_4959_,
        v_newRefls_4960_,
        v_snd_4961_,
        v_targets_4962_,
        v_targetsNew_4963_,
        v_k_4964_,
        v_newEq_4965_,
        v___y_4966_,
        v___y_4967_,
        v___y_4968_,
        v___y_4969_,
    );
    leanh::lean_dec(v___y_4969_);
    leanh::lean_dec_ref(v___y_4968_);
    leanh::lean_dec(v___y_4967_);
    leanh::lean_dec_ref(v___y_4966_);
    leanh::lean_dec(v_i_4958_);
    return v_res_4971_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(
    mut v_targets_4975_: *mut leanh::LeanObject,
    mut v_targetsNew_4976_: *mut leanh::LeanObject,
    mut v_k_4977_: *mut leanh::LeanObject,
    mut v_i_4978_: *mut leanh::LeanObject,
    mut v_newEqs_4979_: *mut leanh::LeanObject,
    mut v_newRefls_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
    mut v_a_4982_: *mut leanh::LeanObject,
    mut v_a_4983_: *mut leanh::LeanObject,
    mut v_a_4984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = lean_array_get_size(v_targets_4975_);
                v___x_4987_ = lean_nat_dec_lt(v_i_4978_, v___x_4986_);
                if v___x_4987_ == 0 {
                    leanh::lean_dec(v_i_4978_);
                    leanh::lean_dec_ref(v_targetsNew_4976_);
                    leanh::lean_dec_ref(v_targets_4975_);
                    leanh::lean_inc(v_a_4984_);
                    leanh::lean_inc_ref(v_a_4983_);
                    leanh::lean_inc(v_a_4982_);
                    leanh::lean_inc_ref(v_a_4981_);
                    v___x_4988_ = leanh::lean_apply_7(
                        v_k_4977_,
                        v_newEqs_4979_,
                        v_newRefls_4980_,
                        v_a_4981_,
                        v_a_4982_,
                        v_a_4983_,
                        v_a_4984_,
                        leanh::lean_box(0),
                    );
                    return v___x_4988_;
                } else {
                    v___x_4989_ = l_Lean_instInhabitedExpr;
                    v___x_4990_ = lean_array_get_borrowed(v___x_4989_, v_targets_4975_, v_i_4978_);
                    v___x_4991_ =
                        lean_array_get_borrowed(v___x_4989_, v_targetsNew_4976_, v_i_4978_);
                    leanh::lean_inc(v___x_4991_);
                    leanh::lean_inc(v___x_4990_);
                    v___x_4992_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(
                        v___x_4990_,
                        v___x_4991_,
                        v_a_4981_,
                        v_a_4982_,
                        v_a_4983_,
                        v_a_4984_,
                    );
                    if leanh::lean_obj_tag(v___x_4992_) == 0 {
                        v_a_4993_ = leanh::lean_ctor_get(v___x_4992_, 0);
                        leanh::lean_inc(v_a_4993_);
                        leanh::lean_dec_ref_known(v___x_4992_, 1);
                        v_fst_4994_ = leanh::lean_ctor_get(v_a_4993_, 0);
                        leanh::lean_inc(v_fst_4994_);
                        v_snd_4995_ = leanh::lean_ctor_get(v_a_4993_, 1);
                        leanh::lean_inc(v_snd_4995_);
                        leanh::lean_dec(v_a_4993_);
                        v___f_4996_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 7);
                        leanh::lean_closure_set(v___f_4996_, 0, v_i_4978_);
                        leanh::lean_closure_set(v___f_4996_, 1, v_newEqs_4979_);
                        leanh::lean_closure_set(v___f_4996_, 2, v_newRefls_4980_);
                        leanh::lean_closure_set(v___f_4996_, 3, v_snd_4995_);
                        leanh::lean_closure_set(v___f_4996_, 4, v_targets_4975_);
                        leanh::lean_closure_set(v___f_4996_, 5, v_targetsNew_4976_);
                        leanh::lean_closure_set(v___f_4996_, 6, v_k_4977_);
                        v___x_4997_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1;
                        v___x_4998_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_4997_, v_fst_4994_, v___f_4996_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
                        return v___x_4998_;
                    } else {
                        leanh::lean_dec_ref(v_newRefls_4980_);
                        leanh::lean_dec_ref(v_newEqs_4979_);
                        leanh::lean_dec(v_i_4978_);
                        leanh::lean_dec_ref(v_k_4977_);
                        leanh::lean_dec_ref(v_targetsNew_4976_);
                        leanh::lean_dec_ref(v_targets_4975_);
                        v_a_4999_ = leanh::lean_ctor_get(v___x_4992_, 0);
                        v_isSharedCheck_5006_ =
                            (!leanh::lean_is_exclusive(v___x_4992_)) as u8;
                        if v_isSharedCheck_5006_ == 0 {
                            v___x_5001_ = v___x_4992_;
                            v_isShared_5002_ = v_isSharedCheck_5006_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4999_);
                            leanh::lean_dec(v___x_4992_);
                            v___x_5001_ = leanh::lean_box(0);
                            v_isShared_5002_ = v_isSharedCheck_5006_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5002_ == 0 {
                    v___x_5004_ = v___x_5001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
                    v___x_5004_ = v_reuseFailAlloc_5005_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(
    mut v_i_5007_: *mut leanh::LeanObject,
    mut v_newEqs_5008_: *mut leanh::LeanObject,
    mut v_newRefls_5009_: *mut leanh::LeanObject,
    mut v_snd_5010_: *mut leanh::LeanObject,
    mut v_targets_5011_: *mut leanh::LeanObject,
    mut v_targetsNew_5012_: *mut leanh::LeanObject,
    mut v_k_5013_: *mut leanh::LeanObject,
    mut v_newEq_5014_: *mut leanh::LeanObject,
    mut v___y_5015_: *mut leanh::LeanObject,
    mut v___y_5016_: *mut leanh::LeanObject,
    mut v___y_5017_: *mut leanh::LeanObject,
    mut v___y_5018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5020_ = leanh::lean_unsigned_to_nat(1);
    v___x_5021_ = lean_nat_add(v_i_5007_, v___x_5020_);
    v___x_5022_ = lean_array_push(v_newEqs_5008_, v_newEq_5014_);
    v___x_5023_ = lean_array_push(v_newRefls_5009_, v_snd_5010_);
    v___x_5024_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(
        v_targets_5011_,
        v_targetsNew_5012_,
        v_k_5013_,
        v___x_5021_,
        v___x_5022_,
        v___x_5023_,
        v___y_5015_,
        v___y_5016_,
        v___y_5017_,
        v___y_5018_,
    );
    return v___x_5024_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(
    mut v_targets_5025_: *mut leanh::LeanObject,
    mut v_targetsNew_5026_: *mut leanh::LeanObject,
    mut v_k_5027_: *mut leanh::LeanObject,
    mut v_i_5028_: *mut leanh::LeanObject,
    mut v_newEqs_5029_: *mut leanh::LeanObject,
    mut v_newRefls_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
    mut v_a_5032_: *mut leanh::LeanObject,
    mut v_a_5033_: *mut leanh::LeanObject,
    mut v_a_5034_: *mut leanh::LeanObject,
    mut v_a_5035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5036_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(
        v_targets_5025_,
        v_targetsNew_5026_,
        v_k_5027_,
        v_i_5028_,
        v_newEqs_5029_,
        v_newRefls_5030_,
        v_a_5031_,
        v_a_5032_,
        v_a_5033_,
        v_a_5034_,
    );
    leanh::lean_dec(v_a_5034_);
    leanh::lean_dec_ref(v_a_5033_);
    leanh::lean_dec(v_a_5032_);
    leanh::lean_dec_ref(v_a_5031_);
    return v_res_5036_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(
    mut v_00_u03b1_5037_: *mut leanh::LeanObject,
    mut v_targets_5038_: *mut leanh::LeanObject,
    mut v_targetsNew_5039_: *mut leanh::LeanObject,
    mut v_k_5040_: *mut leanh::LeanObject,
    mut v_i_5041_: *mut leanh::LeanObject,
    mut v_newEqs_5042_: *mut leanh::LeanObject,
    mut v_newRefls_5043_: *mut leanh::LeanObject,
    mut v_a_5044_: *mut leanh::LeanObject,
    mut v_a_5045_: *mut leanh::LeanObject,
    mut v_a_5046_: *mut leanh::LeanObject,
    mut v_a_5047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5049_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(
        v_targets_5038_,
        v_targetsNew_5039_,
        v_k_5040_,
        v_i_5041_,
        v_newEqs_5042_,
        v_newRefls_5043_,
        v_a_5044_,
        v_a_5045_,
        v_a_5046_,
        v_a_5047_,
    );
    return v___x_5049_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(
    mut v_00_u03b1_5050_: *mut leanh::LeanObject,
    mut v_targets_5051_: *mut leanh::LeanObject,
    mut v_targetsNew_5052_: *mut leanh::LeanObject,
    mut v_k_5053_: *mut leanh::LeanObject,
    mut v_i_5054_: *mut leanh::LeanObject,
    mut v_newEqs_5055_: *mut leanh::LeanObject,
    mut v_newRefls_5056_: *mut leanh::LeanObject,
    mut v_a_5057_: *mut leanh::LeanObject,
    mut v_a_5058_: *mut leanh::LeanObject,
    mut v_a_5059_: *mut leanh::LeanObject,
    mut v_a_5060_: *mut leanh::LeanObject,
    mut v_a_5061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5062_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(
        v_00_u03b1_5050_,
        v_targets_5051_,
        v_targetsNew_5052_,
        v_k_5053_,
        v_i_5054_,
        v_newEqs_5055_,
        v_newRefls_5056_,
        v_a_5057_,
        v_a_5058_,
        v_a_5059_,
        v_a_5060_,
    );
    leanh::lean_dec(v_a_5060_);
    leanh::lean_dec_ref(v_a_5059_);
    leanh::lean_dec(v_a_5058_);
    leanh::lean_dec_ref(v_a_5057_);
    return v_res_5062_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(
    mut v_00_u03b1_5063_: *mut leanh::LeanObject,
    mut v_name_5064_: *mut leanh::LeanObject,
    mut v_bi_5065_: u8,
    mut v_type_5066_: *mut leanh::LeanObject,
    mut v_k_5067_: *mut leanh::LeanObject,
    mut v_kind_5068_: u8,
    mut v___y_5069_: *mut leanh::LeanObject,
    mut v___y_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
    mut v___y_5072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_5064_, v_bi_5065_, v_type_5066_, v_k_5067_, v_kind_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
    return v___x_5074_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(
    mut v_00_u03b1_5075_: *mut leanh::LeanObject,
    mut v_name_5076_: *mut leanh::LeanObject,
    mut v_bi_5077_: *mut leanh::LeanObject,
    mut v_type_5078_: *mut leanh::LeanObject,
    mut v_k_5079_: *mut leanh::LeanObject,
    mut v_kind_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
    mut v___y_5082_: *mut leanh::LeanObject,
    mut v___y_5083_: *mut leanh::LeanObject,
    mut v___y_5084_: *mut leanh::LeanObject,
    mut v___y_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_5086_: u8 = 0;
    let mut v_kind_boxed_5087_: u8 = 0;
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5086_ = (leanh::lean_unbox(v_bi_5077_) as u8);
    v_kind_boxed_5087_ = (leanh::lean_unbox(v_kind_5080_) as u8);
    v_res_5088_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_5075_, v_name_5076_, v_bi_boxed_5086_, v_type_5078_, v_k_5079_, v_kind_boxed_5087_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
    leanh::lean_dec(v___y_5084_);
    leanh::lean_dec_ref(v___y_5083_);
    leanh::lean_dec(v___y_5082_);
    leanh::lean_dec_ref(v___y_5081_);
    return v_res_5088_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(
    mut v_00_u03b1_5089_: *mut leanh::LeanObject,
    mut v_name_5090_: *mut leanh::LeanObject,
    mut v_type_5091_: *mut leanh::LeanObject,
    mut v_k_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
    mut v___y_5095_: *mut leanh::LeanObject,
    mut v___y_5096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5098_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_5090_, v_type_5091_, v_k_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
    return v___x_5098_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(
    mut v_00_u03b1_5099_: *mut leanh::LeanObject,
    mut v_name_5100_: *mut leanh::LeanObject,
    mut v_type_5101_: *mut leanh::LeanObject,
    mut v_k_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5108_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(v_00_u03b1_5099_, v_name_5100_, v_type_5101_, v_k_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    leanh::lean_dec(v___y_5106_);
    leanh::lean_dec_ref(v___y_5105_);
    leanh::lean_dec(v___y_5104_);
    leanh::lean_dec_ref(v___y_5103_);
    return v_res_5108_;
}
pub unsafe fn l_Lean_Meta_withNewEqs___redArg(
    mut v_targets_5111_: *mut leanh::LeanObject,
    mut v_targetsNew_5112_: *mut leanh::LeanObject,
    mut v_k_5113_: *mut leanh::LeanObject,
    mut v_a_5114_: *mut leanh::LeanObject,
    mut v_a_5115_: *mut leanh::LeanObject,
    mut v_a_5116_: *mut leanh::LeanObject,
    mut v_a_5117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5119_ = leanh::lean_unsigned_to_nat(0);
    v___x_5120_ = l_Lean_Meta_withNewEqs___redArg___closed__0;
    v___x_5121_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(
        v_targets_5111_,
        v_targetsNew_5112_,
        v_k_5113_,
        v___x_5119_,
        v___x_5120_,
        v___x_5120_,
        v_a_5114_,
        v_a_5115_,
        v_a_5116_,
        v_a_5117_,
    );
    return v___x_5121_;
}
pub unsafe fn l_Lean_Meta_withNewEqs___redArg___boxed(
    mut v_targets_5122_: *mut leanh::LeanObject,
    mut v_targetsNew_5123_: *mut leanh::LeanObject,
    mut v_k_5124_: *mut leanh::LeanObject,
    mut v_a_5125_: *mut leanh::LeanObject,
    mut v_a_5126_: *mut leanh::LeanObject,
    mut v_a_5127_: *mut leanh::LeanObject,
    mut v_a_5128_: *mut leanh::LeanObject,
    mut v_a_5129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Lean_Meta_withNewEqs___redArg(
        v_targets_5122_,
        v_targetsNew_5123_,
        v_k_5124_,
        v_a_5125_,
        v_a_5126_,
        v_a_5127_,
        v_a_5128_,
    );
    leanh::lean_dec(v_a_5128_);
    leanh::lean_dec_ref(v_a_5127_);
    leanh::lean_dec(v_a_5126_);
    leanh::lean_dec_ref(v_a_5125_);
    return v_res_5130_;
}
pub unsafe fn l_Lean_Meta_withNewEqs(
    mut v_00_u03b1_5131_: *mut leanh::LeanObject,
    mut v_targets_5132_: *mut leanh::LeanObject,
    mut v_targetsNew_5133_: *mut leanh::LeanObject,
    mut v_k_5134_: *mut leanh::LeanObject,
    mut v_a_5135_: *mut leanh::LeanObject,
    mut v_a_5136_: *mut leanh::LeanObject,
    mut v_a_5137_: *mut leanh::LeanObject,
    mut v_a_5138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5140_ = l_Lean_Meta_withNewEqs___redArg(
        v_targets_5132_,
        v_targetsNew_5133_,
        v_k_5134_,
        v_a_5135_,
        v_a_5136_,
        v_a_5137_,
        v_a_5138_,
    );
    return v___x_5140_;
}
pub unsafe fn l_Lean_Meta_withNewEqs___boxed(
    mut v_00_u03b1_5141_: *mut leanh::LeanObject,
    mut v_targets_5142_: *mut leanh::LeanObject,
    mut v_targetsNew_5143_: *mut leanh::LeanObject,
    mut v_k_5144_: *mut leanh::LeanObject,
    mut v_a_5145_: *mut leanh::LeanObject,
    mut v_a_5146_: *mut leanh::LeanObject,
    mut v_a_5147_: *mut leanh::LeanObject,
    mut v_a_5148_: *mut leanh::LeanObject,
    mut v_a_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ = l_Lean_Meta_withNewEqs(
        v_00_u03b1_5141_,
        v_targets_5142_,
        v_targetsNew_5143_,
        v_k_5144_,
        v_a_5145_,
        v_a_5146_,
        v_a_5147_,
        v_a_5148_,
    );
    leanh::lean_dec(v_a_5148_);
    leanh::lean_dec_ref(v_a_5147_);
    leanh::lean_dec(v_a_5146_);
    leanh::lean_dec_ref(v_a_5145_);
    return v_res_5150_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(
    mut v_k_5151_: *mut leanh::LeanObject,
    mut v_b_5152_: *mut leanh::LeanObject,
    mut v_c_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_5157_);
    leanh::lean_inc_ref(v___y_5156_);
    leanh::lean_inc(v___y_5155_);
    leanh::lean_inc_ref(v___y_5154_);
    v___x_5159_ = leanh::lean_apply_7(
        v_k_5151_,
        v_b_5152_,
        v_c_5153_,
        v___y_5154_,
        v___y_5155_,
        v___y_5156_,
        v___y_5157_,
        leanh::lean_box(0),
    );
    return v___x_5159_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(
    mut v_k_5160_: *mut leanh::LeanObject,
    mut v_b_5161_: *mut leanh::LeanObject,
    mut v_c_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
    mut v___y_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
    mut v___y_5167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_5160_, v_b_5161_, v_c_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
    leanh::lean_dec(v___y_5166_);
    leanh::lean_dec_ref(v___y_5165_);
    leanh::lean_dec(v___y_5164_);
    leanh::lean_dec_ref(v___y_5163_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(
    mut v_type_5169_: *mut leanh::LeanObject,
    mut v_k_5170_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5171_: u8,
    mut v_whnfType_5172_: u8,
    mut v___y_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
    mut v___y_5176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5187_: u8 = 0;
    let mut v_a_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5191_: u8 = 0;
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5178_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_5178_, 0, v_k_5170_);
                v___x_5179_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_5169_,
                    v___f_5178_,
                    v_cleanupAnnotations_5171_,
                    v_whnfType_5172_,
                    v___y_5173_,
                    v___y_5174_,
                    v___y_5175_,
                    v___y_5176_,
                );
                if leanh::lean_obj_tag(v___x_5179_) == 0 {
                    v_a_5180_ = leanh::lean_ctor_get(v___x_5179_, 0);
                    v_isSharedCheck_5187_ = (!leanh::lean_is_exclusive(v___x_5179_)) as u8;
                    if v_isSharedCheck_5187_ == 0 {
                        v___x_5182_ = v___x_5179_;
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5180_);
                        leanh::lean_dec(v___x_5179_);
                        v___x_5182_ = leanh::lean_box(0);
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5188_ = leanh::lean_ctor_get(v___x_5179_, 0);
                    v_isSharedCheck_5195_ = (!leanh::lean_is_exclusive(v___x_5179_)) as u8;
                    if v_isSharedCheck_5195_ == 0 {
                        v___x_5190_ = v___x_5179_;
                        v_isShared_5191_ = v_isSharedCheck_5195_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5188_);
                        leanh::lean_dec(v___x_5179_);
                        v___x_5190_ = leanh::lean_box(0);
                        v_isShared_5191_ = v_isSharedCheck_5195_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5183_ == 0 {
                    v___x_5185_ = v___x_5182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
                    v___x_5185_ = v_reuseFailAlloc_5186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5185_;
            }
            3 => {
                if v_isShared_5191_ == 0 {
                    v___x_5193_ = v___x_5190_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
                    v___x_5193_ = v_reuseFailAlloc_5194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(
    mut v_type_5196_: *mut leanh::LeanObject,
    mut v_k_5197_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5198_: *mut leanh::LeanObject,
    mut v_whnfType_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
    mut v___y_5202_: *mut leanh::LeanObject,
    mut v___y_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5205_: u8 = 0;
    let mut v_whnfType_boxed_5206_: u8 = 0;
    let mut v_res_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5205_ = (leanh::lean_unbox(v_cleanupAnnotations_5198_) as u8);
    v_whnfType_boxed_5206_ = (leanh::lean_unbox(v_whnfType_5199_) as u8);
    v_res_5207_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(
            v_type_5196_,
            v_k_5197_,
            v_cleanupAnnotations_boxed_5205_,
            v_whnfType_boxed_5206_,
            v___y_5200_,
            v___y_5201_,
            v___y_5202_,
            v___y_5203_,
        );
    leanh::lean_dec(v___y_5203_);
    leanh::lean_dec_ref(v___y_5202_);
    leanh::lean_dec(v___y_5201_);
    leanh::lean_dec_ref(v___y_5200_);
    return v_res_5207_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(
    mut v_00_u03b1_5208_: *mut leanh::LeanObject,
    mut v_type_5209_: *mut leanh::LeanObject,
    mut v_k_5210_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5211_: u8,
    mut v_whnfType_5212_: u8,
    mut v___y_5213_: *mut leanh::LeanObject,
    mut v___y_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(
            v_type_5209_,
            v_k_5210_,
            v_cleanupAnnotations_5211_,
            v_whnfType_5212_,
            v___y_5213_,
            v___y_5214_,
            v___y_5215_,
            v___y_5216_,
        );
    return v___x_5218_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(
    mut v_00_u03b1_5219_: *mut leanh::LeanObject,
    mut v_type_5220_: *mut leanh::LeanObject,
    mut v_k_5221_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5222_: *mut leanh::LeanObject,
    mut v_whnfType_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
    mut v___y_5225_: *mut leanh::LeanObject,
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5229_: u8 = 0;
    let mut v_whnfType_boxed_5230_: u8 = 0;
    let mut v_res_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5229_ = (leanh::lean_unbox(v_cleanupAnnotations_5222_) as u8);
    v_whnfType_boxed_5230_ = (leanh::lean_unbox(v_whnfType_5223_) as u8);
    v_res_5231_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(
            v_00_u03b1_5219_,
            v_type_5220_,
            v_k_5221_,
            v_cleanupAnnotations_boxed_5229_,
            v_whnfType_boxed_5230_,
            v___y_5224_,
            v___y_5225_,
            v___y_5226_,
            v___y_5227_,
        );
    leanh::lean_dec(v___y_5227_);
    leanh::lean_dec_ref(v___y_5226_);
    leanh::lean_dec(v___y_5225_);
    leanh::lean_dec_ref(v___y_5224_);
    return v_res_5231_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
    mut v_mvarId_5232_: *mut leanh::LeanObject,
    mut v_x_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5243_: u8 = 0;
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_a_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_5232_,
                    v_x_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    v___y_5237_,
                );
                if leanh::lean_obj_tag(v___x_5239_) == 0 {
                    v_a_5240_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5247_ = (!leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5247_ == 0 {
                        v___x_5242_ = v___x_5239_;
                        v_isShared_5243_ = v_isSharedCheck_5247_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5240_);
                        leanh::lean_dec(v___x_5239_);
                        v___x_5242_ = leanh::lean_box(0);
                        v_isShared_5243_ = v_isSharedCheck_5247_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5248_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5255_ = (!leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5255_ == 0 {
                        v___x_5250_ = v___x_5239_;
                        v_isShared_5251_ = v_isSharedCheck_5255_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5248_);
                        leanh::lean_dec(v___x_5239_);
                        v___x_5250_ = leanh::lean_box(0);
                        v_isShared_5251_ = v_isSharedCheck_5255_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5243_ == 0 {
                    v___x_5245_ = v___x_5242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
                    v___x_5245_ = v_reuseFailAlloc_5246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5245_;
            }
            3 => {
                if v_isShared_5251_ == 0 {
                    v___x_5253_ = v___x_5250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
                    v___x_5253_ = v_reuseFailAlloc_5254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(
    mut v_mvarId_5256_: *mut leanh::LeanObject,
    mut v_x_5257_: *mut leanh::LeanObject,
    mut v___y_5258_: *mut leanh::LeanObject,
    mut v___y_5259_: *mut leanh::LeanObject,
    mut v___y_5260_: *mut leanh::LeanObject,
    mut v___y_5261_: *mut leanh::LeanObject,
    mut v___y_5262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5263_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_5256_,
        v_x_5257_,
        v___y_5258_,
        v___y_5259_,
        v___y_5260_,
        v___y_5261_,
    );
    leanh::lean_dec(v___y_5261_);
    leanh::lean_dec_ref(v___y_5260_);
    leanh::lean_dec(v___y_5259_);
    leanh::lean_dec_ref(v___y_5258_);
    return v_res_5263_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(
    mut v_00_u03b1_5264_: *mut leanh::LeanObject,
    mut v_mvarId_5265_: *mut leanh::LeanObject,
    mut v_x_5266_: *mut leanh::LeanObject,
    mut v___y_5267_: *mut leanh::LeanObject,
    mut v___y_5268_: *mut leanh::LeanObject,
    mut v___y_5269_: *mut leanh::LeanObject,
    mut v___y_5270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_5265_,
        v_x_5266_,
        v___y_5267_,
        v___y_5268_,
        v___y_5269_,
        v___y_5270_,
    );
    return v___x_5272_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(
    mut v_00_u03b1_5273_: *mut leanh::LeanObject,
    mut v_mvarId_5274_: *mut leanh::LeanObject,
    mut v_x_5275_: *mut leanh::LeanObject,
    mut v___y_5276_: *mut leanh::LeanObject,
    mut v___y_5277_: *mut leanh::LeanObject,
    mut v___y_5278_: *mut leanh::LeanObject,
    mut v___y_5279_: *mut leanh::LeanObject,
    mut v___y_5280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5281_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(
        v_00_u03b1_5273_,
        v_mvarId_5274_,
        v_x_5275_,
        v___y_5276_,
        v___y_5277_,
        v___y_5278_,
        v___y_5279_,
    );
    leanh::lean_dec(v___y_5279_);
    leanh::lean_dec_ref(v___y_5278_);
    leanh::lean_dec(v___y_5277_);
    leanh::lean_dec_ref(v___y_5276_);
    return v_res_5281_;
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__0(
    mut v_mvarId_5282_: *mut leanh::LeanObject,
    mut v___x_5283_: *mut leanh::LeanObject,
    mut v_eqs_5284_: *mut leanh::LeanObject,
    mut v_eqRefls_5285_: *mut leanh::LeanObject,
    mut v___y_5286_: *mut leanh::LeanObject,
    mut v___y_5287_: *mut leanh::LeanObject,
    mut v___y_5288_: *mut leanh::LeanObject,
    mut v___y_5289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: u8 = 0;
    let mut v___x_5294_: u8 = 0;
    let mut v___x_5295_: u8 = 0;
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut v_a_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5311_: u8 = 0;
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut v_a_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5323_: u8 = 0;
    let mut v_a_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5291_ = l_Lean_MVarId_getType(
                    v_mvarId_5282_,
                    v___y_5286_,
                    v___y_5287_,
                    v___y_5288_,
                    v___y_5289_,
                );
                if leanh::lean_obj_tag(v___x_5291_) == 0 {
                    v_a_5292_ = leanh::lean_ctor_get(v___x_5291_, 0);
                    leanh::lean_inc(v_a_5292_);
                    leanh::lean_dec_ref_known(v___x_5291_, 1);
                    v___x_5293_ = 0;
                    v___x_5294_ = 1;
                    v___x_5295_ = 1;
                    v___x_5296_ = l_Lean_Meta_mkForallFVars(
                        v_eqs_5284_,
                        v_a_5292_,
                        v___x_5293_,
                        v___x_5294_,
                        v___x_5294_,
                        v___x_5295_,
                        v___y_5286_,
                        v___y_5287_,
                        v___y_5288_,
                        v___y_5289_,
                    );
                    if leanh::lean_obj_tag(v___x_5296_) == 0 {
                        v_a_5297_ = leanh::lean_ctor_get(v___x_5296_, 0);
                        leanh::lean_inc(v_a_5297_);
                        leanh::lean_dec_ref_known(v___x_5296_, 1);
                        v___x_5298_ = l_Lean_Meta_mkForallFVars(
                            v___x_5283_,
                            v_a_5297_,
                            v___x_5293_,
                            v___x_5294_,
                            v___x_5294_,
                            v___x_5295_,
                            v___y_5286_,
                            v___y_5287_,
                            v___y_5288_,
                            v___y_5289_,
                        );
                        if leanh::lean_obj_tag(v___x_5298_) == 0 {
                            v_a_5299_ = leanh::lean_ctor_get(v___x_5298_, 0);
                            v_isSharedCheck_5307_ =
                                (!leanh::lean_is_exclusive(v___x_5298_)) as u8;
                            if v_isSharedCheck_5307_ == 0 {
                                v___x_5301_ = v___x_5298_;
                                v_isShared_5302_ = v_isSharedCheck_5307_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5299_);
                                leanh::lean_dec(v___x_5298_);
                                v___x_5301_ = leanh::lean_box(0);
                                v_isShared_5302_ = v_isSharedCheck_5307_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_eqRefls_5285_);
                            v_a_5308_ = leanh::lean_ctor_get(v___x_5298_, 0);
                            v_isSharedCheck_5315_ =
                                (!leanh::lean_is_exclusive(v___x_5298_)) as u8;
                            if v_isSharedCheck_5315_ == 0 {
                                v___x_5310_ = v___x_5298_;
                                v_isShared_5311_ = v_isSharedCheck_5315_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5308_);
                                leanh::lean_dec(v___x_5298_);
                                v___x_5310_ = leanh::lean_box(0);
                                v_isShared_5311_ = v_isSharedCheck_5315_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_eqRefls_5285_);
                        v_a_5316_ = leanh::lean_ctor_get(v___x_5296_, 0);
                        v_isSharedCheck_5323_ =
                            (!leanh::lean_is_exclusive(v___x_5296_)) as u8;
                        if v_isSharedCheck_5323_ == 0 {
                            v___x_5318_ = v___x_5296_;
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5316_);
                            leanh::lean_dec(v___x_5296_);
                            v___x_5318_ = leanh::lean_box(0);
                            v_isShared_5319_ = v_isSharedCheck_5323_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_eqRefls_5285_);
                    v_a_5324_ = leanh::lean_ctor_get(v___x_5291_, 0);
                    v_isSharedCheck_5331_ = (!leanh::lean_is_exclusive(v___x_5291_)) as u8;
                    if v_isSharedCheck_5331_ == 0 {
                        v___x_5326_ = v___x_5291_;
                        v_isShared_5327_ = v_isSharedCheck_5331_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5324_);
                        leanh::lean_dec(v___x_5291_);
                        v___x_5326_ = leanh::lean_box(0);
                        v_isShared_5327_ = v_isSharedCheck_5331_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5303_, 0, v_a_5299_);
                leanh::lean_ctor_set(v___x_5303_, 1, v_eqRefls_5285_);
                if v_isShared_5302_ == 0 {
                    leanh::lean_ctor_set(v___x_5301_, 0, v___x_5303_);
                    v___x_5305_ = v___x_5301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
                    v___x_5305_ = v_reuseFailAlloc_5306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5305_;
            }
            3 => {
                if v_isShared_5311_ == 0 {
                    v___x_5313_ = v___x_5310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5313_;
            }
            5 => {
                if v_isShared_5319_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5322_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5321_;
            }
            7 => {
                if v_isShared_5327_ == 0 {
                    v___x_5329_ = v___x_5326_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
                    v___x_5329_ = v_reuseFailAlloc_5330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(
    mut v_mvarId_5332_: *mut leanh::LeanObject,
    mut v___x_5333_: *mut leanh::LeanObject,
    mut v_eqs_5334_: *mut leanh::LeanObject,
    mut v_eqRefls_5335_: *mut leanh::LeanObject,
    mut v___y_5336_: *mut leanh::LeanObject,
    mut v___y_5337_: *mut leanh::LeanObject,
    mut v___y_5338_: *mut leanh::LeanObject,
    mut v___y_5339_: *mut leanh::LeanObject,
    mut v___y_5340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5341_ = l_Lean_Meta_generalizeTargetsEq___lam__0(
        v_mvarId_5332_,
        v___x_5333_,
        v_eqs_5334_,
        v_eqRefls_5335_,
        v___y_5336_,
        v___y_5337_,
        v___y_5338_,
        v___y_5339_,
    );
    leanh::lean_dec(v___y_5339_);
    leanh::lean_dec_ref(v___y_5338_);
    leanh::lean_dec(v___y_5337_);
    leanh::lean_dec_ref(v___y_5336_);
    leanh::lean_dec_ref(v_eqs_5334_);
    leanh::lean_dec_ref(v___x_5333_);
    return v_res_5341_;
}
pub unsafe fn _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5343_ = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0;
    v___x_5344_ = l_Lean_stringToMessageData(v___x_5343_);
    return v___x_5344_;
}
pub unsafe fn _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5346_ = l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2;
    v___x_5347_ = l_Lean_stringToMessageData(v___x_5346_);
    return v___x_5347_;
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__1(
    mut v_targets_5348_: *mut leanh::LeanObject,
    mut v_mvarId_5349_: *mut leanh::LeanObject,
    mut v_targetsNew_5350_: *mut leanh::LeanObject,
    mut v_x_5351_: *mut leanh::LeanObject,
    mut v___y_5352_: *mut leanh::LeanObject,
    mut v___y_5353_: *mut leanh::LeanObject,
    mut v___y_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5364_ = lean_array_get_size(v_targets_5348_);
                v___x_5365_ = lean_array_get_size(v_targetsNew_5350_);
                v___x_5366_ = lean_nat_dec_le(v___x_5364_, v___x_5365_);
                if v___x_5366_ == 0 {
                    leanh::lean_dec_ref(v_targetsNew_5350_);
                    leanh::lean_dec(v_mvarId_5349_);
                    leanh::lean_dec_ref(v_targets_5348_);
                    v___x_5367_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1,
                    );
                    v___x_5368_ = l_Nat_reprFast(v___x_5364_);
                    v___x_5369_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5369_, 0, v___x_5368_);
                    v___x_5370_ = l_Lean_MessageData_ofFormat(v___x_5369_);
                    v___x_5371_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5371_, 0, v___x_5367_);
                    leanh::lean_ctor_set(v___x_5371_, 1, v___x_5370_);
                    v___x_5372_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3,
                    );
                    v___x_5373_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5373_, 0, v___x_5371_);
                    leanh::lean_ctor_set(v___x_5373_, 1, v___x_5372_);
                    v___x_5374_ = l_Nat_reprFast(v___x_5365_);
                    v___x_5375_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5375_, 0, v___x_5374_);
                    v___x_5376_ = l_Lean_MessageData_ofFormat(v___x_5375_);
                    v___x_5377_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5377_, 0, v___x_5373_);
                    leanh::lean_ctor_set(v___x_5377_, 1, v___x_5376_);
                    v___x_5378_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_5377_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
                    v_a_5379_ = leanh::lean_ctor_get(v___x_5378_, 0);
                    v_isSharedCheck_5386_ = (!leanh::lean_is_exclusive(v___x_5378_)) as u8;
                    if v_isSharedCheck_5386_ == 0 {
                        v___x_5381_ = v___x_5378_;
                        v_isShared_5382_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5379_);
                        leanh::lean_dec(v___x_5378_);
                        v___x_5381_ = leanh::lean_box(0);
                        v_isShared_5382_ = v_isSharedCheck_5386_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5358_ = lean_array_get_size(v_targets_5348_);
                v___x_5359_ = leanh::lean_unsigned_to_nat(0);
                v___x_5360_ =
                    l_Array_toSubarray___redArg(v_targetsNew_5350_, v___x_5359_, v___x_5358_);
                v___x_5361_ = l_Subarray_copy___redArg(v___x_5360_);
                leanh::lean_inc_ref(v___x_5361_);
                v___f_5362_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_generalizeTargetsEq___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                leanh::lean_closure_set(v___f_5362_, 0, v_mvarId_5349_);
                leanh::lean_closure_set(v___f_5362_, 1, v___x_5361_);
                v___x_5363_ = l_Lean_Meta_withNewEqs___redArg(
                    v_targets_5348_,
                    v___x_5361_,
                    v___f_5362_,
                    v___y_5352_,
                    v___y_5353_,
                    v___y_5354_,
                    v___y_5355_,
                );
                return v___x_5363_;
            }
            2 => {
                if v_isShared_5382_ == 0 {
                    v___x_5384_ = v___x_5381_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
                    v___x_5384_ = v_reuseFailAlloc_5385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(
    mut v_targets_5387_: *mut leanh::LeanObject,
    mut v_mvarId_5388_: *mut leanh::LeanObject,
    mut v_targetsNew_5389_: *mut leanh::LeanObject,
    mut v_x_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: *mut leanh::LeanObject,
    mut v___y_5392_: *mut leanh::LeanObject,
    mut v___y_5393_: *mut leanh::LeanObject,
    mut v___y_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_Lean_Meta_generalizeTargetsEq___lam__1(
        v_targets_5387_,
        v_mvarId_5388_,
        v_targetsNew_5389_,
        v_x_5390_,
        v___y_5391_,
        v___y_5392_,
        v___y_5393_,
        v___y_5394_,
    );
    leanh::lean_dec(v___y_5394_);
    leanh::lean_dec_ref(v___y_5393_);
    leanh::lean_dec(v___y_5392_);
    leanh::lean_dec_ref(v___y_5391_);
    leanh::lean_dec_ref(v_x_5390_);
    return v_res_5396_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_5397_: *mut leanh::LeanObject,
    mut v_x_5398_: *mut leanh::LeanObject,
    mut v_x_5399_: *mut leanh::LeanObject,
    mut v_x_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5405_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5401_ = leanh::lean_ctor_get(v_x_5397_, 0);
                v_vs_5402_ = leanh::lean_ctor_get(v_x_5397_, 1);
                v_isSharedCheck_5426_ = (!leanh::lean_is_exclusive(v_x_5397_)) as u8;
                if v_isSharedCheck_5426_ == 0 {
                    v___x_5404_ = v_x_5397_;
                    v_isShared_5405_ = v_isSharedCheck_5426_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_5402_);
                    leanh::lean_inc(v_ks_5401_);
                    leanh::lean_dec(v_x_5397_);
                    v___x_5404_ = leanh::lean_box(0);
                    v_isShared_5405_ = v_isSharedCheck_5426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5406_ = lean_array_get_size(v_ks_5401_);
                v___x_5407_ = lean_nat_dec_lt(v_x_5398_, v___x_5406_);
                if v___x_5407_ == 0 {
                    leanh::lean_dec(v_x_5398_);
                    v___x_5408_ = lean_array_push(v_ks_5401_, v_x_5399_);
                    v___x_5409_ = lean_array_push(v_vs_5402_, v_x_5400_);
                    if v_isShared_5405_ == 0 {
                        leanh::lean_ctor_set(v___x_5404_, 1, v___x_5409_);
                        leanh::lean_ctor_set(v___x_5404_, 0, v___x_5408_);
                        v___x_5411_ = v___x_5404_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5412_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 1, v___x_5409_);
                        v___x_5411_ = v_reuseFailAlloc_5412_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5413_ = lean_array_fget_borrowed(v_ks_5401_, v_x_5398_);
                    v___x_5414_ = l_Lean_instBEqMVarId_beq(v_x_5399_, v_k_x27_5413_);
                    if v___x_5414_ == 0 {
                        if v_isShared_5405_ == 0 {
                            v___x_5416_ = v___x_5404_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5420_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_ks_5401_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_vs_5402_);
                            v___x_5416_ = v_reuseFailAlloc_5420_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5421_ = lean_array_fset(v_ks_5401_, v_x_5398_, v_x_5399_);
                        v___x_5422_ = lean_array_fset(v_vs_5402_, v_x_5398_, v_x_5400_);
                        leanh::lean_dec(v_x_5398_);
                        if v_isShared_5405_ == 0 {
                            leanh::lean_ctor_set(v___x_5404_, 1, v___x_5422_);
                            leanh::lean_ctor_set(v___x_5404_, 0, v___x_5421_);
                            v___x_5424_ = v___x_5404_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5425_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5421_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 1, v___x_5422_);
                            v___x_5424_ = v_reuseFailAlloc_5425_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5411_;
            }
            3 => {
                v___x_5417_ = leanh::lean_unsigned_to_nat(1);
                v___x_5418_ = lean_nat_add(v_x_5398_, v___x_5417_);
                leanh::lean_dec(v_x_5398_);
                v_x_5397_ = v___x_5416_;
                v_x_5398_ = v___x_5418_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(
    mut v_n_5427_: *mut leanh::LeanObject,
    mut v_k_5428_: *mut leanh::LeanObject,
    mut v_v_5429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5430_ = leanh::lean_unsigned_to_nat(0);
    v___x_5431_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_5427_, v___x_5430_, v_k_5428_, v_v_5429_);
    return v___x_5431_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_5432_: usize = 0;
    let mut v___x_5433_: usize = 0;
    let mut v___x_5434_: usize = 0;
    v___x_5432_ = 5usize;
    v___x_5433_ = 1usize;
    v___x_5434_ = lean_usize_shift_left(v___x_5433_, v___x_5432_);
    return v___x_5434_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_5435_: usize = 0;
    let mut v___x_5436_: usize = 0;
    let mut v___x_5437_: usize = 0;
    v___x_5435_ = 1usize;
    v___x_5436_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_5437_ = lean_usize_sub(v___x_5436_, v___x_5435_);
    return v___x_5437_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5438_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(
    mut v_x_5439_: *mut leanh::LeanObject,
    mut v_x_5440_: usize,
    mut v_x_5441_: usize,
    mut v_x_5442_: *mut leanh::LeanObject,
    mut v_x_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: usize = 0;
    let mut v___x_5447_: usize = 0;
    let mut v___x_5448_: usize = 0;
    let mut v_j_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: u8 = 0;
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v_v_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5468_: u8 = 0;
    let mut v___x_5469_: u8 = 0;
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut v_node_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5479_: u8 = 0;
    let mut v___x_5480_: usize = 0;
    let mut v___x_5481_: usize = 0;
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5488_: u8 = 0;
    let mut v_unused_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5499_: u8 = 0;
    let mut v_ks_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: u8 = 0;
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: u8 = 0;
    let mut v_reuseFailAlloc_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5439_) == 0 {
                    v_es_5444_ = leanh::lean_ctor_get(v_x_5439_, 0);
                    v___x_5445_ = 5usize;
                    v___x_5446_ = 1usize;
                    v___x_5447_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_5448_ = lean_usize_land(v_x_5440_, v___x_5447_);
                    v_j_5449_ = lean_usize_to_nat(v___x_5448_);
                    v___x_5450_ = lean_array_get_size(v_es_5444_);
                    v___x_5451_ = lean_nat_dec_lt(v_j_5449_, v___x_5450_);
                    if v___x_5451_ == 0 {
                        leanh::lean_dec(v_j_5449_);
                        leanh::lean_dec(v_x_5443_);
                        leanh::lean_dec(v_x_5442_);
                        return v_x_5439_;
                    } else {
                        leanh::lean_inc_ref(v_es_5444_);
                        v_isSharedCheck_5488_ = (!leanh::lean_is_exclusive(v_x_5439_)) as u8;
                        if v_isSharedCheck_5488_ == 0 {
                            v_unused_5489_ = leanh::lean_ctor_get(v_x_5439_, 0);
                            leanh::lean_dec(v_unused_5489_);
                            v___x_5453_ = v_x_5439_;
                            v_isShared_5454_ = v_isSharedCheck_5488_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5439_);
                            v___x_5453_ = leanh::lean_box(0);
                            v_isShared_5454_ = v_isSharedCheck_5488_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5490_ = leanh::lean_ctor_get(v_x_5439_, 0);
                    v_vs_5491_ = leanh::lean_ctor_get(v_x_5439_, 1);
                    v_isSharedCheck_5511_ = (!leanh::lean_is_exclusive(v_x_5439_)) as u8;
                    if v_isSharedCheck_5511_ == 0 {
                        v___x_5493_ = v_x_5439_;
                        v_isShared_5494_ = v_isSharedCheck_5511_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5491_);
                        leanh::lean_inc(v_ks_5490_);
                        leanh::lean_dec(v_x_5439_);
                        v___x_5493_ = leanh::lean_box(0);
                        v_isShared_5494_ = v_isSharedCheck_5511_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5455_ = lean_array_fget(v_es_5444_, v_j_5449_);
                v___x_5456_ = leanh::lean_box(0);
                v_xs_x27_5457_ = lean_array_fset(v_es_5444_, v_j_5449_, v___x_5456_);
                match leanh::lean_obj_tag(v_v_5455_) {
                    0 => {
                        v_key_5464_ = leanh::lean_ctor_get(v_v_5455_, 0);
                        v_val_5465_ = leanh::lean_ctor_get(v_v_5455_, 1);
                        v_isSharedCheck_5475_ = (!leanh::lean_is_exclusive(v_v_5455_)) as u8;
                        if v_isSharedCheck_5475_ == 0 {
                            v___x_5467_ = v_v_5455_;
                            v_isShared_5468_ = v_isSharedCheck_5475_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5465_);
                            leanh::lean_inc(v_key_5464_);
                            leanh::lean_dec(v_v_5455_);
                            v___x_5467_ = leanh::lean_box(0);
                            v_isShared_5468_ = v_isSharedCheck_5475_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5476_ = leanh::lean_ctor_get(v_v_5455_, 0);
                        v_isSharedCheck_5486_ = (!leanh::lean_is_exclusive(v_v_5455_)) as u8;
                        if v_isSharedCheck_5486_ == 0 {
                            v___x_5478_ = v_v_5455_;
                            v_isShared_5479_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_5476_);
                            leanh::lean_dec(v_v_5455_);
                            v___x_5478_ = leanh::lean_box(0);
                            v_isShared_5479_ = v_isSharedCheck_5486_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5487_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5487_, 0, v_x_5442_);
                        leanh::lean_ctor_set(v___x_5487_, 1, v_x_5443_);
                        v___y_5459_ = v___x_5487_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5460_ = lean_array_fset(v_xs_x27_5457_, v_j_5449_, v___y_5459_);
                leanh::lean_dec(v_j_5449_);
                if v_isShared_5454_ == 0 {
                    leanh::lean_ctor_set(v___x_5453_, 0, v___x_5460_);
                    v___x_5462_ = v___x_5453_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5460_);
                    v___x_5462_ = v_reuseFailAlloc_5463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5462_;
            }
            4 => {
                v___x_5469_ = l_Lean_instBEqMVarId_beq(v_x_5442_, v_key_5464_);
                if v___x_5469_ == 0 {
                    leanh::lean_del_object(v___x_5467_);
                    v___x_5470_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5464_,
                        v_val_5465_,
                        v_x_5442_,
                        v_x_5443_,
                    );
                    v___x_5471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5471_, 0, v___x_5470_);
                    v___y_5459_ = v___x_5471_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_5465_);
                    leanh::lean_dec(v_key_5464_);
                    if v_isShared_5468_ == 0 {
                        leanh::lean_ctor_set(v___x_5467_, 1, v_x_5443_);
                        leanh::lean_ctor_set(v___x_5467_, 0, v_x_5442_);
                        v___x_5473_ = v___x_5467_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_x_5442_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_x_5443_);
                        v___x_5473_ = v_reuseFailAlloc_5474_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5459_ = v___x_5473_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5480_ = lean_usize_shift_right(v_x_5440_, v___x_5445_);
                v___x_5481_ = lean_usize_add(v_x_5441_, v___x_5446_);
                v___x_5482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_5476_, v___x_5480_, v___x_5481_, v_x_5442_, v_x_5443_);
                if v_isShared_5479_ == 0 {
                    leanh::lean_ctor_set(v___x_5478_, 0, v___x_5482_);
                    v___x_5484_ = v___x_5478_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5482_);
                    v___x_5484_ = v_reuseFailAlloc_5485_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5459_ = v___x_5484_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5494_ == 0 {
                    v___x_5496_ = v___x_5493_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5510_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_ks_5490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 1, v_vs_5491_);
                    v___x_5496_ = v_reuseFailAlloc_5510_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5497_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_5496_, v_x_5442_, v_x_5443_);
                v___x_5505_ = 7usize;
                v___x_5506_ = lean_usize_dec_le(v___x_5505_, v_x_5441_);
                if v___x_5506_ == 0 {
                    v___x_5507_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5497_);
                    v___x_5508_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5509_ = lean_nat_dec_lt(v___x_5507_, v___x_5508_);
                    leanh::lean_dec(v___x_5507_);
                    v___y_5499_ = v___x_5509_;
                    state = 10;
                    continue;
                } else {
                    v___y_5499_ = v___x_5506_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5499_ == 0 {
                    v_ks_5500_ = leanh::lean_ctor_get(v_newNode_5497_, 0);
                    leanh::lean_inc_ref(v_ks_5500_);
                    v_vs_5501_ = leanh::lean_ctor_get(v_newNode_5497_, 1);
                    leanh::lean_inc_ref(v_vs_5501_);
                    leanh::lean_dec_ref(v_newNode_5497_);
                    v___x_5502_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5503_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_5504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_5441_, v_ks_5500_, v_vs_5501_, v___x_5502_, v___x_5503_);
                    leanh::lean_dec_ref(v_vs_5501_);
                    leanh::lean_dec_ref(v_ks_5500_);
                    return v___x_5504_;
                } else {
                    return v_newNode_5497_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_depth_5512_: usize,
    mut v_keys_5513_: *mut leanh::LeanObject,
    mut v_vals_5514_: *mut leanh::LeanObject,
    mut v_i_5515_: *mut leanh::LeanObject,
    mut v_entries_5516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: u8 = 0;
    let mut v_k_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u64 = 0;
    let mut v_h_5522_: usize = 0;
    let mut v___x_5523_: usize = 0;
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: usize = 0;
    let mut v___x_5526_: usize = 0;
    let mut v___x_5527_: usize = 0;
    let mut v_h_5528_: usize = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5517_ = lean_array_get_size(v_keys_5513_);
                v___x_5518_ = lean_nat_dec_lt(v_i_5515_, v___x_5517_);
                if v___x_5518_ == 0 {
                    leanh::lean_dec(v_i_5515_);
                    return v_entries_5516_;
                } else {
                    v_k_5519_ = lean_array_fget_borrowed(v_keys_5513_, v_i_5515_);
                    v_v_5520_ = lean_array_fget_borrowed(v_vals_5514_, v_i_5515_);
                    v___x_5521_ = l_Lean_instHashableMVarId_hash(v_k_5519_);
                    v_h_5522_ = lean_uint64_to_usize(v___x_5521_);
                    v___x_5523_ = 5usize;
                    v___x_5524_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5525_ = 1usize;
                    v___x_5526_ = lean_usize_sub(v_depth_5512_, v___x_5525_);
                    v___x_5527_ = lean_usize_mul(v___x_5523_, v___x_5526_);
                    v_h_5528_ = lean_usize_shift_right(v_h_5522_, v___x_5527_);
                    v___x_5529_ = lean_nat_add(v_i_5515_, v___x_5524_);
                    leanh::lean_dec(v_i_5515_);
                    leanh::lean_inc(v_v_5520_);
                    leanh::lean_inc(v_k_5519_);
                    v___x_5530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_5516_, v_h_5528_, v_depth_5512_, v_k_5519_, v_v_5520_);
                    v_i_5515_ = v___x_5529_;
                    v_entries_5516_ = v___x_5530_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_depth_5532_: *mut leanh::LeanObject,
    mut v_keys_5533_: *mut leanh::LeanObject,
    mut v_vals_5534_: *mut leanh::LeanObject,
    mut v_i_5535_: *mut leanh::LeanObject,
    mut v_entries_5536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5537_: usize = 0;
    let mut v_res_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5537_ = leanh::lean_unbox_usize(v_depth_5532_);
    leanh::lean_dec(v_depth_5532_);
    v_res_5538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_5537_, v_keys_5533_, v_vals_5534_, v_i_5535_, v_entries_5536_);
    leanh::lean_dec_ref(v_vals_5534_);
    leanh::lean_dec_ref(v_keys_5533_);
    return v_res_5538_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_5539_: *mut leanh::LeanObject,
    mut v_x_5540_: *mut leanh::LeanObject,
    mut v_x_5541_: *mut leanh::LeanObject,
    mut v_x_5542_: *mut leanh::LeanObject,
    mut v_x_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2571__boxed_5544_: usize = 0;
    let mut v_x_2572__boxed_5545_: usize = 0;
    let mut v_res_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2571__boxed_5544_ = leanh::lean_unbox_usize(v_x_5540_);
    leanh::lean_dec(v_x_5540_);
    v_x_2572__boxed_5545_ = leanh::lean_unbox_usize(v_x_5541_);
    leanh::lean_dec(v_x_5541_);
    v_res_5546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_5539_, v_x_2571__boxed_5544_, v_x_2572__boxed_5545_, v_x_5542_, v_x_5543_);
    return v_res_5546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(
    mut v_x_5547_: *mut leanh::LeanObject,
    mut v_x_5548_: *mut leanh::LeanObject,
    mut v_x_5549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5550_: u64 = 0;
    let mut v___x_5551_: usize = 0;
    let mut v___x_5552_: usize = 0;
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5550_ = l_Lean_instHashableMVarId_hash(v_x_5548_);
    v___x_5551_ = lean_uint64_to_usize(v___x_5550_);
    v___x_5552_ = 1usize;
    v___x_5553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_5547_, v___x_5551_, v___x_5552_, v_x_5548_, v_x_5549_);
    return v___x_5553_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(
    mut v_mvarId_5554_: *mut leanh::LeanObject,
    mut v_val_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v_depth_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5558_ = lean_st_ref_take(v___y_5556_);
                v_mctx_5559_ = leanh::lean_ctor_get(v___x_5558_, 0);
                v_cache_5560_ = leanh::lean_ctor_get(v___x_5558_, 1);
                v_zetaDeltaFVarIds_5561_ = leanh::lean_ctor_get(v___x_5558_, 2);
                v_postponed_5562_ = leanh::lean_ctor_get(v___x_5558_, 3);
                v_diag_5563_ = leanh::lean_ctor_get(v___x_5558_, 4);
                v_isSharedCheck_5591_ = (!leanh::lean_is_exclusive(v___x_5558_)) as u8;
                if v_isSharedCheck_5591_ == 0 {
                    v___x_5565_ = v___x_5558_;
                    v_isShared_5566_ = v_isSharedCheck_5591_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5563_);
                    leanh::lean_inc(v_postponed_5562_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5561_);
                    leanh::lean_inc(v_cache_5560_);
                    leanh::lean_inc(v_mctx_5559_);
                    leanh::lean_dec(v___x_5558_);
                    v___x_5565_ = leanh::lean_box(0);
                    v_isShared_5566_ = v_isSharedCheck_5591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5567_ = leanh::lean_ctor_get(v_mctx_5559_, 0);
                v_levelAssignDepth_5568_ = leanh::lean_ctor_get(v_mctx_5559_, 1);
                v_lmvarCounter_5569_ = leanh::lean_ctor_get(v_mctx_5559_, 2);
                v_mvarCounter_5570_ = leanh::lean_ctor_get(v_mctx_5559_, 3);
                v_lDecls_5571_ = leanh::lean_ctor_get(v_mctx_5559_, 4);
                v_decls_5572_ = leanh::lean_ctor_get(v_mctx_5559_, 5);
                v_userNames_5573_ = leanh::lean_ctor_get(v_mctx_5559_, 6);
                v_lAssignment_5574_ = leanh::lean_ctor_get(v_mctx_5559_, 7);
                v_eAssignment_5575_ = leanh::lean_ctor_get(v_mctx_5559_, 8);
                v_dAssignment_5576_ = leanh::lean_ctor_get(v_mctx_5559_, 9);
                v_isSharedCheck_5590_ = (!leanh::lean_is_exclusive(v_mctx_5559_)) as u8;
                if v_isSharedCheck_5590_ == 0 {
                    v___x_5578_ = v_mctx_5559_;
                    v_isShared_5579_ = v_isSharedCheck_5590_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_5576_);
                    leanh::lean_inc(v_eAssignment_5575_);
                    leanh::lean_inc(v_lAssignment_5574_);
                    leanh::lean_inc(v_userNames_5573_);
                    leanh::lean_inc(v_decls_5572_);
                    leanh::lean_inc(v_lDecls_5571_);
                    leanh::lean_inc(v_mvarCounter_5570_);
                    leanh::lean_inc(v_lmvarCounter_5569_);
                    leanh::lean_inc(v_levelAssignDepth_5568_);
                    leanh::lean_inc(v_depth_5567_);
                    leanh::lean_dec(v_mctx_5559_);
                    v___x_5578_ = leanh::lean_box(0);
                    v_isShared_5579_ = v_isSharedCheck_5590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5580_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_5575_, v_mvarId_5554_, v_val_5555_);
                if v_isShared_5579_ == 0 {
                    leanh::lean_ctor_set(v___x_5578_, 8, v___x_5580_);
                    v___x_5582_ = v___x_5578_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_depth_5567_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5589_,
                        1,
                        v_levelAssignDepth_5568_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 2, v_lmvarCounter_5569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 3, v_mvarCounter_5570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 4, v_lDecls_5571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 5, v_decls_5572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 6, v_userNames_5573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 7, v_lAssignment_5574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 8, v___x_5580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 9, v_dAssignment_5576_);
                    v___x_5582_ = v_reuseFailAlloc_5589_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5566_ == 0 {
                    leanh::lean_ctor_set(v___x_5565_, 0, v___x_5582_);
                    v___x_5584_ = v___x_5565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_cache_5560_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5588_,
                        2,
                        v_zetaDeltaFVarIds_5561_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 3, v_postponed_5562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 4, v_diag_5563_);
                    v___x_5584_ = v_reuseFailAlloc_5588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5585_ = lean_st_ref_set(v___y_5556_, v___x_5584_);
                v___x_5586_ = leanh::lean_box(0);
                v___x_5587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5587_, 0, v___x_5586_);
                return v___x_5587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(
    mut v_mvarId_5592_: *mut leanh::LeanObject,
    mut v_val_5593_: *mut leanh::LeanObject,
    mut v___y_5594_: *mut leanh::LeanObject,
    mut v___y_5595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5596_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(
        v_mvarId_5592_,
        v_val_5593_,
        v___y_5594_,
    );
    leanh::lean_dec(v___y_5594_);
    return v_res_5596_;
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__2(
    mut v_mvarId_5597_: *mut leanh::LeanObject,
    mut v___x_5598_: *mut leanh::LeanObject,
    mut v_motiveType_5599_: *mut leanh::LeanObject,
    mut v___f_5600_: *mut leanh::LeanObject,
    mut v_targets_5601_: *mut leanh::LeanObject,
    mut v___y_5602_: *mut leanh::LeanObject,
    mut v___y_5603_: *mut leanh::LeanObject,
    mut v___y_5604_: *mut leanh::LeanObject,
    mut v___y_5605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: u8 = 0;
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5622_: u8 = 0;
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut v_unused_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut v_a_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5640_: u8 = 0;
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5644_: u8 = 0;
    let mut v_a_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5648_: u8 = 0;
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_5597_);
                v___x_5607_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5597_,
                    v___x_5598_,
                    v___y_5602_,
                    v___y_5603_,
                    v___y_5604_,
                    v___y_5605_,
                );
                if leanh::lean_obj_tag(v___x_5607_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5607_, 1);
                    v___x_5608_ = 0;
                    v___x_5609_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_5599_, v___f_5600_, v___x_5608_, v___x_5608_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
                    if leanh::lean_obj_tag(v___x_5609_) == 0 {
                        v_a_5610_ = leanh::lean_ctor_get(v___x_5609_, 0);
                        leanh::lean_inc(v_a_5610_);
                        leanh::lean_dec_ref_known(v___x_5609_, 1);
                        v_fst_5611_ = leanh::lean_ctor_get(v_a_5610_, 0);
                        leanh::lean_inc(v_fst_5611_);
                        v_snd_5612_ = leanh::lean_ctor_get(v_a_5610_, 1);
                        leanh::lean_inc(v_snd_5612_);
                        leanh::lean_dec(v_a_5610_);
                        leanh::lean_inc(v_mvarId_5597_);
                        v___x_5613_ = l_Lean_MVarId_getTag(
                            v_mvarId_5597_,
                            v___y_5602_,
                            v___y_5603_,
                            v___y_5604_,
                            v___y_5605_,
                        );
                        if leanh::lean_obj_tag(v___x_5613_) == 0 {
                            v_a_5614_ = leanh::lean_ctor_get(v___x_5613_, 0);
                            leanh::lean_inc(v_a_5614_);
                            leanh::lean_dec_ref_known(v___x_5613_, 1);
                            v___x_5615_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_fst_5611_,
                                v_a_5614_,
                                v___y_5602_,
                                v___y_5603_,
                                v___y_5604_,
                                v___y_5605_,
                            );
                            if leanh::lean_obj_tag(v___x_5615_) == 0 {
                                v_a_5616_ = leanh::lean_ctor_get(v___x_5615_, 0);
                                leanh::lean_inc_n(v_a_5616_, 2);
                                leanh::lean_dec_ref_known(v___x_5615_, 1);
                                v___x_5617_ = l_Lean_mkAppN(v_a_5616_, v_targets_5601_);
                                v___x_5618_ = l_Lean_mkAppN(v___x_5617_, v_snd_5612_);
                                leanh::lean_dec(v_snd_5612_);
                                v___x_5619_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_5597_, v___x_5618_, v___y_5603_);
                                v_isSharedCheck_5627_ =
                                    (!leanh::lean_is_exclusive(v___x_5619_)) as u8;
                                if v_isSharedCheck_5627_ == 0 {
                                    v_unused_5628_ = leanh::lean_ctor_get(v___x_5619_, 0);
                                    leanh::lean_dec(v_unused_5628_);
                                    v___x_5621_ = v___x_5619_;
                                    v_isShared_5622_ = v_isSharedCheck_5627_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_5619_);
                                    v___x_5621_ = leanh::lean_box(0);
                                    v_isShared_5622_ = v_isSharedCheck_5627_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_snd_5612_);
                                leanh::lean_dec(v_mvarId_5597_);
                                v_a_5629_ = leanh::lean_ctor_get(v___x_5615_, 0);
                                v_isSharedCheck_5636_ =
                                    (!leanh::lean_is_exclusive(v___x_5615_)) as u8;
                                if v_isSharedCheck_5636_ == 0 {
                                    v___x_5631_ = v___x_5615_;
                                    v_isShared_5632_ = v_isSharedCheck_5636_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5629_);
                                    leanh::lean_dec(v___x_5615_);
                                    v___x_5631_ = leanh::lean_box(0);
                                    v_isShared_5632_ = v_isSharedCheck_5636_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_snd_5612_);
                            leanh::lean_dec(v_fst_5611_);
                            leanh::lean_dec(v_mvarId_5597_);
                            v_a_5637_ = leanh::lean_ctor_get(v___x_5613_, 0);
                            v_isSharedCheck_5644_ =
                                (!leanh::lean_is_exclusive(v___x_5613_)) as u8;
                            if v_isSharedCheck_5644_ == 0 {
                                v___x_5639_ = v___x_5613_;
                                v_isShared_5640_ = v_isSharedCheck_5644_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5637_);
                                leanh::lean_dec(v___x_5613_);
                                v___x_5639_ = leanh::lean_box(0);
                                v_isShared_5640_ = v_isSharedCheck_5644_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_5597_);
                        v_a_5645_ = leanh::lean_ctor_get(v___x_5609_, 0);
                        v_isSharedCheck_5652_ =
                            (!leanh::lean_is_exclusive(v___x_5609_)) as u8;
                        if v_isSharedCheck_5652_ == 0 {
                            v___x_5647_ = v___x_5609_;
                            v_isShared_5648_ = v_isSharedCheck_5652_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5645_);
                            leanh::lean_dec(v___x_5609_);
                            v___x_5647_ = leanh::lean_box(0);
                            v_isShared_5648_ = v_isSharedCheck_5652_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_5600_);
                    leanh::lean_dec_ref(v_motiveType_5599_);
                    leanh::lean_dec(v_mvarId_5597_);
                    v_a_5653_ = leanh::lean_ctor_get(v___x_5607_, 0);
                    v_isSharedCheck_5660_ = (!leanh::lean_is_exclusive(v___x_5607_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5655_ = v___x_5607_;
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5653_);
                        leanh::lean_dec(v___x_5607_);
                        v___x_5655_ = leanh::lean_box(0);
                        v_isShared_5656_ = v_isSharedCheck_5660_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5623_ = l_Lean_Expr_mvarId_x21(v_a_5616_);
                leanh::lean_dec(v_a_5616_);
                if v_isShared_5622_ == 0 {
                    leanh::lean_ctor_set(v___x_5621_, 0, v___x_5623_);
                    v___x_5625_ = v___x_5621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5623_);
                    v___x_5625_ = v_reuseFailAlloc_5626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5625_;
            }
            3 => {
                if v_isShared_5632_ == 0 {
                    v___x_5634_ = v___x_5631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
                    v___x_5634_ = v_reuseFailAlloc_5635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5634_;
            }
            5 => {
                if v_isShared_5640_ == 0 {
                    v___x_5642_ = v___x_5639_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
                    v___x_5642_ = v_reuseFailAlloc_5643_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5642_;
            }
            7 => {
                if v_isShared_5648_ == 0 {
                    v___x_5650_ = v___x_5647_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_a_5645_);
                    v___x_5650_ = v_reuseFailAlloc_5651_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5650_;
            }
            9 => {
                if v_isShared_5656_ == 0 {
                    v___x_5658_ = v___x_5655_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(
    mut v_mvarId_5661_: *mut leanh::LeanObject,
    mut v___x_5662_: *mut leanh::LeanObject,
    mut v_motiveType_5663_: *mut leanh::LeanObject,
    mut v___f_5664_: *mut leanh::LeanObject,
    mut v_targets_5665_: *mut leanh::LeanObject,
    mut v___y_5666_: *mut leanh::LeanObject,
    mut v___y_5667_: *mut leanh::LeanObject,
    mut v___y_5668_: *mut leanh::LeanObject,
    mut v___y_5669_: *mut leanh::LeanObject,
    mut v___y_5670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5671_ = l_Lean_Meta_generalizeTargetsEq___lam__2(
        v_mvarId_5661_,
        v___x_5662_,
        v_motiveType_5663_,
        v___f_5664_,
        v_targets_5665_,
        v___y_5666_,
        v___y_5667_,
        v___y_5668_,
        v___y_5669_,
    );
    leanh::lean_dec(v___y_5669_);
    leanh::lean_dec_ref(v___y_5668_);
    leanh::lean_dec(v___y_5667_);
    leanh::lean_dec_ref(v___y_5666_);
    leanh::lean_dec_ref(v_targets_5665_);
    return v_res_5671_;
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq(
    mut v_mvarId_5675_: *mut leanh::LeanObject,
    mut v_motiveType_5676_: *mut leanh::LeanObject,
    mut v_targets_5677_: *mut leanh::LeanObject,
    mut v_a_5678_: *mut leanh::LeanObject,
    mut v_a_5679_: *mut leanh::LeanObject,
    mut v_a_5680_: *mut leanh::LeanObject,
    mut v_a_5681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_mvarId_5675_, 2);
    leanh::lean_inc_ref(v_targets_5677_);
    v___f_5683_ = leanh::lean_alloc_closure(
        l_Lean_Meta_generalizeTargetsEq___lam__1___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_5683_, 0, v_targets_5677_);
    leanh::lean_closure_set(v___f_5683_, 1, v_mvarId_5675_);
    v___x_5684_ = l_Lean_Meta_generalizeTargetsEq___closed__1;
    v___f_5685_ = leanh::lean_alloc_closure(
        l_Lean_Meta_generalizeTargetsEq___lam__2___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___f_5685_, 0, v_mvarId_5675_);
    leanh::lean_closure_set(v___f_5685_, 1, v___x_5684_);
    leanh::lean_closure_set(v___f_5685_, 2, v_motiveType_5676_);
    leanh::lean_closure_set(v___f_5685_, 3, v___f_5683_);
    leanh::lean_closure_set(v___f_5685_, 4, v_targets_5677_);
    v___x_5686_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_5675_,
        v___f_5685_,
        v_a_5678_,
        v_a_5679_,
        v_a_5680_,
        v_a_5681_,
    );
    return v___x_5686_;
}
pub unsafe fn l_Lean_Meta_generalizeTargetsEq___boxed(
    mut v_mvarId_5687_: *mut leanh::LeanObject,
    mut v_motiveType_5688_: *mut leanh::LeanObject,
    mut v_targets_5689_: *mut leanh::LeanObject,
    mut v_a_5690_: *mut leanh::LeanObject,
    mut v_a_5691_: *mut leanh::LeanObject,
    mut v_a_5692_: *mut leanh::LeanObject,
    mut v_a_5693_: *mut leanh::LeanObject,
    mut v_a_5694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5695_ = l_Lean_Meta_generalizeTargetsEq(
        v_mvarId_5687_,
        v_motiveType_5688_,
        v_targets_5689_,
        v_a_5690_,
        v_a_5691_,
        v_a_5692_,
        v_a_5693_,
    );
    leanh::lean_dec(v_a_5693_);
    leanh::lean_dec_ref(v_a_5692_);
    leanh::lean_dec(v_a_5691_);
    leanh::lean_dec_ref(v_a_5690_);
    return v_res_5695_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(
    mut v_mvarId_5696_: *mut leanh::LeanObject,
    mut v_val_5697_: *mut leanh::LeanObject,
    mut v___y_5698_: *mut leanh::LeanObject,
    mut v___y_5699_: *mut leanh::LeanObject,
    mut v___y_5700_: *mut leanh::LeanObject,
    mut v___y_5701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(
        v_mvarId_5696_,
        v_val_5697_,
        v___y_5699_,
    );
    return v___x_5703_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(
    mut v_mvarId_5704_: *mut leanh::LeanObject,
    mut v_val_5705_: *mut leanh::LeanObject,
    mut v___y_5706_: *mut leanh::LeanObject,
    mut v___y_5707_: *mut leanh::LeanObject,
    mut v___y_5708_: *mut leanh::LeanObject,
    mut v___y_5709_: *mut leanh::LeanObject,
    mut v___y_5710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(
        v_mvarId_5704_,
        v_val_5705_,
        v___y_5706_,
        v___y_5707_,
        v___y_5708_,
        v___y_5709_,
    );
    leanh::lean_dec(v___y_5709_);
    leanh::lean_dec_ref(v___y_5708_);
    leanh::lean_dec(v___y_5707_);
    leanh::lean_dec_ref(v___y_5706_);
    return v_res_5711_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(
    mut v_00_u03b2_5712_: *mut leanh::LeanObject,
    mut v_x_5713_: *mut leanh::LeanObject,
    mut v_x_5714_: *mut leanh::LeanObject,
    mut v_x_5715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5716_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_5713_, v_x_5714_, v_x_5715_);
    return v___x_5716_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(
    mut v_00_u03b2_5717_: *mut leanh::LeanObject,
    mut v_x_5718_: *mut leanh::LeanObject,
    mut v_x_5719_: usize,
    mut v_x_5720_: usize,
    mut v_x_5721_: *mut leanh::LeanObject,
    mut v_x_5722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_5718_, v_x_5719_, v_x_5720_, v_x_5721_, v_x_5722_);
    return v___x_5723_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_5724_: *mut leanh::LeanObject,
    mut v_x_5725_: *mut leanh::LeanObject,
    mut v_x_5726_: *mut leanh::LeanObject,
    mut v_x_5727_: *mut leanh::LeanObject,
    mut v_x_5728_: *mut leanh::LeanObject,
    mut v_x_5729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2968__boxed_5730_: usize = 0;
    let mut v_x_2969__boxed_5731_: usize = 0;
    let mut v_res_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2968__boxed_5730_ = leanh::lean_unbox_usize(v_x_5726_);
    leanh::lean_dec(v_x_5726_);
    v_x_2969__boxed_5731_ = leanh::lean_unbox_usize(v_x_5727_);
    leanh::lean_dec(v_x_5727_);
    v_res_5732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_5724_, v_x_5725_, v_x_2968__boxed_5730_, v_x_2969__boxed_5731_, v_x_5728_, v_x_5729_);
    return v_res_5732_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(
    mut v_00_u03b2_5733_: *mut leanh::LeanObject,
    mut v_n_5734_: *mut leanh::LeanObject,
    mut v_k_5735_: *mut leanh::LeanObject,
    mut v_v_5736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_5734_, v_k_5735_, v_v_5736_);
    return v___x_5737_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(
    mut v_00_u03b2_5738_: *mut leanh::LeanObject,
    mut v_depth_5739_: usize,
    mut v_keys_5740_: *mut leanh::LeanObject,
    mut v_vals_5741_: *mut leanh::LeanObject,
    mut v_heq_5742_: *mut leanh::LeanObject,
    mut v_i_5743_: *mut leanh::LeanObject,
    mut v_entries_5744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5745_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_5739_, v_keys_5740_, v_vals_5741_, v_i_5743_, v_entries_5744_);
    return v___x_5745_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_5746_: *mut leanh::LeanObject,
    mut v_depth_5747_: *mut leanh::LeanObject,
    mut v_keys_5748_: *mut leanh::LeanObject,
    mut v_vals_5749_: *mut leanh::LeanObject,
    mut v_heq_5750_: *mut leanh::LeanObject,
    mut v_i_5751_: *mut leanh::LeanObject,
    mut v_entries_5752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5753_: usize = 0;
    let mut v_res_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5753_ = leanh::lean_unbox_usize(v_depth_5747_);
    leanh::lean_dec(v_depth_5747_);
    v_res_5754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_5746_, v_depth_boxed_5753_, v_keys_5748_, v_vals_5749_, v_heq_5750_, v_i_5751_, v_entries_5752_);
    leanh::lean_dec_ref(v_vals_5749_);
    leanh::lean_dec_ref(v_keys_5748_);
    return v_res_5754_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_5755_: *mut leanh::LeanObject,
    mut v_x_5756_: *mut leanh::LeanObject,
    mut v_x_5757_: *mut leanh::LeanObject,
    mut v_x_5758_: *mut leanh::LeanObject,
    mut v_x_5759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5760_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_5756_, v_x_5757_, v_x_5758_, v_x_5759_);
    return v___x_5760_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(
    mut v_mvarId_5761_: *mut leanh::LeanObject,
    mut v_newEqs_5762_: *mut leanh::LeanObject,
    mut v___x_5763_: u8,
    mut v_h_x27_5764_: *mut leanh::LeanObject,
    mut v_newIndices_5765_: *mut leanh::LeanObject,
    mut v___x_5766_: *mut leanh::LeanObject,
    mut v___x_5767_: *mut leanh::LeanObject,
    mut v___x_5768_: *mut leanh::LeanObject,
    mut v___x_5769_: *mut leanh::LeanObject,
    mut v_e_5770_: *mut leanh::LeanObject,
    mut v___x_5771_: *mut leanh::LeanObject,
    mut v_newEq_5772_: *mut leanh::LeanObject,
    mut v___y_5773_: *mut leanh::LeanObject,
    mut v___y_5774_: *mut leanh::LeanObject,
    mut v___y_5775_: *mut leanh::LeanObject,
    mut v___y_5776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: u8 = 0;
    let mut v___x_5784_: u8 = 0;
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: u8 = 0;
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v_fst_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5820_: u8 = 0;
    let mut v_a_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5824_: u8 = 0;
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5828_: u8 = 0;
    let mut v_a_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5832_: u8 = 0;
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5836_: u8 = 0;
    let mut v_a_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut v_a_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_a_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5860_: u8 = 0;
    let mut v_a_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut v_a_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5872_: u8 = 0;
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v_a_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5880_: u8 = 0;
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_5761_);
                v___x_5778_ = l_Lean_MVarId_getType(
                    v_mvarId_5761_,
                    v___y_5773_,
                    v___y_5774_,
                    v___y_5775_,
                    v___y_5776_,
                );
                if leanh::lean_obj_tag(v___x_5778_) == 0 {
                    v_a_5779_ = leanh::lean_ctor_get(v___x_5778_, 0);
                    leanh::lean_inc(v_a_5779_);
                    leanh::lean_dec_ref_known(v___x_5778_, 1);
                    leanh::lean_inc(v_mvarId_5761_);
                    v___x_5780_ = l_Lean_MVarId_getTag(
                        v_mvarId_5761_,
                        v___y_5773_,
                        v___y_5774_,
                        v___y_5775_,
                        v___y_5776_,
                    );
                    if leanh::lean_obj_tag(v___x_5780_) == 0 {
                        v_a_5781_ = leanh::lean_ctor_get(v___x_5780_, 0);
                        leanh::lean_inc(v_a_5781_);
                        leanh::lean_dec_ref_known(v___x_5780_, 1);
                        v___x_5782_ = lean_array_push(v_newEqs_5762_, v_newEq_5772_);
                        v___x_5783_ = 1;
                        v___x_5784_ = 1;
                        v___x_5785_ = l_Lean_Meta_mkForallFVars(
                            v___x_5782_,
                            v_a_5779_,
                            v___x_5763_,
                            v___x_5783_,
                            v___x_5783_,
                            v___x_5784_,
                            v___y_5773_,
                            v___y_5774_,
                            v___y_5775_,
                            v___y_5776_,
                        );
                        if leanh::lean_obj_tag(v___x_5785_) == 0 {
                            v_a_5786_ = leanh::lean_ctor_get(v___x_5785_, 0);
                            leanh::lean_inc(v_a_5786_);
                            leanh::lean_dec_ref_known(v___x_5785_, 1);
                            v___x_5787_ = leanh::lean_unsigned_to_nat(1);
                            v___x_5788_ = lean_mk_empty_array_with_capacity(v___x_5787_);
                            v___x_5789_ = lean_array_push(v___x_5788_, v_h_x27_5764_);
                            v___x_5790_ = l_Lean_Meta_mkForallFVars(
                                v___x_5789_,
                                v_a_5786_,
                                v___x_5763_,
                                v___x_5783_,
                                v___x_5783_,
                                v___x_5784_,
                                v___y_5773_,
                                v___y_5774_,
                                v___y_5775_,
                                v___y_5776_,
                            );
                            leanh::lean_dec_ref(v___x_5789_);
                            if leanh::lean_obj_tag(v___x_5790_) == 0 {
                                v_a_5791_ = leanh::lean_ctor_get(v___x_5790_, 0);
                                leanh::lean_inc(v_a_5791_);
                                leanh::lean_dec_ref_known(v___x_5790_, 1);
                                v___x_5792_ = l_Lean_Meta_mkForallFVars(
                                    v_newIndices_5765_,
                                    v_a_5791_,
                                    v___x_5763_,
                                    v___x_5783_,
                                    v___x_5783_,
                                    v___x_5784_,
                                    v___y_5773_,
                                    v___y_5774_,
                                    v___y_5775_,
                                    v___y_5776_,
                                );
                                if leanh::lean_obj_tag(v___x_5792_) == 0 {
                                    v_a_5793_ = leanh::lean_ctor_get(v___x_5792_, 0);
                                    leanh::lean_inc(v_a_5793_);
                                    leanh::lean_dec_ref_known(v___x_5792_, 1);
                                    v___x_5794_ = 2;
                                    v___x_5795_ = l_Lean_Meta_mkFreshExprMVarAt(
                                        v___x_5766_,
                                        v___x_5767_,
                                        v_a_5793_,
                                        v___x_5794_,
                                        v_a_5781_,
                                        v___x_5768_,
                                        v___y_5773_,
                                        v___y_5774_,
                                        v___y_5775_,
                                        v___y_5776_,
                                    );
                                    if leanh::lean_obj_tag(v___x_5795_) == 0 {
                                        v_a_5796_ = leanh::lean_ctor_get(v___x_5795_, 0);
                                        leanh::lean_inc_n(v_a_5796_, 2);
                                        leanh::lean_dec_ref_known(v___x_5795_, 1);
                                        v___x_5797_ = l_Lean_mkAppN(v_a_5796_, v___x_5769_);
                                        v___x_5798_ =
                                            l_Lean_Expr_app___override(v___x_5797_, v_e_5770_);
                                        v___x_5799_ = l_Lean_mkAppN(v___x_5798_, v___x_5771_);
                                        v___x_5800_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_5761_, v___x_5799_, v___y_5774_);
                                        leanh::lean_dec_ref(v___x_5800_);
                                        v___x_5801_ = l_Lean_Expr_mvarId_x21(v_a_5796_);
                                        leanh::lean_dec(v_a_5796_);
                                        v___x_5802_ = lean_array_get_size(v_newIndices_5765_);
                                        v___x_5803_ = leanh::lean_box(0);
                                        v___x_5804_ = l_Lean_Meta_introNCore(
                                            v___x_5801_,
                                            v___x_5802_,
                                            v___x_5803_,
                                            v___x_5763_,
                                            v___x_5783_,
                                            v___y_5773_,
                                            v___y_5774_,
                                            v___y_5775_,
                                            v___y_5776_,
                                        );
                                        if leanh::lean_obj_tag(v___x_5804_) == 0 {
                                            v_a_5805_ = leanh::lean_ctor_get(v___x_5804_, 0);
                                            leanh::lean_inc(v_a_5805_);
                                            leanh::lean_dec_ref_known(v___x_5804_, 1);
                                            v_fst_5806_ = leanh::lean_ctor_get(v_a_5805_, 0);
                                            leanh::lean_inc(v_fst_5806_);
                                            v_snd_5807_ = leanh::lean_ctor_get(v_a_5805_, 1);
                                            leanh::lean_inc(v_snd_5807_);
                                            leanh::lean_dec(v_a_5805_);
                                            v___x_5808_ = l_Lean_Meta_intro1Core(
                                                v_snd_5807_,
                                                v___x_5783_,
                                                v___y_5773_,
                                                v___y_5774_,
                                                v___y_5775_,
                                                v___y_5776_,
                                            );
                                            if leanh::lean_obj_tag(v___x_5808_) == 0 {
                                                v_a_5809_ =
                                                    leanh::lean_ctor_get(v___x_5808_, 0);
                                                v_isSharedCheck_5820_ =
                                                    (!leanh::lean_is_exclusive(v___x_5808_))
                                                        as u8;
                                                if v_isSharedCheck_5820_ == 0 {
                                                    v___x_5811_ = v___x_5808_;
                                                    v_isShared_5812_ = v_isSharedCheck_5820_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5809_);
                                                    leanh::lean_dec(v___x_5808_);
                                                    v___x_5811_ = leanh::lean_box(0);
                                                    v_isShared_5812_ = v_isSharedCheck_5820_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_fst_5806_);
                                                leanh::lean_dec_ref(v___x_5782_);
                                                v_a_5821_ =
                                                    leanh::lean_ctor_get(v___x_5808_, 0);
                                                v_isSharedCheck_5828_ =
                                                    (!leanh::lean_is_exclusive(v___x_5808_))
                                                        as u8;
                                                if v_isSharedCheck_5828_ == 0 {
                                                    v___x_5823_ = v___x_5808_;
                                                    v_isShared_5824_ = v_isSharedCheck_5828_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5821_);
                                                    leanh::lean_dec(v___x_5808_);
                                                    v___x_5823_ = leanh::lean_box(0);
                                                    v_isShared_5824_ = v_isSharedCheck_5828_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_5782_);
                                            v_a_5829_ = leanh::lean_ctor_get(v___x_5804_, 0);
                                            v_isSharedCheck_5836_ =
                                                (!leanh::lean_is_exclusive(v___x_5804_))
                                                    as u8;
                                            if v_isSharedCheck_5836_ == 0 {
                                                v___x_5831_ = v___x_5804_;
                                                v_isShared_5832_ = v_isSharedCheck_5836_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5829_);
                                                leanh::lean_dec(v___x_5804_);
                                                v___x_5831_ = leanh::lean_box(0);
                                                v_isShared_5832_ = v_isSharedCheck_5836_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_5782_);
                                        leanh::lean_dec_ref(v_e_5770_);
                                        leanh::lean_dec(v_mvarId_5761_);
                                        v_a_5837_ = leanh::lean_ctor_get(v___x_5795_, 0);
                                        v_isSharedCheck_5844_ =
                                            (!leanh::lean_is_exclusive(v___x_5795_)) as u8;
                                        if v_isSharedCheck_5844_ == 0 {
                                            v___x_5839_ = v___x_5795_;
                                            v_isShared_5840_ = v_isSharedCheck_5844_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5837_);
                                            leanh::lean_dec(v___x_5795_);
                                            v___x_5839_ = leanh::lean_box(0);
                                            v_isShared_5840_ = v_isSharedCheck_5844_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_5782_);
                                    leanh::lean_dec(v_a_5781_);
                                    leanh::lean_dec_ref(v_e_5770_);
                                    leanh::lean_dec(v___x_5768_);
                                    leanh::lean_dec_ref(v___x_5767_);
                                    leanh::lean_dec_ref(v___x_5766_);
                                    leanh::lean_dec(v_mvarId_5761_);
                                    v_a_5845_ = leanh::lean_ctor_get(v___x_5792_, 0);
                                    v_isSharedCheck_5852_ =
                                        (!leanh::lean_is_exclusive(v___x_5792_)) as u8;
                                    if v_isSharedCheck_5852_ == 0 {
                                        v___x_5847_ = v___x_5792_;
                                        v_isShared_5848_ = v_isSharedCheck_5852_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5845_);
                                        leanh::lean_dec(v___x_5792_);
                                        v___x_5847_ = leanh::lean_box(0);
                                        v_isShared_5848_ = v_isSharedCheck_5852_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_5782_);
                                leanh::lean_dec(v_a_5781_);
                                leanh::lean_dec_ref(v_e_5770_);
                                leanh::lean_dec(v___x_5768_);
                                leanh::lean_dec_ref(v___x_5767_);
                                leanh::lean_dec_ref(v___x_5766_);
                                leanh::lean_dec(v_mvarId_5761_);
                                v_a_5853_ = leanh::lean_ctor_get(v___x_5790_, 0);
                                v_isSharedCheck_5860_ =
                                    (!leanh::lean_is_exclusive(v___x_5790_)) as u8;
                                if v_isSharedCheck_5860_ == 0 {
                                    v___x_5855_ = v___x_5790_;
                                    v_isShared_5856_ = v_isSharedCheck_5860_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5853_);
                                    leanh::lean_dec(v___x_5790_);
                                    v___x_5855_ = leanh::lean_box(0);
                                    v_isShared_5856_ = v_isSharedCheck_5860_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_5782_);
                            leanh::lean_dec(v_a_5781_);
                            leanh::lean_dec_ref(v_e_5770_);
                            leanh::lean_dec(v___x_5768_);
                            leanh::lean_dec_ref(v___x_5767_);
                            leanh::lean_dec_ref(v___x_5766_);
                            leanh::lean_dec_ref(v_h_x27_5764_);
                            leanh::lean_dec(v_mvarId_5761_);
                            v_a_5861_ = leanh::lean_ctor_get(v___x_5785_, 0);
                            v_isSharedCheck_5868_ =
                                (!leanh::lean_is_exclusive(v___x_5785_)) as u8;
                            if v_isSharedCheck_5868_ == 0 {
                                v___x_5863_ = v___x_5785_;
                                v_isShared_5864_ = v_isSharedCheck_5868_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5861_);
                                leanh::lean_dec(v___x_5785_);
                                v___x_5863_ = leanh::lean_box(0);
                                v_isShared_5864_ = v_isSharedCheck_5868_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5779_);
                        leanh::lean_dec_ref(v_newEq_5772_);
                        leanh::lean_dec_ref(v_e_5770_);
                        leanh::lean_dec(v___x_5768_);
                        leanh::lean_dec_ref(v___x_5767_);
                        leanh::lean_dec_ref(v___x_5766_);
                        leanh::lean_dec_ref(v_h_x27_5764_);
                        leanh::lean_dec_ref(v_newEqs_5762_);
                        leanh::lean_dec(v_mvarId_5761_);
                        v_a_5869_ = leanh::lean_ctor_get(v___x_5780_, 0);
                        v_isSharedCheck_5876_ =
                            (!leanh::lean_is_exclusive(v___x_5780_)) as u8;
                        if v_isSharedCheck_5876_ == 0 {
                            v___x_5871_ = v___x_5780_;
                            v_isShared_5872_ = v_isSharedCheck_5876_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5869_);
                            leanh::lean_dec(v___x_5780_);
                            v___x_5871_ = leanh::lean_box(0);
                            v_isShared_5872_ = v_isSharedCheck_5876_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_newEq_5772_);
                    leanh::lean_dec_ref(v_e_5770_);
                    leanh::lean_dec(v___x_5768_);
                    leanh::lean_dec_ref(v___x_5767_);
                    leanh::lean_dec_ref(v___x_5766_);
                    leanh::lean_dec_ref(v_h_x27_5764_);
                    leanh::lean_dec_ref(v_newEqs_5762_);
                    leanh::lean_dec(v_mvarId_5761_);
                    v_a_5877_ = leanh::lean_ctor_get(v___x_5778_, 0);
                    v_isSharedCheck_5884_ = (!leanh::lean_is_exclusive(v___x_5778_)) as u8;
                    if v_isSharedCheck_5884_ == 0 {
                        v___x_5879_ = v___x_5778_;
                        v_isShared_5880_ = v_isSharedCheck_5884_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5877_);
                        leanh::lean_dec(v___x_5778_);
                        v___x_5879_ = leanh::lean_box(0);
                        v_isShared_5880_ = v_isSharedCheck_5884_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5813_ = leanh::lean_ctor_get(v_a_5809_, 0);
                leanh::lean_inc(v_fst_5813_);
                v_snd_5814_ = leanh::lean_ctor_get(v_a_5809_, 1);
                leanh::lean_inc(v_snd_5814_);
                leanh::lean_dec(v_a_5809_);
                v___x_5815_ = lean_array_get_size(v___x_5782_);
                leanh::lean_dec_ref(v___x_5782_);
                v___x_5816_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5816_, 0, v_snd_5814_);
                leanh::lean_ctor_set(v___x_5816_, 1, v_fst_5806_);
                leanh::lean_ctor_set(v___x_5816_, 2, v_fst_5813_);
                leanh::lean_ctor_set(v___x_5816_, 3, v___x_5815_);
                if v_isShared_5812_ == 0 {
                    leanh::lean_ctor_set(v___x_5811_, 0, v___x_5816_);
                    v___x_5818_ = v___x_5811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5819_, 0, v___x_5816_);
                    v___x_5818_ = v_reuseFailAlloc_5819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5818_;
            }
            3 => {
                if v_isShared_5824_ == 0 {
                    v___x_5826_ = v___x_5823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5827_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_a_5821_);
                    v___x_5826_ = v_reuseFailAlloc_5827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5826_;
            }
            5 => {
                if v_isShared_5832_ == 0 {
                    v___x_5834_ = v___x_5831_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5829_);
                    v___x_5834_ = v_reuseFailAlloc_5835_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5834_;
            }
            7 => {
                if v_isShared_5840_ == 0 {
                    v___x_5842_ = v___x_5839_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_a_5837_);
                    v___x_5842_ = v_reuseFailAlloc_5843_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5842_;
            }
            9 => {
                if v_isShared_5848_ == 0 {
                    v___x_5850_ = v___x_5847_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
                    v___x_5850_ = v_reuseFailAlloc_5851_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5850_;
            }
            11 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5859_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5858_;
            }
            13 => {
                if v_isShared_5864_ == 0 {
                    v___x_5866_ = v___x_5863_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
                    v___x_5866_ = v_reuseFailAlloc_5867_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5866_;
            }
            15 => {
                if v_isShared_5872_ == 0 {
                    v___x_5874_ = v___x_5871_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
                    v___x_5874_ = v_reuseFailAlloc_5875_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5874_;
            }
            17 => {
                if v_isShared_5880_ == 0 {
                    v___x_5882_ = v___x_5879_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_a_5877_);
                    v___x_5882_ = v_reuseFailAlloc_5883_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_5885_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_newEqs_5886_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_5887_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_h_x27_5888_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_newIndices_5889_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_5890_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_5891_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5892_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5893_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_e_5894_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5895_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_newEq_5896_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5897_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5898_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5899_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5900_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5901_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_6260__boxed_5902_: u8 = 0;
    let mut v_res_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6260__boxed_5902_ = (leanh::lean_unbox(v___x_5887_) as u8);
    v_res_5903_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(
        v_mvarId_5885_,
        v_newEqs_5886_,
        v___x_6260__boxed_5902_,
        v_h_x27_5888_,
        v_newIndices_5889_,
        v___x_5890_,
        v___x_5891_,
        v___x_5892_,
        v___x_5893_,
        v_e_5894_,
        v___x_5895_,
        v_newEq_5896_,
        v___y_5897_,
        v___y_5898_,
        v___y_5899_,
        v___y_5900_,
    );
    leanh::lean_dec(v___y_5900_);
    leanh::lean_dec_ref(v___y_5899_);
    leanh::lean_dec(v___y_5898_);
    leanh::lean_dec_ref(v___y_5897_);
    leanh::lean_dec_ref(v___x_5895_);
    leanh::lean_dec_ref(v___x_5893_);
    leanh::lean_dec_ref(v_newIndices_5889_);
    return v_res_5903_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(
    mut v_e_5904_: *mut leanh::LeanObject,
    mut v_h_x27_5905_: *mut leanh::LeanObject,
    mut v_mvarId_5906_: *mut leanh::LeanObject,
    mut v___x_5907_: u8,
    mut v_newIndices_5908_: *mut leanh::LeanObject,
    mut v___x_5909_: *mut leanh::LeanObject,
    mut v___x_5910_: *mut leanh::LeanObject,
    mut v___x_5911_: *mut leanh::LeanObject,
    mut v___x_5912_: *mut leanh::LeanObject,
    mut v_newEqs_5913_: *mut leanh::LeanObject,
    mut v_newRefls_5914_: *mut leanh::LeanObject,
    mut v___y_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
    mut v___y_5917_: *mut leanh::LeanObject,
    mut v___y_5918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5932_: u8 = 0;
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_h_x27_5905_);
                leanh::lean_inc_ref(v_e_5904_);
                v___x_5920_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(
                    v_e_5904_,
                    v_h_x27_5905_,
                    v___y_5915_,
                    v___y_5916_,
                    v___y_5917_,
                    v___y_5918_,
                );
                if leanh::lean_obj_tag(v___x_5920_) == 0 {
                    v_a_5921_ = leanh::lean_ctor_get(v___x_5920_, 0);
                    leanh::lean_inc(v_a_5921_);
                    leanh::lean_dec_ref_known(v___x_5920_, 1);
                    v_fst_5922_ = leanh::lean_ctor_get(v_a_5921_, 0);
                    leanh::lean_inc(v_fst_5922_);
                    v_snd_5923_ = leanh::lean_ctor_get(v_a_5921_, 1);
                    leanh::lean_inc(v_snd_5923_);
                    leanh::lean_dec(v_a_5921_);
                    v___x_5924_ = lean_array_push(v_newRefls_5914_, v_snd_5923_);
                    v___x_5925_ = leanh::lean_box((v___x_5907_) as usize);
                    v___f_5926_ = leanh::lean_alloc_closure(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed as *mut core::ffi::c_void, 17, 11);
                    leanh::lean_closure_set(v___f_5926_, 0, v_mvarId_5906_);
                    leanh::lean_closure_set(v___f_5926_, 1, v_newEqs_5913_);
                    leanh::lean_closure_set(v___f_5926_, 2, v___x_5925_);
                    leanh::lean_closure_set(v___f_5926_, 3, v_h_x27_5905_);
                    leanh::lean_closure_set(v___f_5926_, 4, v_newIndices_5908_);
                    leanh::lean_closure_set(v___f_5926_, 5, v___x_5909_);
                    leanh::lean_closure_set(v___f_5926_, 6, v___x_5910_);
                    leanh::lean_closure_set(v___f_5926_, 7, v___x_5911_);
                    leanh::lean_closure_set(v___f_5926_, 8, v___x_5912_);
                    leanh::lean_closure_set(v___f_5926_, 9, v_e_5904_);
                    leanh::lean_closure_set(v___f_5926_, 10, v___x_5924_);
                    v___x_5927_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1;
                    v___x_5928_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_5927_, v_fst_5922_, v___f_5926_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
                    return v___x_5928_;
                } else {
                    leanh::lean_dec_ref(v_newRefls_5914_);
                    leanh::lean_dec_ref(v_newEqs_5913_);
                    leanh::lean_dec_ref(v___x_5912_);
                    leanh::lean_dec(v___x_5911_);
                    leanh::lean_dec_ref(v___x_5910_);
                    leanh::lean_dec_ref(v___x_5909_);
                    leanh::lean_dec_ref(v_newIndices_5908_);
                    leanh::lean_dec(v_mvarId_5906_);
                    leanh::lean_dec_ref(v_h_x27_5905_);
                    leanh::lean_dec_ref(v_e_5904_);
                    v_a_5929_ = leanh::lean_ctor_get(v___x_5920_, 0);
                    v_isSharedCheck_5936_ = (!leanh::lean_is_exclusive(v___x_5920_)) as u8;
                    if v_isSharedCheck_5936_ == 0 {
                        v___x_5931_ = v___x_5920_;
                        v_isShared_5932_ = v_isSharedCheck_5936_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5929_);
                        leanh::lean_dec(v___x_5920_);
                        v___x_5931_ = leanh::lean_box(0);
                        v_isShared_5932_ = v_isSharedCheck_5936_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5932_ == 0 {
                    v___x_5934_ = v___x_5931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5935_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_a_5929_);
                    v___x_5934_ = v_reuseFailAlloc_5935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(
    mut v_e_5937_: *mut leanh::LeanObject,
    mut v_h_x27_5938_: *mut leanh::LeanObject,
    mut v_mvarId_5939_: *mut leanh::LeanObject,
    mut v___x_5940_: *mut leanh::LeanObject,
    mut v_newIndices_5941_: *mut leanh::LeanObject,
    mut v___x_5942_: *mut leanh::LeanObject,
    mut v___x_5943_: *mut leanh::LeanObject,
    mut v___x_5944_: *mut leanh::LeanObject,
    mut v___x_5945_: *mut leanh::LeanObject,
    mut v_newEqs_5946_: *mut leanh::LeanObject,
    mut v_newRefls_5947_: *mut leanh::LeanObject,
    mut v___y_5948_: *mut leanh::LeanObject,
    mut v___y_5949_: *mut leanh::LeanObject,
    mut v___y_5950_: *mut leanh::LeanObject,
    mut v___y_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6512__boxed_5953_: u8 = 0;
    let mut v_res_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6512__boxed_5953_ = (leanh::lean_unbox(v___x_5940_) as u8);
    v_res_5954_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(
        v_e_5937_,
        v_h_x27_5938_,
        v_mvarId_5939_,
        v___x_6512__boxed_5953_,
        v_newIndices_5941_,
        v___x_5942_,
        v___x_5943_,
        v___x_5944_,
        v___x_5945_,
        v_newEqs_5946_,
        v_newRefls_5947_,
        v___y_5948_,
        v___y_5949_,
        v___y_5950_,
        v___y_5951_,
    );
    leanh::lean_dec(v___y_5951_);
    leanh::lean_dec_ref(v___y_5950_);
    leanh::lean_dec(v___y_5949_);
    leanh::lean_dec_ref(v___y_5948_);
    return v_res_5954_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(
    mut v_e_5955_: *mut leanh::LeanObject,
    mut v_mvarId_5956_: *mut leanh::LeanObject,
    mut v___x_5957_: u8,
    mut v_newIndices_5958_: *mut leanh::LeanObject,
    mut v___x_5959_: *mut leanh::LeanObject,
    mut v___x_5960_: *mut leanh::LeanObject,
    mut v___x_5961_: *mut leanh::LeanObject,
    mut v___x_5962_: *mut leanh::LeanObject,
    mut v_h_x27_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
    mut v___y_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5969_ = leanh::lean_box((v___x_5957_) as usize);
    leanh::lean_inc_ref(v___x_5962_);
    leanh::lean_inc_ref(v_newIndices_5958_);
    v___f_5970_ = leanh::lean_alloc_closure(
        l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed
            as *mut core::ffi::c_void,
        16,
        9,
    );
    leanh::lean_closure_set(v___f_5970_, 0, v_e_5955_);
    leanh::lean_closure_set(v___f_5970_, 1, v_h_x27_5963_);
    leanh::lean_closure_set(v___f_5970_, 2, v_mvarId_5956_);
    leanh::lean_closure_set(v___f_5970_, 3, v___x_5969_);
    leanh::lean_closure_set(v___f_5970_, 4, v_newIndices_5958_);
    leanh::lean_closure_set(v___f_5970_, 5, v___x_5959_);
    leanh::lean_closure_set(v___f_5970_, 6, v___x_5960_);
    leanh::lean_closure_set(v___f_5970_, 7, v___x_5961_);
    leanh::lean_closure_set(v___f_5970_, 8, v___x_5962_);
    v___x_5971_ = l_Lean_Meta_withNewEqs___redArg(
        v___x_5962_,
        v_newIndices_5958_,
        v___f_5970_,
        v___y_5964_,
        v___y_5965_,
        v___y_5966_,
        v___y_5967_,
    );
    return v___x_5971_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(
    mut v_e_5972_: *mut leanh::LeanObject,
    mut v_mvarId_5973_: *mut leanh::LeanObject,
    mut v___x_5974_: *mut leanh::LeanObject,
    mut v_newIndices_5975_: *mut leanh::LeanObject,
    mut v___x_5976_: *mut leanh::LeanObject,
    mut v___x_5977_: *mut leanh::LeanObject,
    mut v___x_5978_: *mut leanh::LeanObject,
    mut v___x_5979_: *mut leanh::LeanObject,
    mut v_h_x27_5980_: *mut leanh::LeanObject,
    mut v___y_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
    mut v___y_5984_: *mut leanh::LeanObject,
    mut v___y_5985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6577__boxed_5986_: u8 = 0;
    let mut v_res_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6577__boxed_5986_ = (leanh::lean_unbox(v___x_5974_) as u8);
    v_res_5987_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(
        v_e_5972_,
        v_mvarId_5973_,
        v___x_6577__boxed_5986_,
        v_newIndices_5975_,
        v___x_5976_,
        v___x_5977_,
        v___x_5978_,
        v___x_5979_,
        v_h_x27_5980_,
        v___y_5981_,
        v___y_5982_,
        v___y_5983_,
        v___y_5984_,
    );
    leanh::lean_dec(v___y_5984_);
    leanh::lean_dec_ref(v___y_5983_);
    leanh::lean_dec(v___y_5982_);
    leanh::lean_dec_ref(v___y_5981_);
    return v_res_5987_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(
    mut v_e_5991_: *mut leanh::LeanObject,
    mut v_mvarId_5992_: *mut leanh::LeanObject,
    mut v___x_5993_: u8,
    mut v___x_5994_: *mut leanh::LeanObject,
    mut v___x_5995_: *mut leanh::LeanObject,
    mut v___x_5996_: *mut leanh::LeanObject,
    mut v___x_5997_: *mut leanh::LeanObject,
    mut v___x_5998_: *mut leanh::LeanObject,
    mut v_varName_x3f_5999_: *mut leanh::LeanObject,
    mut v_newIndices_6000_: *mut leanh::LeanObject,
    mut v_x_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
    mut v___y_6004_: *mut leanh::LeanObject,
    mut v___y_6005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6019_: u8 = 0;
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6007_ = leanh::lean_box((v___x_5993_) as usize);
                leanh::lean_inc_ref(v_newIndices_6000_);
                v___f_6008_ = leanh::lean_alloc_closure(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed as *mut core::ffi::c_void, 14, 8);
                leanh::lean_closure_set(v___f_6008_, 0, v_e_5991_);
                leanh::lean_closure_set(v___f_6008_, 1, v_mvarId_5992_);
                leanh::lean_closure_set(v___f_6008_, 2, v___x_6007_);
                leanh::lean_closure_set(v___f_6008_, 3, v_newIndices_6000_);
                leanh::lean_closure_set(v___f_6008_, 4, v___x_5994_);
                leanh::lean_closure_set(v___f_6008_, 5, v___x_5995_);
                leanh::lean_closure_set(v___f_6008_, 6, v___x_5996_);
                leanh::lean_closure_set(v___f_6008_, 7, v___x_5997_);
                v___x_6009_ = l_Lean_mkAppN(v___x_5998_, v_newIndices_6000_);
                leanh::lean_dec_ref(v_newIndices_6000_);
                if leanh::lean_obj_tag(v_varName_x3f_5999_) == 1 {
                    v_val_6010_ = leanh::lean_ctor_get(v_varName_x3f_5999_, 0);
                    leanh::lean_inc(v_val_6010_);
                    leanh::lean_dec_ref_known(v_varName_x3f_5999_, 1);
                    v___x_6011_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_6010_, v___x_6009_, v___f_6008_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_);
                    return v___x_6011_;
                } else {
                    leanh::lean_dec(v_varName_x3f_5999_);
                    v___x_6012_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1;
                    v___x_6013_ =
                        l_Lean_Core_mkFreshUserName(v___x_6012_, v___y_6004_, v___y_6005_);
                    if leanh::lean_obj_tag(v___x_6013_) == 0 {
                        v_a_6014_ = leanh::lean_ctor_get(v___x_6013_, 0);
                        leanh::lean_inc(v_a_6014_);
                        leanh::lean_dec_ref_known(v___x_6013_, 1);
                        v___x_6015_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_6014_, v___x_6009_, v___f_6008_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_);
                        return v___x_6015_;
                    } else {
                        leanh::lean_dec_ref(v___x_6009_);
                        leanh::lean_dec_ref(v___f_6008_);
                        v_a_6016_ = leanh::lean_ctor_get(v___x_6013_, 0);
                        v_isSharedCheck_6023_ =
                            (!leanh::lean_is_exclusive(v___x_6013_)) as u8;
                        if v_isSharedCheck_6023_ == 0 {
                            v___x_6018_ = v___x_6013_;
                            v_isShared_6019_ = v_isSharedCheck_6023_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6016_);
                            leanh::lean_dec(v___x_6013_);
                            v___x_6018_ = leanh::lean_box(0);
                            v_isShared_6019_ = v_isSharedCheck_6023_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6019_ == 0 {
                    v___x_6021_ = v___x_6018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
                    v___x_6021_ = v_reuseFailAlloc_6022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(
    mut v_e_6024_: *mut leanh::LeanObject,
    mut v_mvarId_6025_: *mut leanh::LeanObject,
    mut v___x_6026_: *mut leanh::LeanObject,
    mut v___x_6027_: *mut leanh::LeanObject,
    mut v___x_6028_: *mut leanh::LeanObject,
    mut v___x_6029_: *mut leanh::LeanObject,
    mut v___x_6030_: *mut leanh::LeanObject,
    mut v___x_6031_: *mut leanh::LeanObject,
    mut v_varName_x3f_6032_: *mut leanh::LeanObject,
    mut v_newIndices_6033_: *mut leanh::LeanObject,
    mut v_x_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
    mut v___y_6036_: *mut leanh::LeanObject,
    mut v___y_6037_: *mut leanh::LeanObject,
    mut v___y_6038_: *mut leanh::LeanObject,
    mut v___y_6039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6619__boxed_6040_: u8 = 0;
    let mut v_res_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6619__boxed_6040_ = (leanh::lean_unbox(v___x_6026_) as u8);
    v_res_6041_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(
        v_e_6024_,
        v_mvarId_6025_,
        v___x_6619__boxed_6040_,
        v___x_6027_,
        v___x_6028_,
        v___x_6029_,
        v___x_6030_,
        v___x_6031_,
        v_varName_x3f_6032_,
        v_newIndices_6033_,
        v_x_6034_,
        v___y_6035_,
        v___y_6036_,
        v___y_6037_,
        v___y_6038_,
    );
    leanh::lean_dec(v___y_6038_);
    leanh::lean_dec_ref(v___y_6037_);
    leanh::lean_dec(v___y_6036_);
    leanh::lean_dec_ref(v___y_6035_);
    leanh::lean_dec_ref(v_x_6034_);
    return v_res_6041_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6048_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3;
    v___x_6049_ = l_Lean_MessageData_ofFormat(v___x_6048_);
    return v___x_6049_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6050_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
    v___x_6051_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6051_, 0, v___x_6050_);
    return v___x_6051_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7;
    v___x_6056_ = l_Lean_MessageData_ofFormat(v___x_6055_);
    return v___x_6056_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6057_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
    v___x_6058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6058_, 0, v___x_6057_);
    return v___x_6058_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6062_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11;
    v___x_6063_ = l_Lean_MessageData_ofFormat(v___x_6062_);
    return v___x_6063_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6064_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
    v___x_6065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6065_, 0, v___x_6064_);
    return v___x_6065_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(
    mut v_mvarId_6066_: *mut leanh::LeanObject,
    mut v_e_6067_: *mut leanh::LeanObject,
    mut v___x_6068_: *mut leanh::LeanObject,
    mut v___x_6069_: *mut leanh::LeanObject,
    mut v_varName_x3f_6070_: *mut leanh::LeanObject,
    mut v_x_6071_: *mut leanh::LeanObject,
    mut v_x_6072_: *mut leanh::LeanObject,
    mut v_x_6073_: *mut leanh::LeanObject,
    mut v___y_6074_: *mut leanh::LeanObject,
    mut v___y_6075_: *mut leanh::LeanObject,
    mut v___y_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: u8 = 0;
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v___y_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: u8 = 0;
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6139_: u8 = 0;
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6143_: u8 = 0;
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: u8 = 0;
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6151_: u8 = 0;
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6071_) == 5 {
                    v_fn_6079_ = leanh::lean_ctor_get(v_x_6071_, 0);
                    leanh::lean_inc_ref(v_fn_6079_);
                    v_arg_6080_ = leanh::lean_ctor_get(v_x_6071_, 1);
                    leanh::lean_inc_ref(v_arg_6080_);
                    leanh::lean_dec_ref_known(v_x_6071_, 2);
                    v___x_6081_ = lean_array_set(v_x_6072_, v_x_6073_, v_arg_6080_);
                    v___x_6082_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6083_ = lean_nat_sub(v_x_6073_, v___x_6082_);
                    leanh::lean_dec(v_x_6073_);
                    v_x_6071_ = v_fn_6079_;
                    v_x_6072_ = v___x_6081_;
                    v_x_6073_ = v___x_6083_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6073_);
                    v___x_6085_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1;
                    if leanh::lean_obj_tag(v_x_6071_) == 4 {
                        v_declName_6093_ = leanh::lean_ctor_get(v_x_6071_, 0);
                        v___x_6094_ = lean_st_ref_get(v___y_6077_);
                        v_env_6095_ = leanh::lean_ctor_get(v___x_6094_, 0);
                        leanh::lean_inc_ref(v_env_6095_);
                        leanh::lean_dec(v___x_6094_);
                        v___x_6096_ = 0;
                        leanh::lean_inc(v_declName_6093_);
                        v___x_6097_ =
                            l_Lean_Environment_find_x3f(v_env_6095_, v_declName_6093_, v___x_6096_);
                        if leanh::lean_obj_tag(v___x_6097_) == 0 {
                            leanh::lean_dec_ref_known(v_x_6071_, 2);
                            leanh::lean_dec_ref(v_x_6072_);
                            leanh::lean_dec(v_varName_x3f_6070_);
                            leanh::lean_dec_ref(v___x_6069_);
                            leanh::lean_dec_ref(v___x_6068_);
                            leanh::lean_dec_ref(v_e_6067_);
                            v___y_6087_ = v___y_6074_;
                            v___y_6088_ = v___y_6075_;
                            v___y_6089_ = v___y_6076_;
                            v___y_6090_ = v___y_6077_;
                            state = 1;
                            continue;
                        } else {
                            v_val_6098_ = leanh::lean_ctor_get(v___x_6097_, 0);
                            leanh::lean_inc(v_val_6098_);
                            leanh::lean_dec_ref_known(v___x_6097_, 1);
                            if leanh::lean_obj_tag(v_val_6098_) == 5 {
                                v_val_6099_ = leanh::lean_ctor_get(v_val_6098_, 0);
                                leanh::lean_inc_ref(v_val_6099_);
                                leanh::lean_dec_ref_known(v_val_6098_, 1);
                                v_numParams_6100_ = leanh::lean_ctor_get(v_val_6099_, 1);
                                leanh::lean_inc(v_numParams_6100_);
                                v_numIndices_6101_ = leanh::lean_ctor_get(v_val_6099_, 2);
                                leanh::lean_inc(v_numIndices_6101_);
                                leanh::lean_dec_ref(v_val_6099_);
                                v___x_6144_ = leanh::lean_unsigned_to_nat(0);
                                v___x_6145_ = lean_nat_dec_lt(v___x_6144_, v_numIndices_6101_);
                                if v___x_6145_ == 0 {
                                    v___x_6146_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
                                    leanh::lean_inc(v_mvarId_6066_);
                                    v___x_6147_ = l_Lean_Meta_throwTacticEx___redArg(
                                        v___x_6085_,
                                        v_mvarId_6066_,
                                        v___x_6146_,
                                        v___y_6074_,
                                        v___y_6075_,
                                        v___y_6076_,
                                        v___y_6077_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6147_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_6147_, 1);
                                        v___y_6127_ = v___y_6074_;
                                        v___y_6128_ = v___y_6075_;
                                        v___y_6129_ = v___y_6076_;
                                        v___y_6130_ = v___y_6077_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_numIndices_6101_);
                                        leanh::lean_dec(v_numParams_6100_);
                                        leanh::lean_dec_ref_known(v_x_6071_, 2);
                                        leanh::lean_dec_ref(v_x_6072_);
                                        leanh::lean_dec(v_varName_x3f_6070_);
                                        leanh::lean_dec_ref(v___x_6069_);
                                        leanh::lean_dec_ref(v___x_6068_);
                                        leanh::lean_dec_ref(v_e_6067_);
                                        leanh::lean_dec(v_mvarId_6066_);
                                        v_a_6148_ = leanh::lean_ctor_get(v___x_6147_, 0);
                                        v_isSharedCheck_6155_ =
                                            (!leanh::lean_is_exclusive(v___x_6147_)) as u8;
                                        if v_isSharedCheck_6155_ == 0 {
                                            v___x_6150_ = v___x_6147_;
                                            v_isShared_6151_ = v_isSharedCheck_6155_;
                                            state = 8;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6148_);
                                            leanh::lean_dec(v___x_6147_);
                                            v___x_6150_ = leanh::lean_box(0);
                                            v_isShared_6151_ = v_isSharedCheck_6155_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___y_6127_ = v___y_6074_;
                                    v___y_6128_ = v___y_6075_;
                                    v___y_6129_ = v___y_6076_;
                                    v___y_6130_ = v___y_6077_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_6098_);
                                leanh::lean_dec_ref_known(v_x_6071_, 2);
                                leanh::lean_dec_ref(v_x_6072_);
                                leanh::lean_dec(v_varName_x3f_6070_);
                                leanh::lean_dec_ref(v___x_6069_);
                                leanh::lean_dec_ref(v___x_6068_);
                                leanh::lean_dec_ref(v_e_6067_);
                                v___y_6087_ = v___y_6074_;
                                v___y_6088_ = v___y_6075_;
                                v___y_6089_ = v___y_6076_;
                                v___y_6090_ = v___y_6077_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_6072_);
                        leanh::lean_dec_ref(v_x_6071_);
                        leanh::lean_dec(v_varName_x3f_6070_);
                        leanh::lean_dec_ref(v___x_6069_);
                        leanh::lean_dec_ref(v___x_6068_);
                        leanh::lean_dec_ref(v_e_6067_);
                        v___y_6087_ = v___y_6074_;
                        v___y_6088_ = v___y_6075_;
                        v___y_6089_ = v___y_6076_;
                        v___y_6090_ = v___y_6077_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6091_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
                v___x_6092_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_6085_,
                    v_mvarId_6066_,
                    v___x_6091_,
                    v___y_6087_,
                    v___y_6088_,
                    v___y_6089_,
                    v___y_6090_,
                );
                return v___x_6092_;
            }
            2 => {
                v___x_6107_ = leanh::lean_unsigned_to_nat(0);
                v___x_6108_ = l_Array_extract___redArg(v_x_6072_, v___x_6107_, v_numParams_6100_);
                v___x_6109_ = l_Lean_mkAppN(v_x_6071_, v___x_6108_);
                leanh::lean_dec_ref(v___x_6108_);
                leanh::lean_inc(v___y_6106_);
                leanh::lean_inc_ref(v___y_6105_);
                leanh::lean_inc(v___y_6104_);
                leanh::lean_inc_ref(v___y_6103_);
                leanh::lean_inc_ref(v___x_6109_);
                v___x_6110_ = lean_infer_type(
                    v___x_6109_,
                    v___y_6103_,
                    v___y_6104_,
                    v___y_6105_,
                    v___y_6106_,
                );
                if leanh::lean_obj_tag(v___x_6110_) == 0 {
                    v_a_6111_ = leanh::lean_ctor_get(v___x_6110_, 0);
                    leanh::lean_inc(v_a_6111_);
                    leanh::lean_dec_ref_known(v___x_6110_, 1);
                    v___x_6112_ = lean_array_get_size(v_x_6072_);
                    v___x_6113_ = lean_nat_sub(v___x_6112_, v_numIndices_6101_);
                    leanh::lean_dec(v_numIndices_6101_);
                    v___x_6114_ = l_Array_extract___redArg(v_x_6072_, v___x_6113_, v___x_6112_);
                    leanh::lean_dec_ref(v_x_6072_);
                    v___x_6115_ = leanh::lean_box((v___x_6096_) as usize);
                    v___f_6116_ = leanh::lean_alloc_closure(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed as *mut core::ffi::c_void, 16, 9);
                    leanh::lean_closure_set(v___f_6116_, 0, v_e_6067_);
                    leanh::lean_closure_set(v___f_6116_, 1, v_mvarId_6066_);
                    leanh::lean_closure_set(v___f_6116_, 2, v___x_6115_);
                    leanh::lean_closure_set(v___f_6116_, 3, v___x_6068_);
                    leanh::lean_closure_set(v___f_6116_, 4, v___x_6069_);
                    leanh::lean_closure_set(v___f_6116_, 5, v___x_6107_);
                    leanh::lean_closure_set(v___f_6116_, 6, v___x_6114_);
                    leanh::lean_closure_set(v___f_6116_, 7, v___x_6109_);
                    leanh::lean_closure_set(v___f_6116_, 8, v_varName_x3f_6070_);
                    v___x_6117_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_6111_, v___f_6116_, v___x_6096_, v___x_6096_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_);
                    return v___x_6117_;
                } else {
                    leanh::lean_dec_ref(v___x_6109_);
                    leanh::lean_dec(v_numIndices_6101_);
                    leanh::lean_dec_ref(v_x_6072_);
                    leanh::lean_dec(v_varName_x3f_6070_);
                    leanh::lean_dec_ref(v___x_6069_);
                    leanh::lean_dec_ref(v___x_6068_);
                    leanh::lean_dec_ref(v_e_6067_);
                    leanh::lean_dec(v_mvarId_6066_);
                    v_a_6118_ = leanh::lean_ctor_get(v___x_6110_, 0);
                    v_isSharedCheck_6125_ = (!leanh::lean_is_exclusive(v___x_6110_)) as u8;
                    if v_isSharedCheck_6125_ == 0 {
                        v___x_6120_ = v___x_6110_;
                        v_isShared_6121_ = v_isSharedCheck_6125_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6118_);
                        leanh::lean_dec(v___x_6110_);
                        v___x_6120_ = leanh::lean_box(0);
                        v_isShared_6121_ = v_isSharedCheck_6125_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6121_ == 0 {
                    v___x_6123_ = v___x_6120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
                    v___x_6123_ = v_reuseFailAlloc_6124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6123_;
            }
            5 => {
                v___x_6131_ = lean_array_get_size(v_x_6072_);
                v___x_6132_ = lean_nat_add(v_numIndices_6101_, v_numParams_6100_);
                v___x_6133_ = lean_nat_dec_eq(v___x_6131_, v___x_6132_);
                leanh::lean_dec(v___x_6132_);
                if v___x_6133_ == 0 {
                    v___x_6134_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
                    leanh::lean_inc(v_mvarId_6066_);
                    v___x_6135_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_6085_,
                        v_mvarId_6066_,
                        v___x_6134_,
                        v___y_6127_,
                        v___y_6128_,
                        v___y_6129_,
                        v___y_6130_,
                    );
                    if leanh::lean_obj_tag(v___x_6135_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6135_, 1);
                        v___y_6103_ = v___y_6127_;
                        v___y_6104_ = v___y_6128_;
                        v___y_6105_ = v___y_6129_;
                        v___y_6106_ = v___y_6130_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_numIndices_6101_);
                        leanh::lean_dec(v_numParams_6100_);
                        leanh::lean_dec_ref_known(v_x_6071_, 2);
                        leanh::lean_dec_ref(v_x_6072_);
                        leanh::lean_dec(v_varName_x3f_6070_);
                        leanh::lean_dec_ref(v___x_6069_);
                        leanh::lean_dec_ref(v___x_6068_);
                        leanh::lean_dec_ref(v_e_6067_);
                        leanh::lean_dec(v_mvarId_6066_);
                        v_a_6136_ = leanh::lean_ctor_get(v___x_6135_, 0);
                        v_isSharedCheck_6143_ =
                            (!leanh::lean_is_exclusive(v___x_6135_)) as u8;
                        if v_isSharedCheck_6143_ == 0 {
                            v___x_6138_ = v___x_6135_;
                            v_isShared_6139_ = v_isSharedCheck_6143_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6136_);
                            leanh::lean_dec(v___x_6135_);
                            v___x_6138_ = leanh::lean_box(0);
                            v_isShared_6139_ = v_isSharedCheck_6143_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___y_6103_ = v___y_6127_;
                    v___y_6104_ = v___y_6128_;
                    v___y_6105_ = v___y_6129_;
                    v___y_6106_ = v___y_6130_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_6139_ == 0 {
                    v___x_6141_ = v___x_6138_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
                    v___x_6141_ = v_reuseFailAlloc_6142_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6141_;
            }
            8 => {
                if v_isShared_6151_ == 0 {
                    v___x_6153_ = v___x_6150_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
                    v___x_6153_ = v_reuseFailAlloc_6154_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(
    mut v_mvarId_6156_: *mut leanh::LeanObject,
    mut v_e_6157_: *mut leanh::LeanObject,
    mut v___x_6158_: *mut leanh::LeanObject,
    mut v___x_6159_: *mut leanh::LeanObject,
    mut v_varName_x3f_6160_: *mut leanh::LeanObject,
    mut v_x_6161_: *mut leanh::LeanObject,
    mut v_x_6162_: *mut leanh::LeanObject,
    mut v_x_6163_: *mut leanh::LeanObject,
    mut v___y_6164_: *mut leanh::LeanObject,
    mut v___y_6165_: *mut leanh::LeanObject,
    mut v___y_6166_: *mut leanh::LeanObject,
    mut v___y_6167_: *mut leanh::LeanObject,
    mut v___y_6168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6169_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(
        v_mvarId_6156_,
        v_e_6157_,
        v___x_6158_,
        v___x_6159_,
        v_varName_x3f_6160_,
        v_x_6161_,
        v_x_6162_,
        v_x_6163_,
        v___y_6164_,
        v___y_6165_,
        v___y_6166_,
        v___y_6167_,
    );
    leanh::lean_dec(v___y_6167_);
    leanh::lean_dec_ref(v___y_6166_);
    leanh::lean_dec(v___y_6165_);
    leanh::lean_dec_ref(v___y_6164_);
    return v_res_6169_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices_x27___lam__0(
    mut v_mvarId_6170_: *mut leanh::LeanObject,
    mut v_e_6171_: *mut leanh::LeanObject,
    mut v_varName_x3f_6172_: *mut leanh::LeanObject,
    mut v___y_6173_: *mut leanh::LeanObject,
    mut v___y_6174_: *mut leanh::LeanObject,
    mut v___y_6175_: *mut leanh::LeanObject,
    mut v___y_6176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6199_: u8 = 0;
    let mut v_a_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6203_: u8 = 0;
    let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6207_: u8 = 0;
    let mut v_a_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6211_: u8 = 0;
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6178_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1;
                leanh::lean_inc(v_mvarId_6170_);
                v___x_6179_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6170_,
                    v___x_6178_,
                    v___y_6173_,
                    v___y_6174_,
                    v___y_6175_,
                    v___y_6176_,
                );
                if leanh::lean_obj_tag(v___x_6179_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6179_, 1);
                    v_lctx_6180_ = leanh::lean_ctor_get(v___y_6173_, 2);
                    leanh::lean_inc_ref(v_lctx_6180_);
                    v_localInstances_6181_ = leanh::lean_ctor_get(v___y_6173_, 3);
                    leanh::lean_inc_ref(v_localInstances_6181_);
                    leanh::lean_inc(v___y_6176_);
                    leanh::lean_inc_ref(v___y_6175_);
                    leanh::lean_inc(v___y_6174_);
                    leanh::lean_inc_ref(v___y_6173_);
                    leanh::lean_inc_ref(v_e_6171_);
                    v___x_6182_ = lean_infer_type(
                        v_e_6171_,
                        v___y_6173_,
                        v___y_6174_,
                        v___y_6175_,
                        v___y_6176_,
                    );
                    if leanh::lean_obj_tag(v___x_6182_) == 0 {
                        v_a_6183_ = leanh::lean_ctor_get(v___x_6182_, 0);
                        leanh::lean_inc(v_a_6183_);
                        leanh::lean_dec_ref_known(v___x_6182_, 1);
                        v___x_6184_ = l_Lean_Meta_whnfD(
                            v_a_6183_,
                            v___y_6173_,
                            v___y_6174_,
                            v___y_6175_,
                            v___y_6176_,
                        );
                        if leanh::lean_obj_tag(v___x_6184_) == 0 {
                            v_a_6185_ = leanh::lean_ctor_get(v___x_6184_, 0);
                            leanh::lean_inc(v_a_6185_);
                            leanh::lean_dec_ref_known(v___x_6184_, 1);
                            v_dummy_6186_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getInductiveUniverseAndParams___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once
                                ),
                                _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0,
                            );
                            v_nargs_6187_ = l_Lean_Expr_getAppNumArgs(v_a_6185_);
                            leanh::lean_inc(v_nargs_6187_);
                            v___x_6188_ = lean_mk_array(v_nargs_6187_, v_dummy_6186_);
                            v___x_6189_ = leanh::lean_unsigned_to_nat(1);
                            v___x_6190_ = lean_nat_sub(v_nargs_6187_, v___x_6189_);
                            leanh::lean_dec(v_nargs_6187_);
                            v___x_6191_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_6170_, v_e_6171_, v_lctx_6180_, v_localInstances_6181_, v_varName_x3f_6172_, v_a_6185_, v___x_6188_, v___x_6190_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
                            leanh::lean_dec(v___y_6176_);
                            leanh::lean_dec_ref(v___y_6175_);
                            leanh::lean_dec(v___y_6174_);
                            leanh::lean_dec_ref(v___y_6173_);
                            return v___x_6191_;
                        } else {
                            leanh::lean_dec_ref(v_localInstances_6181_);
                            leanh::lean_dec_ref(v_lctx_6180_);
                            leanh::lean_dec(v___y_6176_);
                            leanh::lean_dec_ref(v___y_6175_);
                            leanh::lean_dec(v___y_6174_);
                            leanh::lean_dec_ref(v___y_6173_);
                            leanh::lean_dec(v_varName_x3f_6172_);
                            leanh::lean_dec_ref(v_e_6171_);
                            leanh::lean_dec(v_mvarId_6170_);
                            v_a_6192_ = leanh::lean_ctor_get(v___x_6184_, 0);
                            v_isSharedCheck_6199_ =
                                (!leanh::lean_is_exclusive(v___x_6184_)) as u8;
                            if v_isSharedCheck_6199_ == 0 {
                                v___x_6194_ = v___x_6184_;
                                v_isShared_6195_ = v_isSharedCheck_6199_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6192_);
                                leanh::lean_dec(v___x_6184_);
                                v___x_6194_ = leanh::lean_box(0);
                                v_isShared_6195_ = v_isSharedCheck_6199_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_localInstances_6181_);
                        leanh::lean_dec_ref(v_lctx_6180_);
                        leanh::lean_dec(v___y_6176_);
                        leanh::lean_dec_ref(v___y_6175_);
                        leanh::lean_dec(v___y_6174_);
                        leanh::lean_dec_ref(v___y_6173_);
                        leanh::lean_dec(v_varName_x3f_6172_);
                        leanh::lean_dec_ref(v_e_6171_);
                        leanh::lean_dec(v_mvarId_6170_);
                        v_a_6200_ = leanh::lean_ctor_get(v___x_6182_, 0);
                        v_isSharedCheck_6207_ =
                            (!leanh::lean_is_exclusive(v___x_6182_)) as u8;
                        if v_isSharedCheck_6207_ == 0 {
                            v___x_6202_ = v___x_6182_;
                            v_isShared_6203_ = v_isSharedCheck_6207_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6200_);
                            leanh::lean_dec(v___x_6182_);
                            v___x_6202_ = leanh::lean_box(0);
                            v_isShared_6203_ = v_isSharedCheck_6207_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_6176_);
                    leanh::lean_dec_ref(v___y_6175_);
                    leanh::lean_dec(v___y_6174_);
                    leanh::lean_dec_ref(v___y_6173_);
                    leanh::lean_dec(v_varName_x3f_6172_);
                    leanh::lean_dec_ref(v_e_6171_);
                    leanh::lean_dec(v_mvarId_6170_);
                    v_a_6208_ = leanh::lean_ctor_get(v___x_6179_, 0);
                    v_isSharedCheck_6215_ = (!leanh::lean_is_exclusive(v___x_6179_)) as u8;
                    if v_isSharedCheck_6215_ == 0 {
                        v___x_6210_ = v___x_6179_;
                        v_isShared_6211_ = v_isSharedCheck_6215_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6208_);
                        leanh::lean_dec(v___x_6179_);
                        v___x_6210_ = leanh::lean_box(0);
                        v_isShared_6211_ = v_isSharedCheck_6215_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6195_ == 0 {
                    v___x_6197_ = v___x_6194_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
                    v___x_6197_ = v_reuseFailAlloc_6198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6197_;
            }
            3 => {
                if v_isShared_6203_ == 0 {
                    v___x_6205_ = v___x_6202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_a_6200_);
                    v___x_6205_ = v_reuseFailAlloc_6206_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6205_;
            }
            5 => {
                if v_isShared_6211_ == 0 {
                    v___x_6213_ = v___x_6210_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_a_6208_);
                    v___x_6213_ = v_reuseFailAlloc_6214_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(
    mut v_mvarId_6216_: *mut leanh::LeanObject,
    mut v_e_6217_: *mut leanh::LeanObject,
    mut v_varName_x3f_6218_: *mut leanh::LeanObject,
    mut v___y_6219_: *mut leanh::LeanObject,
    mut v___y_6220_: *mut leanh::LeanObject,
    mut v___y_6221_: *mut leanh::LeanObject,
    mut v___y_6222_: *mut leanh::LeanObject,
    mut v___y_6223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6224_ = l_Lean_Meta_generalizeIndices_x27___lam__0(
        v_mvarId_6216_,
        v_e_6217_,
        v_varName_x3f_6218_,
        v___y_6219_,
        v___y_6220_,
        v___y_6221_,
        v___y_6222_,
    );
    return v_res_6224_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices_x27(
    mut v_mvarId_6225_: *mut leanh::LeanObject,
    mut v_e_6226_: *mut leanh::LeanObject,
    mut v_varName_x3f_6227_: *mut leanh::LeanObject,
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
    mut v_a_6230_: *mut leanh::LeanObject,
    mut v_a_6231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_6225_);
    v___f_6233_ = leanh::lean_alloc_closure(
        l_Lean_Meta_generalizeIndices_x27___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_6233_, 0, v_mvarId_6225_);
    leanh::lean_closure_set(v___f_6233_, 1, v_e_6226_);
    leanh::lean_closure_set(v___f_6233_, 2, v_varName_x3f_6227_);
    v___x_6234_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_6225_,
        v___f_6233_,
        v_a_6228_,
        v_a_6229_,
        v_a_6230_,
        v_a_6231_,
    );
    return v___x_6234_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices_x27___boxed(
    mut v_mvarId_6235_: *mut leanh::LeanObject,
    mut v_e_6236_: *mut leanh::LeanObject,
    mut v_varName_x3f_6237_: *mut leanh::LeanObject,
    mut v_a_6238_: *mut leanh::LeanObject,
    mut v_a_6239_: *mut leanh::LeanObject,
    mut v_a_6240_: *mut leanh::LeanObject,
    mut v_a_6241_: *mut leanh::LeanObject,
    mut v_a_6242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6243_ = l_Lean_Meta_generalizeIndices_x27(
        v_mvarId_6235_,
        v_e_6236_,
        v_varName_x3f_6237_,
        v_a_6238_,
        v_a_6239_,
        v_a_6240_,
        v_a_6241_,
    );
    leanh::lean_dec(v_a_6241_);
    leanh::lean_dec_ref(v_a_6240_);
    leanh::lean_dec(v_a_6239_);
    leanh::lean_dec_ref(v_a_6238_);
    return v_res_6243_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices___lam__0(
    mut v_fvarId_6244_: *mut leanh::LeanObject,
    mut v_mvarId_6245_: *mut leanh::LeanObject,
    mut v___y_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6251_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_6244_,
                    v___y_6246_,
                    v___y_6248_,
                    v___y_6249_,
                );
                if leanh::lean_obj_tag(v___x_6251_) == 0 {
                    v_a_6252_ = leanh::lean_ctor_get(v___x_6251_, 0);
                    leanh::lean_inc_n(v_a_6252_, 2);
                    leanh::lean_dec_ref_known(v___x_6251_, 1);
                    v___x_6253_ = l_Lean_LocalDecl_toExpr(v_a_6252_);
                    v___x_6254_ = l_Lean_LocalDecl_userName(v_a_6252_);
                    leanh::lean_dec(v_a_6252_);
                    v___x_6255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6255_, 0, v___x_6254_);
                    v___x_6256_ = l_Lean_Meta_generalizeIndices_x27(
                        v_mvarId_6245_,
                        v___x_6253_,
                        v___x_6255_,
                        v___y_6246_,
                        v___y_6247_,
                        v___y_6248_,
                        v___y_6249_,
                    );
                    return v___x_6256_;
                } else {
                    leanh::lean_dec(v_mvarId_6245_);
                    v_a_6257_ = leanh::lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6264_ = (!leanh::lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6264_ == 0 {
                        v___x_6259_ = v___x_6251_;
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6257_);
                        leanh::lean_dec(v___x_6251_);
                        v___x_6259_ = leanh::lean_box(0);
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6260_ == 0 {
                    v___x_6262_ = v___x_6259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
                    v___x_6262_ = v_reuseFailAlloc_6263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeIndices___lam__0___boxed(
    mut v_fvarId_6265_: *mut leanh::LeanObject,
    mut v_mvarId_6266_: *mut leanh::LeanObject,
    mut v___y_6267_: *mut leanh::LeanObject,
    mut v___y_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
    mut v___y_6270_: *mut leanh::LeanObject,
    mut v___y_6271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6272_ = l_Lean_Meta_generalizeIndices___lam__0(
        v_fvarId_6265_,
        v_mvarId_6266_,
        v___y_6267_,
        v___y_6268_,
        v___y_6269_,
        v___y_6270_,
    );
    leanh::lean_dec(v___y_6270_);
    leanh::lean_dec_ref(v___y_6269_);
    leanh::lean_dec(v___y_6268_);
    leanh::lean_dec_ref(v___y_6267_);
    return v_res_6272_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices(
    mut v_mvarId_6273_: *mut leanh::LeanObject,
    mut v_fvarId_6274_: *mut leanh::LeanObject,
    mut v_a_6275_: *mut leanh::LeanObject,
    mut v_a_6276_: *mut leanh::LeanObject,
    mut v_a_6277_: *mut leanh::LeanObject,
    mut v_a_6278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_6273_);
    v___f_6280_ = leanh::lean_alloc_closure(
        l_Lean_Meta_generalizeIndices___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_6280_, 0, v_fvarId_6274_);
    leanh::lean_closure_set(v___f_6280_, 1, v_mvarId_6273_);
    v___x_6281_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_6273_,
        v___f_6280_,
        v_a_6275_,
        v_a_6276_,
        v_a_6277_,
        v_a_6278_,
    );
    return v___x_6281_;
}
pub unsafe fn l_Lean_Meta_generalizeIndices___boxed(
    mut v_mvarId_6282_: *mut leanh::LeanObject,
    mut v_fvarId_6283_: *mut leanh::LeanObject,
    mut v_a_6284_: *mut leanh::LeanObject,
    mut v_a_6285_: *mut leanh::LeanObject,
    mut v_a_6286_: *mut leanh::LeanObject,
    mut v_a_6287_: *mut leanh::LeanObject,
    mut v_a_6288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6289_ = l_Lean_Meta_generalizeIndices(
        v_mvarId_6282_,
        v_fvarId_6283_,
        v_a_6284_,
        v_a_6285_,
        v_a_6286_,
        v_a_6287_,
    );
    leanh::lean_dec(v_a_6287_);
    leanh::lean_dec_ref(v_a_6286_);
    leanh::lean_dec(v_a_6285_);
    leanh::lean_dec_ref(v_a_6284_);
    return v_res_6289_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(
    mut v___x_6291_: *mut leanh::LeanObject,
    mut v_a_6292_: *mut leanh::LeanObject,
    mut v_x_6293_: *mut leanh::LeanObject,
    mut v_x_6294_: *mut leanh::LeanObject,
    mut v_x_6295_: *mut leanh::LeanObject,
    mut v___y_6296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: u8 = 0;
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v_val_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6319_: u8 = 0;
    let mut v_toConstantVal_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: u8 = 0;
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: u8 = 0;
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6349_: u8 = 0;
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6293_) == 5 {
                    v_fn_6301_ = leanh::lean_ctor_get(v_x_6293_, 0);
                    leanh::lean_inc_ref(v_fn_6301_);
                    v_arg_6302_ = leanh::lean_ctor_get(v_x_6293_, 1);
                    leanh::lean_inc_ref(v_arg_6302_);
                    leanh::lean_dec_ref_known(v_x_6293_, 2);
                    v___x_6303_ = lean_array_set(v_x_6294_, v_x_6295_, v_arg_6302_);
                    v___x_6304_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6305_ = lean_nat_sub(v_x_6295_, v___x_6304_);
                    leanh::lean_dec(v_x_6295_);
                    v_x_6293_ = v_fn_6301_;
                    v_x_6294_ = v___x_6303_;
                    v_x_6295_ = v___x_6305_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6295_);
                    if leanh::lean_obj_tag(v_x_6293_) == 4 {
                        v_declName_6307_ = leanh::lean_ctor_get(v_x_6293_, 0);
                        v___x_6308_ = lean_st_ref_get(v___y_6296_);
                        v_env_6309_ = leanh::lean_ctor_get(v___x_6308_, 0);
                        leanh::lean_inc_ref(v_env_6309_);
                        leanh::lean_dec(v___x_6308_);
                        v___x_6310_ = 0;
                        leanh::lean_inc(v_declName_6307_);
                        v___x_6311_ =
                            l_Lean_Environment_find_x3f(v_env_6309_, v_declName_6307_, v___x_6310_);
                        if leanh::lean_obj_tag(v___x_6311_) == 0 {
                            leanh::lean_dec_ref_known(v_x_6293_, 2);
                            leanh::lean_dec_ref(v_x_6294_);
                            leanh::lean_dec_ref(v_a_6292_);
                            leanh::lean_dec_ref(v___x_6291_);
                            state = 1;
                            continue;
                        } else {
                            v_val_6312_ = leanh::lean_ctor_get(v___x_6311_, 0);
                            v_isSharedCheck_6350_ =
                                (!leanh::lean_is_exclusive(v___x_6311_)) as u8;
                            if v_isSharedCheck_6350_ == 0 {
                                v___x_6314_ = v___x_6311_;
                                v_isShared_6315_ = v_isSharedCheck_6350_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_6312_);
                                leanh::lean_dec(v___x_6311_);
                                v___x_6314_ = leanh::lean_box(0);
                                v_isShared_6315_ = v_isSharedCheck_6350_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_6294_);
                        leanh::lean_dec_ref(v_x_6293_);
                        leanh::lean_dec_ref(v_a_6292_);
                        leanh::lean_dec_ref(v___x_6291_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6299_ = leanh::lean_box(0);
                v___x_6300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6300_, 0, v___x_6299_);
                return v___x_6300_;
            }
            2 => {
                if leanh::lean_obj_tag(v_val_6312_) == 5 {
                    v_val_6316_ = leanh::lean_ctor_get(v_val_6312_, 0);
                    v_isSharedCheck_6349_ = (!leanh::lean_is_exclusive(v_val_6312_)) as u8;
                    if v_isSharedCheck_6349_ == 0 {
                        v___x_6318_ = v_val_6312_;
                        v_isShared_6319_ = v_isSharedCheck_6349_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6316_);
                        leanh::lean_dec(v_val_6312_);
                        v___x_6318_ = leanh::lean_box(0);
                        v_isShared_6319_ = v_isSharedCheck_6349_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6314_);
                    leanh::lean_dec(v_val_6312_);
                    leanh::lean_dec_ref_known(v_x_6293_, 2);
                    leanh::lean_dec_ref(v_x_6294_);
                    leanh::lean_dec_ref(v_a_6292_);
                    leanh::lean_dec_ref(v___x_6291_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_toConstantVal_6320_ = leanh::lean_ctor_get(v_val_6316_, 0);
                v_numParams_6321_ = leanh::lean_ctor_get(v_val_6316_, 1);
                v_numIndices_6322_ = leanh::lean_ctor_get(v_val_6316_, 2);
                v_ctors_6323_ = leanh::lean_ctor_get(v_val_6316_, 4);
                v___x_6324_ = lean_array_get_size(v_x_6294_);
                v___x_6325_ = lean_nat_add(v_numIndices_6322_, v_numParams_6321_);
                v___x_6326_ = lean_nat_dec_eq(v___x_6324_, v___x_6325_);
                leanh::lean_dec(v___x_6325_);
                if v___x_6326_ == 0 {
                    leanh::lean_dec_ref(v_val_6316_);
                    leanh::lean_del_object(v___x_6314_);
                    leanh::lean_dec_ref_known(v_x_6293_, 2);
                    leanh::lean_dec_ref(v_x_6294_);
                    leanh::lean_dec_ref(v_a_6292_);
                    leanh::lean_dec_ref(v___x_6291_);
                    v___x_6327_ = leanh::lean_box(0);
                    if v_isShared_6319_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6318_, 0);
                        leanh::lean_ctor_set(v___x_6318_, 0, v___x_6327_);
                        v___x_6329_ = v___x_6318_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6330_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6327_);
                        v___x_6329_ = v_reuseFailAlloc_6330_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_name_6331_ = leanh::lean_ctor_get(v_toConstantVal_6320_, 0);
                    v___x_6332_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0;
                    leanh::lean_inc(v_name_6331_);
                    v___x_6333_ = l_Lean_Name_str___override(v_name_6331_, v___x_6332_);
                    v___x_6334_ =
                        l_Lean_Environment_contains(v___x_6291_, v___x_6333_, v___x_6326_);
                    if v___x_6334_ == 0 {
                        leanh::lean_dec_ref(v_val_6316_);
                        leanh::lean_del_object(v___x_6314_);
                        leanh::lean_dec_ref_known(v_x_6293_, 2);
                        leanh::lean_dec_ref(v_x_6294_);
                        leanh::lean_dec_ref(v_a_6292_);
                        v___x_6335_ = leanh::lean_box(0);
                        if v_isShared_6319_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_6318_, 0);
                            leanh::lean_ctor_set(v___x_6318_, 0, v___x_6335_);
                            v___x_6337_ = v___x_6318_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_6338_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6338_, 0, v___x_6335_);
                            v___x_6337_ = v_reuseFailAlloc_6338_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_6339_ = l_List_lengthTR___redArg(v_ctors_6323_);
                        v___x_6340_ = lean_nat_sub(v___x_6324_, v_numIndices_6322_);
                        v___x_6341_ = l_Array_extract___redArg(v_x_6294_, v___x_6340_, v___x_6324_);
                        v___x_6342_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v___x_6342_, 0, v_val_6316_);
                        leanh::lean_ctor_set(v___x_6342_, 1, v___x_6339_);
                        leanh::lean_ctor_set(v___x_6342_, 2, v_a_6292_);
                        leanh::lean_ctor_set(v___x_6342_, 3, v_x_6293_);
                        leanh::lean_ctor_set(v___x_6342_, 4, v_x_6294_);
                        leanh::lean_ctor_set(v___x_6342_, 5, v___x_6341_);
                        if v_isShared_6315_ == 0 {
                            leanh::lean_ctor_set(v___x_6314_, 0, v___x_6342_);
                            v___x_6344_ = v___x_6314_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6348_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6348_, 0, v___x_6342_);
                            v___x_6344_ = v_reuseFailAlloc_6348_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_6329_;
            }
            5 => {
                return v___x_6337_;
            }
            6 => {
                if v_isShared_6319_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6318_, 0);
                    leanh::lean_ctor_set(v___x_6318_, 0, v___x_6344_);
                    v___x_6346_ = v___x_6318_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6347_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6347_, 0, v___x_6344_);
                    v___x_6346_ = v_reuseFailAlloc_6347_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(
    mut v___x_6351_: *mut leanh::LeanObject,
    mut v_a_6352_: *mut leanh::LeanObject,
    mut v_x_6353_: *mut leanh::LeanObject,
    mut v_x_6354_: *mut leanh::LeanObject,
    mut v_x_6355_: *mut leanh::LeanObject,
    mut v___y_6356_: *mut leanh::LeanObject,
    mut v___y_6357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6358_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_6351_, v_a_6352_, v_x_6353_, v_x_6354_, v_x_6355_, v___y_6356_);
    leanh::lean_dec(v___y_6356_);
    return v_res_6358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(
    mut v_majorFVarId_6359_: *mut leanh::LeanObject,
    mut v_a_6360_: *mut leanh::LeanObject,
    mut v_a_6361_: *mut leanh::LeanObject,
    mut v_a_6362_: *mut leanh::LeanObject,
    mut v_a_6363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: u8 = 0;
    let mut v___x_6372_: u8 = 0;
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: u8 = 0;
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6389_: u8 = 0;
    let mut v___x_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6393_: u8 = 0;
    let mut v_a_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6397_: u8 = 0;
    let mut v___x_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6365_ = lean_st_ref_get(v_a_6363_);
                v_env_6369_ = leanh::lean_ctor_get(v___x_6365_, 0);
                leanh::lean_inc_ref_n(v_env_6369_, 2);
                leanh::lean_dec(v___x_6365_);
                v___x_6370_ =
                    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
                v___x_6371_ = 1;
                v___x_6372_ = l_Lean_Environment_contains(v_env_6369_, v___x_6370_, v___x_6371_);
                if v___x_6372_ == 0 {
                    leanh::lean_dec_ref(v_env_6369_);
                    leanh::lean_dec(v_majorFVarId_6359_);
                    state = 1;
                    continue;
                } else {
                    v___x_6373_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
                    leanh::lean_inc_ref(v_env_6369_);
                    v___x_6374_ =
                        l_Lean_Environment_contains(v_env_6369_, v___x_6373_, v___x_6372_);
                    if v___x_6374_ == 0 {
                        leanh::lean_dec_ref(v_env_6369_);
                        leanh::lean_dec(v_majorFVarId_6359_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6375_ = l_Lean_FVarId_getDecl___redArg(
                            v_majorFVarId_6359_,
                            v_a_6360_,
                            v_a_6362_,
                            v_a_6363_,
                        );
                        if leanh::lean_obj_tag(v___x_6375_) == 0 {
                            v_a_6376_ = leanh::lean_ctor_get(v___x_6375_, 0);
                            leanh::lean_inc(v_a_6376_);
                            leanh::lean_dec_ref_known(v___x_6375_, 1);
                            v___x_6377_ = l_Lean_LocalDecl_type(v_a_6376_);
                            leanh::lean_inc(v_a_6363_);
                            leanh::lean_inc_ref(v_a_6362_);
                            leanh::lean_inc(v_a_6361_);
                            leanh::lean_inc_ref(v_a_6360_);
                            v___x_6378_ =
                                lean_whnf(v___x_6377_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_);
                            if leanh::lean_obj_tag(v___x_6378_) == 0 {
                                v_a_6379_ = leanh::lean_ctor_get(v___x_6378_, 0);
                                leanh::lean_inc(v_a_6379_);
                                leanh::lean_dec_ref_known(v___x_6378_, 1);
                                v_dummy_6380_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getInductiveUniverseAndParams___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once
                                    ),
                                    _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0,
                                );
                                v_nargs_6381_ = l_Lean_Expr_getAppNumArgs(v_a_6379_);
                                leanh::lean_inc(v_nargs_6381_);
                                v___x_6382_ = lean_mk_array(v_nargs_6381_, v_dummy_6380_);
                                v___x_6383_ = leanh::lean_unsigned_to_nat(1);
                                v___x_6384_ = lean_nat_sub(v_nargs_6381_, v___x_6383_);
                                leanh::lean_dec(v_nargs_6381_);
                                v___x_6385_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_6369_, v_a_6376_, v_a_6379_, v___x_6382_, v___x_6384_, v_a_6363_);
                                return v___x_6385_;
                            } else {
                                leanh::lean_dec(v_a_6376_);
                                leanh::lean_dec_ref(v_env_6369_);
                                v_a_6386_ = leanh::lean_ctor_get(v___x_6378_, 0);
                                v_isSharedCheck_6393_ =
                                    (!leanh::lean_is_exclusive(v___x_6378_)) as u8;
                                if v_isSharedCheck_6393_ == 0 {
                                    v___x_6388_ = v___x_6378_;
                                    v_isShared_6389_ = v_isSharedCheck_6393_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6386_);
                                    leanh::lean_dec(v___x_6378_);
                                    v___x_6388_ = leanh::lean_box(0);
                                    v_isShared_6389_ = v_isSharedCheck_6393_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_env_6369_);
                            v_a_6394_ = leanh::lean_ctor_get(v___x_6375_, 0);
                            v_isSharedCheck_6401_ =
                                (!leanh::lean_is_exclusive(v___x_6375_)) as u8;
                            if v_isSharedCheck_6401_ == 0 {
                                v___x_6396_ = v___x_6375_;
                                v_isShared_6397_ = v_isSharedCheck_6401_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6394_);
                                leanh::lean_dec(v___x_6375_);
                                v___x_6396_ = leanh::lean_box(0);
                                v_isShared_6397_ = v_isSharedCheck_6401_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6367_ = leanh::lean_box(0);
                v___x_6368_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6368_, 0, v___x_6367_);
                return v___x_6368_;
            }
            2 => {
                if v_isShared_6389_ == 0 {
                    v___x_6391_ = v___x_6388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_a_6386_);
                    v___x_6391_ = v_reuseFailAlloc_6392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6391_;
            }
            4 => {
                if v_isShared_6397_ == 0 {
                    v___x_6399_ = v___x_6396_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_a_6394_);
                    v___x_6399_ = v_reuseFailAlloc_6400_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(
    mut v_majorFVarId_6402_: *mut leanh::LeanObject,
    mut v_a_6403_: *mut leanh::LeanObject,
    mut v_a_6404_: *mut leanh::LeanObject,
    mut v_a_6405_: *mut leanh::LeanObject,
    mut v_a_6406_: *mut leanh::LeanObject,
    mut v_a_6407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6408_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(
        v_majorFVarId_6402_,
        v_a_6403_,
        v_a_6404_,
        v_a_6405_,
        v_a_6406_,
    );
    leanh::lean_dec(v_a_6406_);
    leanh::lean_dec_ref(v_a_6405_);
    leanh::lean_dec(v_a_6404_);
    leanh::lean_dec_ref(v_a_6403_);
    return v_res_6408_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(
    mut v___x_6409_: *mut leanh::LeanObject,
    mut v_a_6410_: *mut leanh::LeanObject,
    mut v_x_6411_: *mut leanh::LeanObject,
    mut v_x_6412_: *mut leanh::LeanObject,
    mut v_x_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6419_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_6409_, v_a_6410_, v_x_6411_, v_x_6412_, v_x_6413_, v___y_6417_);
    return v___x_6419_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(
    mut v___x_6420_: *mut leanh::LeanObject,
    mut v_a_6421_: *mut leanh::LeanObject,
    mut v_x_6422_: *mut leanh::LeanObject,
    mut v_x_6423_: *mut leanh::LeanObject,
    mut v_x_6424_: *mut leanh::LeanObject,
    mut v___y_6425_: *mut leanh::LeanObject,
    mut v___y_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
    mut v___y_6429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_6420_, v_a_6421_, v_x_6422_, v_x_6423_, v_x_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    leanh::lean_dec(v___y_6428_);
    leanh::lean_dec_ref(v___y_6427_);
    leanh::lean_dec(v___y_6426_);
    leanh::lean_dec_ref(v___y_6425_);
    return v_res_6430_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(
    mut v___x_6431_: *mut leanh::LeanObject,
    mut v_i_6432_: *mut leanh::LeanObject,
    mut v_n_6433_: *mut leanh::LeanObject,
    mut v_i_6434_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6436_: u8 = 0;
    let mut v___x_6437_: u8 = 0;
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: u8 = 0;
    let mut v_one_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6435_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6436_ = lean_nat_dec_eq(v_i_6434_, v_zero_6435_);
                if v_isZero_6436_ == 1 {
                    leanh::lean_dec(v_i_6434_);
                    v___x_6437_ = 0;
                    return v___x_6437_;
                } else {
                    v___x_6438_ = lean_nat_sub(v_n_6433_, v_i_6434_);
                    v___x_6439_ = lean_array_fget_borrowed(v___x_6431_, v_i_6432_);
                    v___x_6440_ = lean_array_fget_borrowed(v___x_6431_, v___x_6438_);
                    leanh::lean_dec(v___x_6438_);
                    v___x_6441_ = lean_expr_eqv(v___x_6439_, v___x_6440_);
                    if v___x_6441_ == 0 {
                        v_one_6442_ = leanh::lean_unsigned_to_nat(1);
                        v_n_6443_ = lean_nat_sub(v_i_6434_, v_one_6442_);
                        leanh::lean_dec(v_i_6434_);
                        v_i_6434_ = v_n_6443_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_6434_);
                        return v___x_6441_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(
    mut v___x_6445_: *mut leanh::LeanObject,
    mut v_i_6446_: *mut leanh::LeanObject,
    mut v_n_6447_: *mut leanh::LeanObject,
    mut v_i_6448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6449_: u8 = 0;
    let mut v_r_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6449_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_6445_, v_i_6446_, v_n_6447_, v_i_6448_);
    leanh::lean_dec(v_n_6447_);
    leanh::lean_dec(v_i_6446_);
    leanh::lean_dec_ref(v___x_6445_);
    v_r_6450_ = leanh::lean_box((v_res_6449_) as usize);
    return v_r_6450_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(
    mut v___x_6451_: *mut leanh::LeanObject,
    mut v_n_6452_: *mut leanh::LeanObject,
    mut v_i_6453_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6455_: u8 = 0;
    let mut v___x_6456_: u8 = 0;
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: u8 = 0;
    let mut v_one_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6454_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6455_ = lean_nat_dec_eq(v_i_6453_, v_zero_6454_);
                if v_isZero_6455_ == 1 {
                    leanh::lean_dec(v_i_6453_);
                    v___x_6456_ = 0;
                    return v___x_6456_;
                } else {
                    v___x_6457_ = lean_nat_sub(v_n_6452_, v_i_6453_);
                    leanh::lean_inc(v___x_6457_);
                    v___x_6458_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_6451_, v___x_6457_, v___x_6457_, v___x_6457_);
                    leanh::lean_dec(v___x_6457_);
                    if v___x_6458_ == 0 {
                        v_one_6459_ = leanh::lean_unsigned_to_nat(1);
                        v_n_6460_ = lean_nat_sub(v_i_6453_, v_one_6459_);
                        leanh::lean_dec(v_i_6453_);
                        v_i_6453_ = v_n_6460_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_6453_);
                        return v___x_6458_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(
    mut v___x_6462_: *mut leanh::LeanObject,
    mut v_n_6463_: *mut leanh::LeanObject,
    mut v_i_6464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6465_: u8 = 0;
    let mut v_r_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6465_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_6462_, v_n_6463_, v_i_6464_);
    leanh::lean_dec(v_n_6463_);
    leanh::lean_dec_ref(v___x_6462_);
    v_r_6466_ = leanh::lean_box((v_res_6465_) as usize);
    return v_r_6466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(
    mut v___x_6467_: *mut leanh::LeanObject,
    mut v_as_6468_: *mut leanh::LeanObject,
    mut v_i_6469_: usize,
    mut v_stop_6470_: usize,
) -> u8 {
    let mut v___x_6471_: u8 = 0;
    let mut v___x_6472_: u8 = 0;
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: u8 = 0;
    let mut v___x_6477_: usize = 0;
    let mut v___x_6478_: usize = 0;
    let mut v___x_6480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6471_ = lean_usize_dec_eq(v_i_6469_, v_stop_6470_);
                if v___x_6471_ == 0 {
                    v___x_6472_ = 1;
                    v___x_6473_ = lean_array_uget_borrowed(v_as_6468_, v_i_6469_);
                    v___x_6474_ = l_Lean_Expr_isFVar(v___x_6473_);
                    if v___x_6474_ == 0 {
                        return v___x_6472_;
                    } else {
                        v___x_6475_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6476_ = lean_nat_dec_eq(v___x_6467_, v___x_6475_);
                        if v___x_6476_ == 0 {
                            v___x_6477_ = 1usize;
                            v___x_6478_ = lean_usize_add(v_i_6469_, v___x_6477_);
                            v_i_6469_ = v___x_6478_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_6472_;
                        }
                    }
                } else {
                    v___x_6480_ = 0;
                    return v___x_6480_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(
    mut v___x_6481_: *mut leanh::LeanObject,
    mut v_as_6482_: *mut leanh::LeanObject,
    mut v_i_6483_: *mut leanh::LeanObject,
    mut v_stop_6484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6485_: usize = 0;
    let mut v_stop_boxed_6486_: usize = 0;
    let mut v_res_6487_: u8 = 0;
    let mut v_r_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6485_ = leanh::lean_unbox_usize(v_i_6483_);
    leanh::lean_dec(v_i_6483_);
    v_stop_boxed_6486_ = leanh::lean_unbox_usize(v_stop_6484_);
    leanh::lean_dec(v_stop_6484_);
    v_res_6487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_6481_, v_as_6482_, v_i_boxed_6485_, v_stop_boxed_6486_);
    leanh::lean_dec_ref(v_as_6482_);
    leanh::lean_dec(v___x_6481_);
    v_r_6488_ = leanh::lean_box((v_res_6487_) as usize);
    return v_r_6488_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(
    mut v_fvarId_6489_: *mut leanh::LeanObject,
    mut v___y_6490_: u8,
    mut v_as_6491_: *mut leanh::LeanObject,
    mut v_i_6492_: usize,
    mut v_stop_6493_: usize,
) -> u8 {
    let mut v___x_6494_: u8 = 0;
    let mut v___x_6495_: u8 = 0;
    let mut v___y_6497_: u8 = 0;
    let mut v___x_6498_: usize = 0;
    let mut v___x_6499_: usize = 0;
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: u8 = 0;
    let mut v___x_6504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6494_ = lean_usize_dec_eq(v_i_6492_, v_stop_6493_);
                if v___x_6494_ == 0 {
                    v___x_6495_ = 1;
                    v___x_6501_ = lean_array_uget_borrowed(v_as_6491_, v_i_6492_);
                    v___x_6502_ = l_Lean_Expr_fvarId_x21(v___x_6501_);
                    v___x_6503_ = l_Lean_instBEqFVarId_beq(v___x_6502_, v_fvarId_6489_);
                    leanh::lean_dec(v___x_6502_);
                    if v___x_6503_ == 0 {
                        v___y_6497_ = v___y_6490_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6497_ = v___x_6503_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6504_ = 0;
                    return v___x_6504_;
                }
            }
            1 => {
                if v___y_6497_ == 0 {
                    v___x_6498_ = 1usize;
                    v___x_6499_ = lean_usize_add(v_i_6492_, v___x_6498_);
                    v_i_6492_ = v___x_6499_;
                    state = 0;
                    continue;
                } else {
                    return v___x_6495_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(
    mut v_fvarId_6505_: *mut leanh::LeanObject,
    mut v___y_6506_: *mut leanh::LeanObject,
    mut v_as_6507_: *mut leanh::LeanObject,
    mut v_i_6508_: *mut leanh::LeanObject,
    mut v_stop_6509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9117__boxed_6510_: u8 = 0;
    let mut v_i_boxed_6511_: usize = 0;
    let mut v_stop_boxed_6512_: usize = 0;
    let mut v_res_6513_: u8 = 0;
    let mut v_r_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9117__boxed_6510_ = (leanh::lean_unbox(v___y_6506_) as u8);
    v_i_boxed_6511_ = leanh::lean_unbox_usize(v_i_6508_);
    leanh::lean_dec(v_i_6508_);
    v_stop_boxed_6512_ = leanh::lean_unbox_usize(v_stop_6509_);
    leanh::lean_dec(v_stop_6509_);
    v_res_6513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_6505_, v___y_9117__boxed_6510_, v_as_6507_, v_i_boxed_6511_, v_stop_boxed_6512_);
    leanh::lean_dec_ref(v_as_6507_);
    leanh::lean_dec(v_fvarId_6505_);
    v_r_6514_ = leanh::lean_box((v_res_6513_) as usize);
    return v_r_6514_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(
    mut v___x_6515_: *mut leanh::LeanObject,
    mut v___x_6516_: *mut leanh::LeanObject,
    mut v___x_6517_: u8,
    mut v___y_6518_: u8,
    mut v___x_6519_: *mut leanh::LeanObject,
    mut v_fvarId_6520_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: u8 = 0;
    let mut v___x_6524_: usize = 0;
    let mut v___x_6525_: usize = 0;
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: u8 = 0;
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6527_ = lean_nat_dec_lt(v___x_6515_, v___x_6516_);
                if v___x_6527_ == 0 {
                    leanh::lean_dec(v___x_6516_);
                    return v___x_6517_;
                } else {
                    v___x_6528_ = lean_array_get_size(v___x_6519_);
                    v___x_6529_ = lean_nat_dec_le(v___x_6516_, v___x_6528_);
                    if v___x_6529_ == 0 {
                        leanh::lean_dec(v___x_6516_);
                        v___y_6522_ = v___x_6528_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6522_ = v___x_6516_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6523_ = lean_nat_dec_lt(v___x_6515_, v___y_6522_);
                if v___x_6523_ == 0 {
                    leanh::lean_dec(v___y_6522_);
                    return v___x_6517_;
                } else {
                    v___x_6524_ = 0usize;
                    v___x_6525_ = lean_usize_of_nat(v___y_6522_);
                    leanh::lean_dec(v___y_6522_);
                    v___x_6526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_6520_, v___y_6518_, v___x_6519_, v___x_6524_, v___x_6525_);
                    if v___x_6526_ == 0 {
                        return v___x_6517_;
                    } else {
                        return v___y_6518_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(
    mut v___x_6530_: *mut leanh::LeanObject,
    mut v___x_6531_: *mut leanh::LeanObject,
    mut v___x_6532_: *mut leanh::LeanObject,
    mut v___y_6533_: *mut leanh::LeanObject,
    mut v___x_6534_: *mut leanh::LeanObject,
    mut v_fvarId_6535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9144__boxed_6536_: u8 = 0;
    let mut v___y_9145__boxed_6537_: u8 = 0;
    let mut v_res_6538_: u8 = 0;
    let mut v_r_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9144__boxed_6536_ = (leanh::lean_unbox(v___x_6532_) as u8);
    v___y_9145__boxed_6537_ = (leanh::lean_unbox(v___y_6533_) as u8);
    v_res_6538_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_6530_, v___x_6531_, v___x_9144__boxed_6536_, v___y_9145__boxed_6537_, v___x_6534_, v_fvarId_6535_);
    leanh::lean_dec(v_fvarId_6535_);
    leanh::lean_dec_ref(v___x_6534_);
    leanh::lean_dec(v___x_6530_);
    v_r_6539_ = leanh::lean_box((v_res_6538_) as usize);
    return v_r_6539_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(
    mut v___x_6540_: *mut leanh::LeanObject,
    mut v_as_6541_: *mut leanh::LeanObject,
    mut v_i_6542_: usize,
    mut v_stop_6543_: usize,
) -> u8 {
    let mut v___x_6544_: u8 = 0;
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: u8 = 0;
    let mut v___x_6548_: usize = 0;
    let mut v___x_6549_: usize = 0;
    let mut v___x_6551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6544_ = lean_usize_dec_eq(v_i_6542_, v_stop_6543_);
                if v___x_6544_ == 0 {
                    v___x_6545_ = lean_array_uget_borrowed(v_as_6541_, v_i_6542_);
                    v___x_6546_ = l_Lean_Expr_fvarId_x21(v___x_6545_);
                    v___x_6547_ = l_Lean_instBEqFVarId_beq(v___x_6540_, v___x_6546_);
                    leanh::lean_dec(v___x_6546_);
                    if v___x_6547_ == 0 {
                        v___x_6548_ = 1usize;
                        v___x_6549_ = lean_usize_add(v_i_6542_, v___x_6548_);
                        v_i_6542_ = v___x_6549_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6547_;
                    }
                } else {
                    v___x_6551_ = 0;
                    return v___x_6551_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(
    mut v___x_6552_: *mut leanh::LeanObject,
    mut v_as_6553_: *mut leanh::LeanObject,
    mut v_i_6554_: *mut leanh::LeanObject,
    mut v_stop_6555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6556_: usize = 0;
    let mut v_stop_boxed_6557_: usize = 0;
    let mut v_res_6558_: u8 = 0;
    let mut v_r_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6556_ = leanh::lean_unbox_usize(v_i_6554_);
    leanh::lean_dec(v_i_6554_);
    v_stop_boxed_6557_ = leanh::lean_unbox_usize(v_stop_6555_);
    leanh::lean_dec(v_stop_6555_);
    v_res_6558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_6552_, v_as_6553_, v_i_boxed_6556_, v_stop_boxed_6557_);
    leanh::lean_dec_ref(v_as_6553_);
    leanh::lean_dec(v___x_6552_);
    v_r_6559_ = leanh::lean_box((v_res_6558_) as usize);
    return v_r_6559_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(
    mut v___y_6560_: u8,
    mut v_x_6561_: *mut leanh::LeanObject,
) -> u8 {
    return v___y_6560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(
    mut v___y_6562_: *mut leanh::LeanObject,
    mut v_x_6563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9194__boxed_6564_: u8 = 0;
    let mut v_res_6565_: u8 = 0;
    let mut v_r_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9194__boxed_6564_ = (leanh::lean_unbox(v___y_6562_) as u8);
    v_res_6565_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9194__boxed_6564_, v_x_6563_);
    leanh::lean_dec(v_x_6563_);
    v_r_6566_ = leanh::lean_box((v_res_6565_) as usize);
    return v_r_6566_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6567_ = leanh::lean_box(0);
    v___x_6568_ = leanh::lean_unsigned_to_nat(16);
    v___x_6569_ = lean_mk_array(v___x_6568_, v___x_6567_);
    return v___x_6569_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
    v___x_6571_ = leanh::lean_unsigned_to_nat(0);
    v___x_6572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6572_, 0, v___x_6571_);
    leanh::lean_ctor_set(v___x_6572_, 1, v___x_6570_);
    return v___x_6572_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(
    mut v___x_6573_: u8,
    mut v___x_6574_: *mut leanh::LeanObject,
    mut v___x_6575_: *mut leanh::LeanObject,
    mut v_ctx_6576_: *mut leanh::LeanObject,
    mut v_as_6577_: *mut leanh::LeanObject,
    mut v_i_6578_: usize,
    mut v_stop_6579_: usize,
    mut v___y_6580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6582_: u8 = 0;
    let mut v___x_6583_: u8 = 0;
    let mut v_a_6585_: u8 = 0;
    let mut v___x_6586_: usize = 0;
    let mut v___x_6587_: usize = 0;
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: u8 = 0;
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6596_: u8 = 0;
    let mut v_mctx_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6605_: u8 = 0;
    let mut v___x_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut v_unused_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: u8 = 0;
    let mut v_fst_6619_: u8 = 0;
    let mut v_snd_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v_unused_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: u8 = 0;
    let mut v___y_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6645_: u8 = 0;
    let mut v_snd_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: u8 = 0;
    let mut v___x_6648_: u8 = 0;
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: u8 = 0;
    let mut v_fst_6660_: u8 = 0;
    let mut v_mctx_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut v_unused_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u8 = 0;
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorDecl_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: u8 = 0;
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6690_: u8 = 0;
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: u8 = 0;
    let mut v___x_6702_: u8 = 0;
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6705_: u8 = 0;
    let mut v_type_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: u8 = 0;
    let mut v___x_6713_: u8 = 0;
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: u8 = 0;
    let mut v___x_6722_: u8 = 0;
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: u8 = 0;
    let mut v___x_6728_: usize = 0;
    let mut v___x_6729_: usize = 0;
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6731_: u8 = 0;
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: u8 = 0;
    let mut v___x_6734_: u8 = 0;
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6582_ = lean_usize_dec_eq(v_i_6578_, v_stop_6579_);
                if v___x_6582_ == 0 {
                    v___x_6583_ = 1;
                    v___x_6682_ = lean_array_uget_borrowed(v_as_6577_, v_i_6578_);
                    if leanh::lean_obj_tag(v___x_6682_) == 0 {
                        v_a_6585_ = v___x_6573_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6683_ = leanh::lean_ctor_get(v___x_6682_, 0);
                        v_majorDecl_6684_ = leanh::lean_ctor_get(v_ctx_6576_, 2);
                        v___x_6685_ = l_Lean_LocalDecl_fvarId(v_val_6683_);
                        v___x_6686_ = l_Lean_LocalDecl_fvarId(v_majorDecl_6684_);
                        v___x_6687_ = l_Lean_instBEqFVarId_beq(v___x_6685_, v___x_6686_);
                        leanh::lean_dec(v___x_6686_);
                        if v___x_6687_ == 0 {
                            v___x_6688_ = leanh::lean_unsigned_to_nat(0);
                            v___x_6731_ = lean_nat_dec_lt(v___x_6688_, v___x_6575_);
                            if v___x_6731_ == 0 {
                                leanh::lean_dec(v___x_6685_);
                                v___y_6690_ = v___x_6687_;
                                state = 17;
                                continue;
                            } else {
                                v___x_6732_ = lean_array_get_size(v___x_6574_);
                                v___x_6733_ = lean_nat_dec_le(v___x_6575_, v___x_6732_);
                                if v___x_6733_ == 0 {
                                    v___y_6726_ = v___x_6732_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v___x_6575_);
                                    v___y_6726_ = v___x_6575_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_6685_);
                            v_a_6592_ = v___x_6687_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_6575_);
                    leanh::lean_dec_ref(v___x_6574_);
                    v___x_6734_ = 0;
                    v___x_6735_ = leanh::lean_box((v___x_6734_) as usize);
                    v___x_6736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6736_, 0, v___x_6735_);
                    return v___x_6736_;
                }
            }
            1 => {
                if v_a_6585_ == 0 {
                    v___x_6586_ = 1usize;
                    v___x_6587_ = lean_usize_add(v_i_6578_, v___x_6586_);
                    v_i_6578_ = v___x_6587_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6575_);
                    leanh::lean_dec_ref(v___x_6574_);
                    v___x_6589_ = leanh::lean_box((v___x_6583_) as usize);
                    v___x_6590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6590_, 0, v___x_6589_);
                    return v___x_6590_;
                }
            }
            2 => {
                if v_a_6592_ == 0 {
                    leanh::lean_dec(v___x_6575_);
                    leanh::lean_dec_ref(v___x_6574_);
                    v___x_6593_ = leanh::lean_box((v___x_6583_) as usize);
                    v___x_6594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6594_, 0, v___x_6593_);
                    return v___x_6594_;
                } else {
                    v_a_6585_ = v___x_6573_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6598_ = lean_st_ref_take(v___y_6580_);
                v_cache_6599_ = leanh::lean_ctor_get(v___x_6598_, 1);
                v_zetaDeltaFVarIds_6600_ = leanh::lean_ctor_get(v___x_6598_, 2);
                v_postponed_6601_ = leanh::lean_ctor_get(v___x_6598_, 3);
                v_diag_6602_ = leanh::lean_ctor_get(v___x_6598_, 4);
                v_isSharedCheck_6610_ = (!leanh::lean_is_exclusive(v___x_6598_)) as u8;
                if v_isSharedCheck_6610_ == 0 {
                    v_unused_6611_ = leanh::lean_ctor_get(v___x_6598_, 0);
                    leanh::lean_dec(v_unused_6611_);
                    v___x_6604_ = v___x_6598_;
                    v_isShared_6605_ = v_isSharedCheck_6610_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6602_);
                    leanh::lean_inc(v_postponed_6601_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6600_);
                    leanh::lean_inc(v_cache_6599_);
                    leanh::lean_dec(v___x_6598_);
                    v___x_6604_ = leanh::lean_box(0);
                    v_isShared_6605_ = v_isSharedCheck_6610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6605_ == 0 {
                    leanh::lean_ctor_set(v___x_6604_, 0, v_mctx_6597_);
                    v___x_6607_ = v___x_6604_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6609_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 0, v_mctx_6597_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 1, v_cache_6599_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6609_,
                        2,
                        v_zetaDeltaFVarIds_6600_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 3, v_postponed_6601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 4, v_diag_6602_);
                    v___x_6607_ = v_reuseFailAlloc_6609_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6608_ = lean_st_ref_set(v___y_6580_, v___x_6607_);
                v_a_6592_ = v_fst_6596_;
                state = 2;
                continue;
            }
            6 => {
                v_snd_6614_ = leanh::lean_ctor_get(v___y_6613_, 1);
                leanh::lean_inc(v_snd_6614_);
                v_fst_6615_ = leanh::lean_ctor_get(v___y_6613_, 0);
                leanh::lean_inc(v_fst_6615_);
                leanh::lean_dec_ref(v___y_6613_);
                v_mctx_6616_ = leanh::lean_ctor_get(v_snd_6614_, 1);
                leanh::lean_inc_ref(v_mctx_6616_);
                leanh::lean_dec(v_snd_6614_);
                v___x_6617_ = (leanh::lean_unbox(v_fst_6615_) as u8);
                leanh::lean_dec(v_fst_6615_);
                v_fst_6596_ = v___x_6617_;
                v_mctx_6597_ = v_mctx_6616_;
                state = 3;
                continue;
            }
            7 => {
                v_mctx_6621_ = leanh::lean_ctor_get(v_snd_6620_, 1);
                leanh::lean_inc_ref(v_mctx_6621_);
                leanh::lean_dec_ref(v_snd_6620_);
                v___x_6622_ = lean_st_ref_take(v___y_6580_);
                v_cache_6623_ = leanh::lean_ctor_get(v___x_6622_, 1);
                v_zetaDeltaFVarIds_6624_ = leanh::lean_ctor_get(v___x_6622_, 2);
                v_postponed_6625_ = leanh::lean_ctor_get(v___x_6622_, 3);
                v_diag_6626_ = leanh::lean_ctor_get(v___x_6622_, 4);
                v_isSharedCheck_6634_ = (!leanh::lean_is_exclusive(v___x_6622_)) as u8;
                if v_isSharedCheck_6634_ == 0 {
                    v_unused_6635_ = leanh::lean_ctor_get(v___x_6622_, 0);
                    leanh::lean_dec(v_unused_6635_);
                    v___x_6628_ = v___x_6622_;
                    v_isShared_6629_ = v_isSharedCheck_6634_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6626_);
                    leanh::lean_inc(v_postponed_6625_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6624_);
                    leanh::lean_inc(v_cache_6623_);
                    leanh::lean_dec(v___x_6622_);
                    v___x_6628_ = leanh::lean_box(0);
                    v_isShared_6629_ = v_isSharedCheck_6634_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6629_ == 0 {
                    leanh::lean_ctor_set(v___x_6628_, 0, v_mctx_6621_);
                    v___x_6631_ = v___x_6628_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6633_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_mctx_6621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 1, v_cache_6623_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6633_,
                        2,
                        v_zetaDeltaFVarIds_6624_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 3, v_postponed_6625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 4, v_diag_6626_);
                    v___x_6631_ = v_reuseFailAlloc_6633_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6632_ = lean_st_ref_set(v___y_6580_, v___x_6631_);
                v_a_6592_ = v_fst_6619_;
                state = 2;
                continue;
            }
            10 => {
                v_fst_6638_ = leanh::lean_ctor_get(v___y_6637_, 0);
                leanh::lean_inc(v_fst_6638_);
                v_snd_6639_ = leanh::lean_ctor_get(v___y_6637_, 1);
                leanh::lean_inc(v_snd_6639_);
                leanh::lean_dec_ref(v___y_6637_);
                v___x_6640_ = (leanh::lean_unbox(v_fst_6638_) as u8);
                leanh::lean_dec(v_fst_6638_);
                v_fst_6619_ = v___x_6640_;
                v_snd_6620_ = v_snd_6639_;
                state = 7;
                continue;
            }
            11 => {
                if v_fst_6645_ == 0 {
                    v___x_6647_ = l_Lean_Expr_hasFVar(v___y_6643_);
                    if v___x_6647_ == 0 {
                        v___x_6648_ = l_Lean_Expr_hasMVar(v___y_6643_);
                        if v___x_6648_ == 0 {
                            leanh::lean_dec_ref(v___y_6644_);
                            leanh::lean_dec_ref(v___y_6643_);
                            leanh::lean_dec_ref(v___y_6642_);
                            v_fst_6619_ = v___x_6648_;
                            v_snd_6620_ = v_snd_6646_;
                            state = 7;
                            continue;
                        } else {
                            v___x_6649_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___y_6642_,
                                    v___y_6644_,
                                    v___y_6643_,
                                    v_snd_6646_,
                                );
                            v___y_6637_ = v___x_6649_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_6650_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___y_6642_,
                            v___y_6644_,
                            v___y_6643_,
                            v_snd_6646_,
                        );
                        v___y_6637_ = v___x_6650_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6644_);
                    leanh::lean_dec_ref(v___y_6643_);
                    leanh::lean_dec_ref(v___y_6642_);
                    v_fst_6619_ = v_fst_6645_;
                    v_snd_6620_ = v_snd_6646_;
                    state = 7;
                    continue;
                }
            }
            12 => {
                v_fst_6656_ = leanh::lean_ctor_get(v___y_6655_, 0);
                leanh::lean_inc(v_fst_6656_);
                v_snd_6657_ = leanh::lean_ctor_get(v___y_6655_, 1);
                leanh::lean_inc(v_snd_6657_);
                leanh::lean_dec_ref(v___y_6655_);
                v___x_6658_ = (leanh::lean_unbox(v_fst_6656_) as u8);
                leanh::lean_dec(v_fst_6656_);
                v___y_6642_ = v___y_6652_;
                v___y_6643_ = v___y_6653_;
                v___y_6644_ = v___y_6654_;
                v_fst_6645_ = v___x_6658_;
                v_snd_6646_ = v_snd_6657_;
                state = 11;
                continue;
            }
            13 => {
                v___x_6662_ = lean_st_ref_take(v___y_6580_);
                v_cache_6663_ = leanh::lean_ctor_get(v___x_6662_, 1);
                v_zetaDeltaFVarIds_6664_ = leanh::lean_ctor_get(v___x_6662_, 2);
                v_postponed_6665_ = leanh::lean_ctor_get(v___x_6662_, 3);
                v_diag_6666_ = leanh::lean_ctor_get(v___x_6662_, 4);
                v_isSharedCheck_6674_ = (!leanh::lean_is_exclusive(v___x_6662_)) as u8;
                if v_isSharedCheck_6674_ == 0 {
                    v_unused_6675_ = leanh::lean_ctor_get(v___x_6662_, 0);
                    leanh::lean_dec(v_unused_6675_);
                    v___x_6668_ = v___x_6662_;
                    v_isShared_6669_ = v_isSharedCheck_6674_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6666_);
                    leanh::lean_inc(v_postponed_6665_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6664_);
                    leanh::lean_inc(v_cache_6663_);
                    leanh::lean_dec(v___x_6662_);
                    v___x_6668_ = leanh::lean_box(0);
                    v_isShared_6669_ = v_isSharedCheck_6674_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_6669_ == 0 {
                    leanh::lean_ctor_set(v___x_6668_, 0, v_mctx_6661_);
                    v___x_6671_ = v___x_6668_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6673_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6673_, 0, v_mctx_6661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6673_, 1, v_cache_6663_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6673_,
                        2,
                        v_zetaDeltaFVarIds_6664_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6673_, 3, v_postponed_6665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6673_, 4, v_diag_6666_);
                    v___x_6671_ = v_reuseFailAlloc_6673_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_6672_ = lean_st_ref_set(v___y_6580_, v___x_6671_);
                v_a_6592_ = v_fst_6660_;
                state = 2;
                continue;
            }
            16 => {
                v_snd_6678_ = leanh::lean_ctor_get(v___y_6677_, 1);
                leanh::lean_inc(v_snd_6678_);
                v_fst_6679_ = leanh::lean_ctor_get(v___y_6677_, 0);
                leanh::lean_inc(v_fst_6679_);
                leanh::lean_dec_ref(v___y_6677_);
                v_mctx_6680_ = leanh::lean_ctor_get(v_snd_6678_, 1);
                leanh::lean_inc_ref(v_mctx_6680_);
                leanh::lean_dec(v_snd_6678_);
                v___x_6681_ = (leanh::lean_unbox(v_fst_6679_) as u8);
                leanh::lean_dec(v_fst_6679_);
                v_fst_6660_ = v___x_6681_;
                v_mctx_6661_ = v_mctx_6680_;
                state = 13;
                continue;
            }
            17 => {
                if v___y_6690_ == 0 {
                    v___x_6691_ = leanh::lean_box((v___y_6690_) as usize);
                    v___f_6692_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_6692_, 0, v___x_6691_);
                    v___x_6693_ = leanh::lean_box((v___x_6583_) as usize);
                    v___x_6694_ = leanh::lean_box((v___y_6690_) as usize);
                    leanh::lean_inc_ref(v___x_6574_);
                    leanh::lean_inc(v___x_6575_);
                    v___f_6695_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
                    leanh::lean_closure_set(v___f_6695_, 0, v___x_6688_);
                    leanh::lean_closure_set(v___f_6695_, 1, v___x_6575_);
                    leanh::lean_closure_set(v___f_6695_, 2, v___x_6693_);
                    leanh::lean_closure_set(v___f_6695_, 3, v___x_6694_);
                    leanh::lean_closure_set(v___f_6695_, 4, v___x_6574_);
                    if leanh::lean_obj_tag(v_val_6683_) == 0 {
                        v_type_6696_ = leanh::lean_ctor_get(v_val_6683_, 3);
                        v___x_6697_ = lean_st_ref_get(v___y_6580_);
                        v_mctx_6698_ = leanh::lean_ctor_get(v___x_6697_, 0);
                        leanh::lean_inc_ref_n(v_mctx_6698_, 2);
                        leanh::lean_dec(v___x_6697_);
                        v___x_6699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
                        v___x_6700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6700_, 0, v___x_6699_);
                        leanh::lean_ctor_set(v___x_6700_, 1, v_mctx_6698_);
                        v___x_6701_ = l_Lean_Expr_hasFVar(v_type_6696_);
                        if v___x_6701_ == 0 {
                            v___x_6702_ = l_Lean_Expr_hasMVar(v_type_6696_);
                            if v___x_6702_ == 0 {
                                leanh::lean_dec_ref_known(v___x_6700_, 2);
                                leanh::lean_dec_ref(v___f_6695_);
                                leanh::lean_dec_ref(v___f_6692_);
                                v_fst_6596_ = v___x_6702_;
                                v_mctx_6597_ = v_mctx_6698_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_mctx_6698_);
                                leanh::lean_inc_ref(v_type_6696_);
                                v___x_6703_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_6695_,
                                        v___f_6692_,
                                        v_type_6696_,
                                        v___x_6700_,
                                    );
                                v___y_6613_ = v___x_6703_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_mctx_6698_);
                            leanh::lean_inc_ref(v_type_6696_);
                            v___x_6704_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_6695_,
                                    v___f_6692_,
                                    v_type_6696_,
                                    v___x_6700_,
                                );
                            v___y_6613_ = v___x_6704_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_nondep_6705_ = leanh::lean_ctor_get_uint8(
                            v_val_6683_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        if v_nondep_6705_ == 0 {
                            v_type_6706_ = leanh::lean_ctor_get(v_val_6683_, 3);
                            v_value_6707_ = leanh::lean_ctor_get(v_val_6683_, 4);
                            v___x_6708_ = lean_st_ref_get(v___y_6580_);
                            v_mctx_6709_ = leanh::lean_ctor_get(v___x_6708_, 0);
                            leanh::lean_inc_ref(v_mctx_6709_);
                            leanh::lean_dec(v___x_6708_);
                            v___x_6710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
                            v___x_6711_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6711_, 0, v___x_6710_);
                            leanh::lean_ctor_set(v___x_6711_, 1, v_mctx_6709_);
                            v___x_6712_ = l_Lean_Expr_hasFVar(v_type_6706_);
                            if v___x_6712_ == 0 {
                                v___x_6713_ = l_Lean_Expr_hasMVar(v_type_6706_);
                                if v___x_6713_ == 0 {
                                    leanh::lean_inc_ref(v_value_6707_);
                                    v___y_6642_ = v___f_6695_;
                                    v___y_6643_ = v_value_6707_;
                                    v___y_6644_ = v___f_6692_;
                                    v_fst_6645_ = v___x_6713_;
                                    v_snd_6646_ = v___x_6711_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc_ref(v_type_6706_);
                                    leanh::lean_inc_ref(v___f_6692_);
                                    leanh::lean_inc_ref(v___f_6695_);
                                    v___x_6714_ =
                                        l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                            v___f_6695_,
                                            v___f_6692_,
                                            v_type_6706_,
                                            v___x_6711_,
                                        );
                                    leanh::lean_inc_ref(v_value_6707_);
                                    v___y_6652_ = v___f_6695_;
                                    v___y_6653_ = v_value_6707_;
                                    v___y_6654_ = v___f_6692_;
                                    v___y_6655_ = v___x_6714_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc_ref(v_type_6706_);
                                leanh::lean_inc_ref(v___f_6692_);
                                leanh::lean_inc_ref(v___f_6695_);
                                v___x_6715_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_6695_,
                                        v___f_6692_,
                                        v_type_6706_,
                                        v___x_6711_,
                                    );
                                leanh::lean_inc_ref(v_value_6707_);
                                v___y_6652_ = v___f_6695_;
                                v___y_6653_ = v_value_6707_;
                                v___y_6654_ = v___f_6692_;
                                v___y_6655_ = v___x_6715_;
                                state = 12;
                                continue;
                            }
                        } else {
                            v_type_6716_ = leanh::lean_ctor_get(v_val_6683_, 3);
                            v___x_6717_ = lean_st_ref_get(v___y_6580_);
                            v_mctx_6718_ = leanh::lean_ctor_get(v___x_6717_, 0);
                            leanh::lean_inc_ref_n(v_mctx_6718_, 2);
                            leanh::lean_dec(v___x_6717_);
                            v___x_6719_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
                            v___x_6720_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6720_, 0, v___x_6719_);
                            leanh::lean_ctor_set(v___x_6720_, 1, v_mctx_6718_);
                            v___x_6721_ = l_Lean_Expr_hasFVar(v_type_6716_);
                            if v___x_6721_ == 0 {
                                v___x_6722_ = l_Lean_Expr_hasMVar(v_type_6716_);
                                if v___x_6722_ == 0 {
                                    leanh::lean_dec_ref_known(v___x_6720_, 2);
                                    leanh::lean_dec_ref(v___f_6695_);
                                    leanh::lean_dec_ref(v___f_6692_);
                                    v_fst_6660_ = v___x_6722_;
                                    v_mctx_6661_ = v_mctx_6718_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_mctx_6718_);
                                    leanh::lean_inc_ref(v_type_6716_);
                                    v___x_6723_ =
                                        l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                            v___f_6695_,
                                            v___f_6692_,
                                            v_type_6716_,
                                            v___x_6720_,
                                        );
                                    v___y_6677_ = v___x_6723_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_mctx_6718_);
                                leanh::lean_inc_ref(v_type_6716_);
                                v___x_6724_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_6695_,
                                        v___f_6692_,
                                        v_type_6716_,
                                        v___x_6720_,
                                    );
                                v___y_6677_ = v___x_6724_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_6585_ = v___x_6573_;
                    state = 1;
                    continue;
                }
            }
            18 => {
                v___x_6727_ = lean_nat_dec_lt(v___x_6688_, v___y_6726_);
                if v___x_6727_ == 0 {
                    leanh::lean_dec(v___y_6726_);
                    leanh::lean_dec(v___x_6685_);
                    v___y_6690_ = v___x_6687_;
                    state = 17;
                    continue;
                } else {
                    v___x_6728_ = 0usize;
                    v___x_6729_ = lean_usize_of_nat(v___y_6726_);
                    leanh::lean_dec(v___y_6726_);
                    v___x_6730_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_6685_, v___x_6574_, v___x_6728_, v___x_6729_);
                    leanh::lean_dec(v___x_6685_);
                    v___y_6690_ = v___x_6730_;
                    state = 17;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(
    mut v___x_6737_: *mut leanh::LeanObject,
    mut v___x_6738_: *mut leanh::LeanObject,
    mut v___x_6739_: *mut leanh::LeanObject,
    mut v_ctx_6740_: *mut leanh::LeanObject,
    mut v_as_6741_: *mut leanh::LeanObject,
    mut v_i_6742_: *mut leanh::LeanObject,
    mut v_stop_6743_: *mut leanh::LeanObject,
    mut v___y_6744_: *mut leanh::LeanObject,
    mut v___y_6745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9224__boxed_6746_: u8 = 0;
    let mut v_i_boxed_6747_: usize = 0;
    let mut v_stop_boxed_6748_: usize = 0;
    let mut v_res_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9224__boxed_6746_ = (leanh::lean_unbox(v___x_6737_) as u8);
    v_i_boxed_6747_ = leanh::lean_unbox_usize(v_i_6742_);
    leanh::lean_dec(v_i_6742_);
    v_stop_boxed_6748_ = leanh::lean_unbox_usize(v_stop_6743_);
    leanh::lean_dec(v_stop_6743_);
    v_res_6749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_9224__boxed_6746_, v___x_6738_, v___x_6739_, v_ctx_6740_, v_as_6741_, v_i_boxed_6747_, v_stop_boxed_6748_, v___y_6744_);
    leanh::lean_dec(v___y_6744_);
    leanh::lean_dec_ref(v_as_6741_);
    leanh::lean_dec_ref(v_ctx_6740_);
    return v_res_6749_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(
    mut v___x_6750_: u8,
    mut v___x_6751_: *mut leanh::LeanObject,
    mut v___x_6752_: *mut leanh::LeanObject,
    mut v_ctx_6753_: *mut leanh::LeanObject,
    mut v_x_6754_: *mut leanh::LeanObject,
    mut v___y_6755_: *mut leanh::LeanObject,
    mut v___y_6756_: *mut leanh::LeanObject,
    mut v___y_6757_: *mut leanh::LeanObject,
    mut v___y_6758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6763_: u8 = 0;
    let mut v___x_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: u8 = 0;
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: usize = 0;
    let mut v___x_6776_: usize = 0;
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6778_: u8 = 0;
    let mut v_vs_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: u8 = 0;
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: usize = 0;
    let mut v___x_6795_: usize = 0;
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6754_) == 0 {
                    v_cs_6760_ = leanh::lean_ctor_get(v_x_6754_, 0);
                    v_isSharedCheck_6778_ = (!leanh::lean_is_exclusive(v_x_6754_)) as u8;
                    if v_isSharedCheck_6778_ == 0 {
                        v___x_6762_ = v_x_6754_;
                        v_isShared_6763_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_6760_);
                        leanh::lean_dec(v_x_6754_);
                        v___x_6762_ = leanh::lean_box(0);
                        v_isShared_6763_ = v_isSharedCheck_6778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_6779_ = leanh::lean_ctor_get(v_x_6754_, 0);
                    v_isSharedCheck_6797_ = (!leanh::lean_is_exclusive(v_x_6754_)) as u8;
                    if v_isSharedCheck_6797_ == 0 {
                        v___x_6781_ = v_x_6754_;
                        v_isShared_6782_ = v_isSharedCheck_6797_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_6779_);
                        leanh::lean_dec(v_x_6754_);
                        v___x_6781_ = leanh::lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6797_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6764_ = leanh::lean_unsigned_to_nat(0);
                v___x_6765_ = lean_array_get_size(v_cs_6760_);
                v___x_6766_ = lean_nat_dec_lt(v___x_6764_, v___x_6765_);
                if v___x_6766_ == 0 {
                    leanh::lean_dec_ref(v_cs_6760_);
                    leanh::lean_dec(v___x_6752_);
                    leanh::lean_dec_ref(v___x_6751_);
                    v___x_6767_ = leanh::lean_box((v___x_6766_) as usize);
                    if v_isShared_6763_ == 0 {
                        leanh::lean_ctor_set(v___x_6762_, 0, v___x_6767_);
                        v___x_6769_ = v___x_6762_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6770_, 0, v___x_6767_);
                        v___x_6769_ = v_reuseFailAlloc_6770_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_6766_ == 0 {
                        leanh::lean_dec_ref(v_cs_6760_);
                        leanh::lean_dec(v___x_6752_);
                        leanh::lean_dec_ref(v___x_6751_);
                        v___x_6771_ = leanh::lean_box((v___x_6766_) as usize);
                        if v_isShared_6763_ == 0 {
                            leanh::lean_ctor_set(v___x_6762_, 0, v___x_6771_);
                            v___x_6773_ = v___x_6762_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6774_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6774_, 0, v___x_6771_);
                            v___x_6773_ = v_reuseFailAlloc_6774_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6762_);
                        v___x_6775_ = 0usize;
                        v___x_6776_ = lean_usize_of_nat(v___x_6765_);
                        v___x_6777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_6750_, v___x_6751_, v___x_6752_, v_ctx_6753_, v_cs_6760_, v___x_6775_, v___x_6776_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_);
                        leanh::lean_dec_ref(v_cs_6760_);
                        return v___x_6777_;
                    }
                }
            }
            2 => {
                return v___x_6769_;
            }
            3 => {
                return v___x_6773_;
            }
            4 => {
                v___x_6783_ = leanh::lean_unsigned_to_nat(0);
                v___x_6784_ = lean_array_get_size(v_vs_6779_);
                v___x_6785_ = lean_nat_dec_lt(v___x_6783_, v___x_6784_);
                if v___x_6785_ == 0 {
                    leanh::lean_dec_ref(v_vs_6779_);
                    leanh::lean_dec(v___x_6752_);
                    leanh::lean_dec_ref(v___x_6751_);
                    v___x_6786_ = leanh::lean_box((v___x_6785_) as usize);
                    if v_isShared_6782_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6781_, 0);
                        leanh::lean_ctor_set(v___x_6781_, 0, v___x_6786_);
                        v___x_6788_ = v___x_6781_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6789_, 0, v___x_6786_);
                        v___x_6788_ = v_reuseFailAlloc_6789_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v___x_6785_ == 0 {
                        leanh::lean_dec_ref(v_vs_6779_);
                        leanh::lean_dec(v___x_6752_);
                        leanh::lean_dec_ref(v___x_6751_);
                        v___x_6790_ = leanh::lean_box((v___x_6785_) as usize);
                        if v_isShared_6782_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_6781_, 0);
                            leanh::lean_ctor_set(v___x_6781_, 0, v___x_6790_);
                            v___x_6792_ = v___x_6781_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6793_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 0, v___x_6790_);
                            v___x_6792_ = v_reuseFailAlloc_6793_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6781_);
                        v___x_6794_ = 0usize;
                        v___x_6795_ = lean_usize_of_nat(v___x_6784_);
                        v___x_6796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_6750_, v___x_6751_, v___x_6752_, v_ctx_6753_, v_vs_6779_, v___x_6794_, v___x_6795_, v___y_6756_);
                        leanh::lean_dec_ref(v_vs_6779_);
                        return v___x_6796_;
                    }
                }
            }
            5 => {
                return v___x_6788_;
            }
            6 => {
                return v___x_6792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(
    mut v___x_6798_: u8,
    mut v___x_6799_: *mut leanh::LeanObject,
    mut v___x_6800_: *mut leanh::LeanObject,
    mut v_ctx_6801_: *mut leanh::LeanObject,
    mut v_as_6802_: *mut leanh::LeanObject,
    mut v_i_6803_: usize,
    mut v_stop_6804_: usize,
    mut v___y_6805_: *mut leanh::LeanObject,
    mut v___y_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6810_: u8 = 0;
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6816_: u8 = 0;
    let mut v___x_6817_: u8 = 0;
    let mut v___x_6818_: usize = 0;
    let mut v___x_6819_: usize = 0;
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6824_: u8 = 0;
    let mut v___x_6825_: u8 = 0;
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6810_ = lean_usize_dec_eq(v_i_6803_, v_stop_6804_);
                if v___x_6810_ == 0 {
                    v___x_6811_ = lean_array_uget_borrowed(v_as_6802_, v_i_6803_);
                    leanh::lean_inc(v___x_6811_);
                    leanh::lean_inc(v___x_6800_);
                    leanh::lean_inc_ref(v___x_6799_);
                    v___x_6812_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_6798_, v___x_6799_, v___x_6800_, v_ctx_6801_, v___x_6811_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_);
                    if leanh::lean_obj_tag(v___x_6812_) == 0 {
                        v_a_6813_ = leanh::lean_ctor_get(v___x_6812_, 0);
                        v_isSharedCheck_6824_ =
                            (!leanh::lean_is_exclusive(v___x_6812_)) as u8;
                        if v_isSharedCheck_6824_ == 0 {
                            v___x_6815_ = v___x_6812_;
                            v_isShared_6816_ = v_isSharedCheck_6824_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6813_);
                            leanh::lean_dec(v___x_6812_);
                            v___x_6815_ = leanh::lean_box(0);
                            v_isShared_6816_ = v_isSharedCheck_6824_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6800_);
                        leanh::lean_dec_ref(v___x_6799_);
                        return v___x_6812_;
                    }
                } else {
                    leanh::lean_dec(v___x_6800_);
                    leanh::lean_dec_ref(v___x_6799_);
                    v___x_6825_ = 0;
                    v___x_6826_ = leanh::lean_box((v___x_6825_) as usize);
                    v___x_6827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6827_, 0, v___x_6826_);
                    return v___x_6827_;
                }
            }
            1 => {
                v___x_6817_ = (leanh::lean_unbox(v_a_6813_) as u8);
                if v___x_6817_ == 0 {
                    leanh::lean_del_object(v___x_6815_);
                    leanh::lean_dec(v_a_6813_);
                    v___x_6818_ = 1usize;
                    v___x_6819_ = lean_usize_add(v_i_6803_, v___x_6818_);
                    v_i_6803_ = v___x_6819_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6800_);
                    leanh::lean_dec_ref(v___x_6799_);
                    if v_isShared_6816_ == 0 {
                        v___x_6822_ = v___x_6815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6823_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_a_6813_);
                        v___x_6822_ = v_reuseFailAlloc_6823_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(
    mut v___x_6828_: *mut leanh::LeanObject,
    mut v___x_6829_: *mut leanh::LeanObject,
    mut v___x_6830_: *mut leanh::LeanObject,
    mut v_ctx_6831_: *mut leanh::LeanObject,
    mut v_as_6832_: *mut leanh::LeanObject,
    mut v_i_6833_: *mut leanh::LeanObject,
    mut v_stop_6834_: *mut leanh::LeanObject,
    mut v___y_6835_: *mut leanh::LeanObject,
    mut v___y_6836_: *mut leanh::LeanObject,
    mut v___y_6837_: *mut leanh::LeanObject,
    mut v___y_6838_: *mut leanh::LeanObject,
    mut v___y_6839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9531__boxed_6840_: u8 = 0;
    let mut v_i_boxed_6841_: usize = 0;
    let mut v_stop_boxed_6842_: usize = 0;
    let mut v_res_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9531__boxed_6840_ = (leanh::lean_unbox(v___x_6828_) as u8);
    v_i_boxed_6841_ = leanh::lean_unbox_usize(v_i_6833_);
    leanh::lean_dec(v_i_6833_);
    v_stop_boxed_6842_ = leanh::lean_unbox_usize(v_stop_6834_);
    leanh::lean_dec(v_stop_6834_);
    v_res_6843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_9531__boxed_6840_, v___x_6829_, v___x_6830_, v_ctx_6831_, v_as_6832_, v_i_boxed_6841_, v_stop_boxed_6842_, v___y_6835_, v___y_6836_, v___y_6837_, v___y_6838_);
    leanh::lean_dec(v___y_6838_);
    leanh::lean_dec_ref(v___y_6837_);
    leanh::lean_dec(v___y_6836_);
    leanh::lean_dec_ref(v___y_6835_);
    leanh::lean_dec_ref(v_as_6832_);
    leanh::lean_dec_ref(v_ctx_6831_);
    return v_res_6843_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(
    mut v___x_6844_: *mut leanh::LeanObject,
    mut v___x_6845_: *mut leanh::LeanObject,
    mut v___x_6846_: *mut leanh::LeanObject,
    mut v_ctx_6847_: *mut leanh::LeanObject,
    mut v_x_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
    mut v___y_6853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9550__boxed_6854_: u8 = 0;
    let mut v_res_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9550__boxed_6854_ = (leanh::lean_unbox(v___x_6844_) as u8);
    v_res_6855_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_9550__boxed_6854_, v___x_6845_, v___x_6846_, v_ctx_6847_, v_x_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
    leanh::lean_dec(v___y_6852_);
    leanh::lean_dec_ref(v___y_6851_);
    leanh::lean_dec(v___y_6850_);
    leanh::lean_dec_ref(v___y_6849_);
    leanh::lean_dec_ref(v_ctx_6847_);
    return v_res_6855_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(
    mut v___x_6856_: u8,
    mut v___x_6857_: *mut leanh::LeanObject,
    mut v___x_6858_: *mut leanh::LeanObject,
    mut v_ctx_6859_: *mut leanh::LeanObject,
    mut v_t_6860_: *mut leanh::LeanObject,
    mut v___y_6861_: *mut leanh::LeanObject,
    mut v___y_6862_: *mut leanh::LeanObject,
    mut v___y_6863_: *mut leanh::LeanObject,
    mut v___y_6864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_6866_ = leanh::lean_ctor_get(v_t_6860_, 0);
    leanh::lean_inc_ref(v_root_6866_);
    v_tail_6867_ = leanh::lean_ctor_get(v_t_6860_, 1);
    leanh::lean_inc_ref(v_tail_6867_);
    leanh::lean_dec_ref(v_t_6860_);
    leanh::lean_inc(v___x_6858_);
    leanh::lean_inc_ref(v___x_6857_);
    v___x_6868_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_6856_, v___x_6857_, v___x_6858_, v_ctx_6859_, v_root_6866_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_);
    if leanh::lean_obj_tag(v___x_6868_) == 0 {
        let mut v_a_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6870_: u8 = 0;
        v_a_6869_ = leanh::lean_ctor_get(v___x_6868_, 0);
        leanh::lean_inc(v_a_6869_);
        v___x_6870_ = (leanh::lean_unbox(v_a_6869_) as u8);
        leanh::lean_dec(v_a_6869_);
        if v___x_6870_ == 0 {
            let mut v___x_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6873_: u8 = 0;
            v___x_6871_ = leanh::lean_unsigned_to_nat(0);
            v___x_6872_ = lean_array_get_size(v_tail_6867_);
            v___x_6873_ = lean_nat_dec_lt(v___x_6871_, v___x_6872_);
            if v___x_6873_ == 0 {
                leanh::lean_dec_ref(v_tail_6867_);
                leanh::lean_dec(v___x_6858_);
                leanh::lean_dec_ref(v___x_6857_);
                return v___x_6868_;
            } else {
                if v___x_6873_ == 0 {
                    leanh::lean_dec_ref(v_tail_6867_);
                    leanh::lean_dec(v___x_6858_);
                    leanh::lean_dec_ref(v___x_6857_);
                    return v___x_6868_;
                } else {
                    let mut v___x_6874_: usize = 0;
                    let mut v___x_6875_: usize = 0;
                    let mut v___x_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref_known(v___x_6868_, 1);
                    v___x_6874_ = 0usize;
                    v___x_6875_ = lean_usize_of_nat(v___x_6872_);
                    v___x_6876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_6856_, v___x_6857_, v___x_6858_, v_ctx_6859_, v_tail_6867_, v___x_6874_, v___x_6875_, v___y_6862_);
                    leanh::lean_dec_ref(v_tail_6867_);
                    return v___x_6876_;
                }
            }
        } else {
            leanh::lean_dec_ref(v_tail_6867_);
            leanh::lean_dec(v___x_6858_);
            leanh::lean_dec_ref(v___x_6857_);
            return v___x_6868_;
        }
    } else {
        leanh::lean_dec_ref(v_tail_6867_);
        leanh::lean_dec(v___x_6858_);
        leanh::lean_dec_ref(v___x_6857_);
        return v___x_6868_;
    }
}
pub unsafe fn l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(
    mut v___x_6877_: *mut leanh::LeanObject,
    mut v___x_6878_: *mut leanh::LeanObject,
    mut v___x_6879_: *mut leanh::LeanObject,
    mut v_ctx_6880_: *mut leanh::LeanObject,
    mut v_t_6881_: *mut leanh::LeanObject,
    mut v___y_6882_: *mut leanh::LeanObject,
    mut v___y_6883_: *mut leanh::LeanObject,
    mut v___y_6884_: *mut leanh::LeanObject,
    mut v___y_6885_: *mut leanh::LeanObject,
    mut v___y_6886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9695__boxed_6887_: u8 = 0;
    let mut v_res_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9695__boxed_6887_ = (leanh::lean_unbox(v___x_6877_) as u8);
    v_res_6888_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_9695__boxed_6887_, v___x_6878_, v___x_6879_, v_ctx_6880_, v_t_6881_, v___y_6882_, v___y_6883_, v___y_6884_, v___y_6885_);
    leanh::lean_dec(v___y_6885_);
    leanh::lean_dec_ref(v___y_6884_);
    leanh::lean_dec(v___y_6883_);
    leanh::lean_dec_ref(v___y_6882_);
    leanh::lean_dec_ref(v_ctx_6880_);
    return v_res_6888_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(
    mut v_ctx_6889_: *mut leanh::LeanObject,
    mut v_a_6890_: *mut leanh::LeanObject,
    mut v_a_6891_: *mut leanh::LeanObject,
    mut v_a_6892_: *mut leanh::LeanObject,
    mut v_a_6893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_majorTypeIndices_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: u8 = 0;
    let mut v___y_6900_: u8 = 0;
    let mut v___x_6901_: u8 = 0;
    let mut v_lctx_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6908_: u8 = 0;
    let mut v___x_6909_: u8 = 0;
    let mut v___x_6910_: u8 = 0;
    let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6919_: u8 = 0;
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: u8 = 0;
    let mut v___x_6925_: usize = 0;
    let mut v___x_6926_: usize = 0;
    let mut v___x_6927_: u8 = 0;
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_majorTypeIndices_6895_ = leanh::lean_ctor_get(v_ctx_6889_, 5);
                leanh::lean_inc_ref(v_majorTypeIndices_6895_);
                v___x_6896_ = lean_array_get_size(v_majorTypeIndices_6895_);
                v___x_6897_ = leanh::lean_unsigned_to_nat(0);
                v___x_6898_ = lean_nat_dec_eq(v___x_6896_, v___x_6897_);
                if v___x_6898_ == 0 {
                    v___x_6924_ = lean_nat_dec_lt(v___x_6897_, v___x_6896_);
                    if v___x_6924_ == 0 {
                        v___y_6900_ = v___x_6898_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_6924_ == 0 {
                            v___y_6900_ = v___x_6898_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6925_ = 0usize;
                            v___x_6926_ = lean_usize_of_nat(v___x_6896_);
                            v___x_6927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_6896_, v_majorTypeIndices_6895_, v___x_6925_, v___x_6926_);
                            v___y_6900_ = v___x_6927_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_majorTypeIndices_6895_);
                    leanh::lean_dec_ref(v_ctx_6889_);
                    v___x_6928_ = leanh::lean_box((v___x_6898_) as usize);
                    v___x_6929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6929_, 0, v___x_6928_);
                    return v___x_6929_;
                }
            }
            1 => {
                if v___y_6900_ == 0 {
                    v___x_6901_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_6895_, v___x_6896_, v___x_6896_);
                    if v___x_6901_ == 0 {
                        v_lctx_6902_ = leanh::lean_ctor_get(v_a_6890_, 2);
                        v_decls_6903_ = leanh::lean_ctor_get(v_lctx_6902_, 1);
                        leanh::lean_inc_ref(v_decls_6903_);
                        v___x_6904_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_6901_, v_majorTypeIndices_6895_, v___x_6896_, v_ctx_6889_, v_decls_6903_, v_a_6890_, v_a_6891_, v_a_6892_, v_a_6893_);
                        leanh::lean_dec_ref(v_ctx_6889_);
                        if leanh::lean_obj_tag(v___x_6904_) == 0 {
                            v_a_6905_ = leanh::lean_ctor_get(v___x_6904_, 0);
                            v_isSharedCheck_6919_ =
                                (!leanh::lean_is_exclusive(v___x_6904_)) as u8;
                            if v_isSharedCheck_6919_ == 0 {
                                v___x_6907_ = v___x_6904_;
                                v_isShared_6908_ = v_isSharedCheck_6919_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6905_);
                                leanh::lean_dec(v___x_6904_);
                                v___x_6907_ = leanh::lean_box(0);
                                v_isShared_6908_ = v_isSharedCheck_6919_;
                                state = 2;
                                continue;
                            }
                        } else {
                            return v___x_6904_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_majorTypeIndices_6895_);
                        leanh::lean_dec_ref(v_ctx_6889_);
                        v___x_6920_ = leanh::lean_box((v___y_6900_) as usize);
                        v___x_6921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6921_, 0, v___x_6920_);
                        return v___x_6921_;
                    }
                } else {
                    leanh::lean_dec_ref(v_majorTypeIndices_6895_);
                    leanh::lean_dec_ref(v_ctx_6889_);
                    v___x_6922_ = leanh::lean_box((v___x_6898_) as usize);
                    v___x_6923_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6923_, 0, v___x_6922_);
                    return v___x_6923_;
                }
            }
            2 => {
                v___x_6909_ = (leanh::lean_unbox(v_a_6905_) as u8);
                leanh::lean_dec(v_a_6905_);
                if v___x_6909_ == 0 {
                    v___x_6910_ = 1;
                    v___x_6911_ = leanh::lean_box((v___x_6910_) as usize);
                    if v_isShared_6908_ == 0 {
                        leanh::lean_ctor_set(v___x_6907_, 0, v___x_6911_);
                        v___x_6913_ = v___x_6907_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6914_, 0, v___x_6911_);
                        v___x_6913_ = v_reuseFailAlloc_6914_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6915_ = leanh::lean_box((v___x_6901_) as usize);
                    if v_isShared_6908_ == 0 {
                        leanh::lean_ctor_set(v___x_6907_, 0, v___x_6915_);
                        v___x_6917_ = v___x_6907_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6918_, 0, v___x_6915_);
                        v___x_6917_ = v_reuseFailAlloc_6918_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6913_;
            }
            4 => {
                return v___x_6917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(
    mut v_ctx_6930_: *mut leanh::LeanObject,
    mut v_a_6931_: *mut leanh::LeanObject,
    mut v_a_6932_: *mut leanh::LeanObject,
    mut v_a_6933_: *mut leanh::LeanObject,
    mut v_a_6934_: *mut leanh::LeanObject,
    mut v_a_6935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6936_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(
        v_ctx_6930_,
        v_a_6931_,
        v_a_6932_,
        v_a_6933_,
        v_a_6934_,
    );
    leanh::lean_dec(v_a_6934_);
    leanh::lean_dec_ref(v_a_6933_);
    leanh::lean_dec(v_a_6932_);
    leanh::lean_dec_ref(v_a_6931_);
    return v_res_6936_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(
    mut v___x_6937_: *mut leanh::LeanObject,
    mut v_i_6938_: *mut leanh::LeanObject,
    mut v_n_6939_: *mut leanh::LeanObject,
    mut v_i_6940_: *mut leanh::LeanObject,
    mut v_a_6941_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6942_: u8 = 0;
    v___x_6942_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_6937_, v_i_6938_, v_n_6939_, v_i_6940_);
    return v___x_6942_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(
    mut v___x_6943_: *mut leanh::LeanObject,
    mut v_i_6944_: *mut leanh::LeanObject,
    mut v_n_6945_: *mut leanh::LeanObject,
    mut v_i_6946_: *mut leanh::LeanObject,
    mut v_a_6947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6948_: u8 = 0;
    let mut v_r_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6948_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_6943_, v_i_6944_, v_n_6945_, v_i_6946_, v_a_6947_);
    leanh::lean_dec(v_n_6945_);
    leanh::lean_dec(v_i_6944_);
    leanh::lean_dec_ref(v___x_6943_);
    v_r_6949_ = leanh::lean_box((v_res_6948_) as usize);
    return v_r_6949_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(
    mut v___x_6950_: *mut leanh::LeanObject,
    mut v_n_6951_: *mut leanh::LeanObject,
    mut v_i_6952_: *mut leanh::LeanObject,
    mut v_a_6953_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6954_: u8 = 0;
    v___x_6954_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_6950_, v_n_6951_, v_i_6952_);
    return v___x_6954_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(
    mut v___x_6955_: *mut leanh::LeanObject,
    mut v_n_6956_: *mut leanh::LeanObject,
    mut v_i_6957_: *mut leanh::LeanObject,
    mut v_a_6958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6959_: u8 = 0;
    let mut v_r_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6959_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_6955_, v_n_6956_, v_i_6957_, v_a_6958_);
    leanh::lean_dec(v_n_6956_);
    leanh::lean_dec_ref(v___x_6955_);
    v_r_6960_ = leanh::lean_box((v_res_6959_) as usize);
    return v_r_6960_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(
    mut v___x_6961_: u8,
    mut v___x_6962_: *mut leanh::LeanObject,
    mut v___x_6963_: *mut leanh::LeanObject,
    mut v_ctx_6964_: *mut leanh::LeanObject,
    mut v_as_6965_: *mut leanh::LeanObject,
    mut v_i_6966_: usize,
    mut v_stop_6967_: usize,
    mut v___y_6968_: *mut leanh::LeanObject,
    mut v___y_6969_: *mut leanh::LeanObject,
    mut v___y_6970_: *mut leanh::LeanObject,
    mut v___y_6971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6973_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_6961_, v___x_6962_, v___x_6963_, v_ctx_6964_, v_as_6965_, v_i_6966_, v_stop_6967_, v___y_6969_);
    return v___x_6973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(
    mut v___x_6974_: *mut leanh::LeanObject,
    mut v___x_6975_: *mut leanh::LeanObject,
    mut v___x_6976_: *mut leanh::LeanObject,
    mut v_ctx_6977_: *mut leanh::LeanObject,
    mut v_as_6978_: *mut leanh::LeanObject,
    mut v_i_6979_: *mut leanh::LeanObject,
    mut v_stop_6980_: *mut leanh::LeanObject,
    mut v___y_6981_: *mut leanh::LeanObject,
    mut v___y_6982_: *mut leanh::LeanObject,
    mut v___y_6983_: *mut leanh::LeanObject,
    mut v___y_6984_: *mut leanh::LeanObject,
    mut v___y_6985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9822__boxed_6986_: u8 = 0;
    let mut v_i_boxed_6987_: usize = 0;
    let mut v_stop_boxed_6988_: usize = 0;
    let mut v_res_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9822__boxed_6986_ = (leanh::lean_unbox(v___x_6974_) as u8);
    v_i_boxed_6987_ = leanh::lean_unbox_usize(v_i_6979_);
    leanh::lean_dec(v_i_6979_);
    v_stop_boxed_6988_ = leanh::lean_unbox_usize(v_stop_6980_);
    leanh::lean_dec(v_stop_6980_);
    v_res_6989_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_9822__boxed_6986_, v___x_6975_, v___x_6976_, v_ctx_6977_, v_as_6978_, v_i_boxed_6987_, v_stop_boxed_6988_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_);
    leanh::lean_dec(v___y_6984_);
    leanh::lean_dec_ref(v___y_6983_);
    leanh::lean_dec(v___y_6982_);
    leanh::lean_dec_ref(v___y_6981_);
    leanh::lean_dec_ref(v_as_6978_);
    leanh::lean_dec_ref(v_ctx_6977_);
    return v_res_6989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(
    mut v_as_6990_: *mut leanh::LeanObject,
    mut v_i_6991_: usize,
    mut v_stop_6992_: usize,
    mut v_b_6993_: *mut leanh::LeanObject,
    mut v___y_6994_: *mut leanh::LeanObject,
    mut v___y_6995_: *mut leanh::LeanObject,
    mut v___y_6996_: *mut leanh::LeanObject,
    mut v___y_6997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: usize = 0;
    let mut v___x_7002_: usize = 0;
    let mut v___x_7004_: u8 = 0;
    let mut v_toInductionSubgoal_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7012_: u8 = 0;
    let mut v___x_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7021_: u8 = 0;
    let mut v_a_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7030_: u8 = 0;
    let mut v_unused_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7036_: u8 = 0;
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7040_: u8 = 0;
    let mut v___x_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7045_: u8 = 0;
    let mut v___x_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7049_: u8 = 0;
    let mut v___x_7050_: u8 = 0;
    let mut v___x_7051_: u8 = 0;
    let mut v_reuseFailAlloc_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7053_: u8 = 0;
    let mut v_a_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7057_: u8 = 0;
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7061_: u8 = 0;
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7004_ = lean_usize_dec_eq(v_i_6991_, v_stop_6992_);
                if v___x_7004_ == 0 {
                    v_toInductionSubgoal_7005_ = leanh::lean_ctor_get(v_b_6993_, 0);
                    leanh::lean_inc_ref(v_toInductionSubgoal_7005_);
                    v_ctorName_7006_ = leanh::lean_ctor_get(v_b_6993_, 1);
                    v_mvarId_7007_ = leanh::lean_ctor_get(v_toInductionSubgoal_7005_, 0);
                    v_fields_7008_ = leanh::lean_ctor_get(v_toInductionSubgoal_7005_, 1);
                    v_subst_7009_ = leanh::lean_ctor_get(v_toInductionSubgoal_7005_, 2);
                    v_isSharedCheck_7062_ =
                        (!leanh::lean_is_exclusive(v_toInductionSubgoal_7005_)) as u8;
                    if v_isSharedCheck_7062_ == 0 {
                        v___x_7011_ = v_toInductionSubgoal_7005_;
                        v_isShared_7012_ = v_isSharedCheck_7062_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_subst_7009_);
                        leanh::lean_inc(v_fields_7008_);
                        leanh::lean_inc(v_mvarId_7007_);
                        leanh::lean_dec(v_toInductionSubgoal_7005_);
                        v___x_7011_ = leanh::lean_box(0);
                        v_isShared_7012_ = v_isSharedCheck_7062_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7063_, 0, v_b_6993_);
                    return v___x_7063_;
                }
            }
            1 => {
                v___x_7001_ = 1usize;
                v___x_7002_ = lean_usize_add(v_i_6991_, v___x_7001_);
                v_i_6991_ = v___x_7002_;
                v_b_6993_ = v_a_7000_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7013_ = lean_array_uget_borrowed(v_as_6990_, v_i_6991_);
                leanh::lean_inc(v___x_7013_);
                v___x_7014_ = l_Lean_Meta_FVarSubst_get(v_subst_7009_, v___x_7013_);
                if leanh::lean_obj_tag(v___x_7014_) == 1 {
                    v_fvarId_7015_ = leanh::lean_ctor_get(v___x_7014_, 0);
                    leanh::lean_inc(v_fvarId_7015_);
                    leanh::lean_dec_ref_known(v___x_7014_, 1);
                    v___x_7016_ = l_Lean_Meta_saveState___redArg(v___y_6995_, v___y_6997_);
                    if leanh::lean_obj_tag(v___x_7016_) == 0 {
                        v_a_7017_ = leanh::lean_ctor_get(v___x_7016_, 0);
                        leanh::lean_inc(v_a_7017_);
                        leanh::lean_dec_ref_known(v___x_7016_, 1);
                        v___x_7018_ = l_Lean_MVarId_clear(
                            v_mvarId_7007_,
                            v_fvarId_7015_,
                            v___y_6994_,
                            v___y_6995_,
                            v___y_6996_,
                            v___y_6997_,
                        );
                        if leanh::lean_obj_tag(v___x_7018_) == 0 {
                            leanh::lean_inc(v_ctorName_7006_);
                            leanh::lean_dec(v_a_7017_);
                            v_isSharedCheck_7030_ =
                                (!leanh::lean_is_exclusive(v_b_6993_)) as u8;
                            if v_isSharedCheck_7030_ == 0 {
                                v_unused_7031_ = leanh::lean_ctor_get(v_b_6993_, 1);
                                leanh::lean_dec(v_unused_7031_);
                                v_unused_7032_ = leanh::lean_ctor_get(v_b_6993_, 0);
                                leanh::lean_dec(v_unused_7032_);
                                v___x_7020_ = v_b_6993_;
                                v_isShared_7021_ = v_isSharedCheck_7030_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_b_6993_);
                                v___x_7020_ = leanh::lean_box(0);
                                v_isShared_7021_ = v_isSharedCheck_7030_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_7011_);
                            leanh::lean_dec(v_subst_7009_);
                            leanh::lean_dec_ref(v_fields_7008_);
                            v_a_7033_ = leanh::lean_ctor_get(v___x_7018_, 0);
                            v_isSharedCheck_7053_ =
                                (!leanh::lean_is_exclusive(v___x_7018_)) as u8;
                            if v_isSharedCheck_7053_ == 0 {
                                v___x_7035_ = v___x_7018_;
                                v_isShared_7036_ = v_isSharedCheck_7053_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7033_);
                                leanh::lean_dec(v___x_7018_);
                                v___x_7035_ = leanh::lean_box(0);
                                v_isShared_7036_ = v_isSharedCheck_7053_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_7015_);
                        leanh::lean_del_object(v___x_7011_);
                        leanh::lean_dec(v_subst_7009_);
                        leanh::lean_dec_ref(v_fields_7008_);
                        leanh::lean_dec(v_mvarId_7007_);
                        leanh::lean_dec_ref(v_b_6993_);
                        v_a_7054_ = leanh::lean_ctor_get(v___x_7016_, 0);
                        v_isSharedCheck_7061_ =
                            (!leanh::lean_is_exclusive(v___x_7016_)) as u8;
                        if v_isSharedCheck_7061_ == 0 {
                            v___x_7056_ = v___x_7016_;
                            v_isShared_7057_ = v_isSharedCheck_7061_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7054_);
                            leanh::lean_dec(v___x_7016_);
                            v___x_7056_ = leanh::lean_box(0);
                            v_isShared_7057_ = v_isSharedCheck_7061_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_7014_);
                    leanh::lean_del_object(v___x_7011_);
                    leanh::lean_dec(v_subst_7009_);
                    leanh::lean_dec_ref(v_fields_7008_);
                    leanh::lean_dec(v_mvarId_7007_);
                    v_a_7000_ = v_b_6993_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_7022_ = leanh::lean_ctor_get(v___x_7018_, 0);
                leanh::lean_inc(v_a_7022_);
                leanh::lean_dec_ref_known(v___x_7018_, 1);
                v___x_7023_ = l_Lean_Meta_FVarSubst_erase(v_subst_7009_, v___x_7013_);
                if v_isShared_7012_ == 0 {
                    leanh::lean_ctor_set(v___x_7011_, 2, v___x_7023_);
                    leanh::lean_ctor_set(v___x_7011_, 0, v_a_7022_);
                    v___x_7025_ = v___x_7011_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7029_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 0, v_a_7022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 1, v_fields_7008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 2, v___x_7023_);
                    v___x_7025_ = v_reuseFailAlloc_7029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7021_ == 0 {
                    leanh::lean_ctor_set(v___x_7020_, 0, v___x_7025_);
                    v___x_7027_ = v___x_7020_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 0, v___x_7025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 1, v_ctorName_7006_);
                    v___x_7027_ = v_reuseFailAlloc_7028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_7000_ = v___x_7027_;
                state = 1;
                continue;
            }
            6 => {
                leanh::lean_inc(v_a_7033_);
                if v_isShared_7036_ == 0 {
                    v___x_7038_ = v___x_7035_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7052_, 0, v_a_7033_);
                    v___x_7038_ = v_reuseFailAlloc_7052_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_7050_ = l_Lean_Exception_isInterrupt(v_a_7033_);
                if v___x_7050_ == 0 {
                    v___x_7051_ = l_Lean_Exception_isRuntime(v_a_7033_);
                    v___y_7040_ = v___x_7051_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7033_);
                    v___y_7040_ = v___x_7050_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_7040_ == 0 {
                    leanh::lean_dec_ref(v___x_7038_);
                    v___x_7041_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_7017_,
                        v___y_6995_,
                        v___y_6997_,
                    );
                    leanh::lean_dec(v_a_7017_);
                    if leanh::lean_obj_tag(v___x_7041_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7041_, 1);
                        v_a_7000_ = v_b_6993_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_6993_);
                        v_a_7042_ = leanh::lean_ctor_get(v___x_7041_, 0);
                        v_isSharedCheck_7049_ =
                            (!leanh::lean_is_exclusive(v___x_7041_)) as u8;
                        if v_isSharedCheck_7049_ == 0 {
                            v___x_7044_ = v___x_7041_;
                            v_isShared_7045_ = v_isSharedCheck_7049_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7042_);
                            leanh::lean_dec(v___x_7041_);
                            v___x_7044_ = leanh::lean_box(0);
                            v_isShared_7045_ = v_isSharedCheck_7049_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_7017_);
                    leanh::lean_dec_ref(v_b_6993_);
                    return v___x_7038_;
                }
            }
            9 => {
                if v_isShared_7045_ == 0 {
                    v___x_7047_ = v___x_7044_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7048_, 0, v_a_7042_);
                    v___x_7047_ = v_reuseFailAlloc_7048_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7047_;
            }
            11 => {
                if v_isShared_7057_ == 0 {
                    v___x_7059_ = v___x_7056_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7060_, 0, v_a_7054_);
                    v___x_7059_ = v_reuseFailAlloc_7060_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(
    mut v_as_7064_: *mut leanh::LeanObject,
    mut v_i_7065_: *mut leanh::LeanObject,
    mut v_stop_7066_: *mut leanh::LeanObject,
    mut v_b_7067_: *mut leanh::LeanObject,
    mut v___y_7068_: *mut leanh::LeanObject,
    mut v___y_7069_: *mut leanh::LeanObject,
    mut v___y_7070_: *mut leanh::LeanObject,
    mut v___y_7071_: *mut leanh::LeanObject,
    mut v___y_7072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7073_: usize = 0;
    let mut v_stop_boxed_7074_: usize = 0;
    let mut v_res_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7073_ = leanh::lean_unbox_usize(v_i_7065_);
    leanh::lean_dec(v_i_7065_);
    v_stop_boxed_7074_ = leanh::lean_unbox_usize(v_stop_7066_);
    leanh::lean_dec(v_stop_7066_);
    v_res_7075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_7064_, v_i_boxed_7073_, v_stop_boxed_7074_, v_b_7067_, v___y_7068_, v___y_7069_, v___y_7070_, v___y_7071_);
    leanh::lean_dec(v___y_7071_);
    leanh::lean_dec_ref(v___y_7070_);
    leanh::lean_dec(v___y_7069_);
    leanh::lean_dec_ref(v___y_7068_);
    leanh::lean_dec_ref(v_as_7064_);
    return v_res_7075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(
    mut v_indicesFVarIds_7076_: *mut leanh::LeanObject,
    mut v_sz_7077_: usize,
    mut v_i_7078_: usize,
    mut v_bs_7079_: *mut leanh::LeanObject,
    mut v___y_7080_: *mut leanh::LeanObject,
    mut v___y_7081_: *mut leanh::LeanObject,
    mut v___y_7082_: *mut leanh::LeanObject,
    mut v___y_7083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7085_: u8 = 0;
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: usize = 0;
    let mut v___x_7093_: usize = 0;
    let mut v___x_7094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v___x_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7106_: u8 = 0;
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: u8 = 0;
    let mut v___x_7109_: u8 = 0;
    let mut v___x_7110_: usize = 0;
    let mut v___x_7111_: usize = 0;
    let mut v___x_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: usize = 0;
    let mut v___x_7114_: usize = 0;
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7085_ = lean_usize_dec_lt(v_i_7078_, v_sz_7077_);
                if v___x_7085_ == 0 {
                    v___x_7086_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7086_, 0, v_bs_7079_);
                    return v___x_7086_;
                } else {
                    v_v_7087_ = lean_array_uget(v_bs_7079_, v_i_7078_);
                    v___x_7088_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_7089_ = lean_array_uset(v_bs_7079_, v_i_7078_, v___x_7088_);
                    v___x_7107_ = lean_array_get_size(v_indicesFVarIds_7076_);
                    v___x_7108_ = lean_nat_dec_lt(v___x_7088_, v___x_7107_);
                    if v___x_7108_ == 0 {
                        v_a_7091_ = v_v_7087_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7109_ = lean_nat_dec_le(v___x_7107_, v___x_7107_);
                        if v___x_7109_ == 0 {
                            if v___x_7108_ == 0 {
                                v_a_7091_ = v_v_7087_;
                                state = 1;
                                continue;
                            } else {
                                v___x_7110_ = 0usize;
                                v___x_7111_ = lean_usize_of_nat(v___x_7107_);
                                v___x_7112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_7076_, v___x_7110_, v___x_7111_, v_v_7087_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_);
                                v___y_7097_ = v___x_7112_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_7113_ = 0usize;
                            v___x_7114_ = lean_usize_of_nat(v___x_7107_);
                            v___x_7115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_7076_, v___x_7113_, v___x_7114_, v_v_7087_, v___y_7080_, v___y_7081_, v___y_7082_, v___y_7083_);
                            v___y_7097_ = v___x_7115_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7092_ = 1usize;
                v___x_7093_ = lean_usize_add(v_i_7078_, v___x_7092_);
                v___x_7094_ = lean_array_uset(v_bs_x27_7089_, v_i_7078_, v_a_7091_);
                v_i_7078_ = v___x_7093_;
                v_bs_7079_ = v___x_7094_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_7097_) == 0 {
                    v_a_7098_ = leanh::lean_ctor_get(v___y_7097_, 0);
                    leanh::lean_inc(v_a_7098_);
                    leanh::lean_dec_ref_known(v___y_7097_, 1);
                    v_a_7091_ = v_a_7098_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_bs_x27_7089_);
                    v_a_7099_ = leanh::lean_ctor_get(v___y_7097_, 0);
                    v_isSharedCheck_7106_ = (!leanh::lean_is_exclusive(v___y_7097_)) as u8;
                    if v_isSharedCheck_7106_ == 0 {
                        v___x_7101_ = v___y_7097_;
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7099_);
                        leanh::lean_dec(v___y_7097_);
                        v___x_7101_ = leanh::lean_box(0);
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7102_ == 0 {
                    v___x_7104_ = v___x_7101_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_a_7099_);
                    v___x_7104_ = v_reuseFailAlloc_7105_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(
    mut v_indicesFVarIds_7116_: *mut leanh::LeanObject,
    mut v_sz_7117_: *mut leanh::LeanObject,
    mut v_i_7118_: *mut leanh::LeanObject,
    mut v_bs_7119_: *mut leanh::LeanObject,
    mut v___y_7120_: *mut leanh::LeanObject,
    mut v___y_7121_: *mut leanh::LeanObject,
    mut v___y_7122_: *mut leanh::LeanObject,
    mut v___y_7123_: *mut leanh::LeanObject,
    mut v___y_7124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7125_: usize = 0;
    let mut v_i_boxed_7126_: usize = 0;
    let mut v_res_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7125_ = leanh::lean_unbox_usize(v_sz_7117_);
    leanh::lean_dec(v_sz_7117_);
    v_i_boxed_7126_ = leanh::lean_unbox_usize(v_i_7118_);
    leanh::lean_dec(v_i_7118_);
    v_res_7127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_7116_, v_sz_boxed_7125_, v_i_boxed_7126_, v_bs_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
    leanh::lean_dec(v___y_7123_);
    leanh::lean_dec_ref(v___y_7122_);
    leanh::lean_dec(v___y_7121_);
    leanh::lean_dec_ref(v___y_7120_);
    leanh::lean_dec_ref(v_indicesFVarIds_7116_);
    return v_res_7127_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(
    mut v_s_u2081_7128_: *mut leanh::LeanObject,
    mut v_s_u2082_7129_: *mut leanh::LeanObject,
    mut v_a_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: *mut leanh::LeanObject,
    mut v_a_7132_: *mut leanh::LeanObject,
    mut v_a_7133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indicesFVarIds_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7136_: usize = 0;
    let mut v___x_7137_: usize = 0;
    let mut v___x_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indicesFVarIds_7135_ = leanh::lean_ctor_get(v_s_u2081_7128_, 1);
    v_sz_7136_ = lean_array_size(v_s_u2082_7129_);
    v___x_7137_ = 0usize;
    v___x_7138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_7135_, v_sz_7136_, v___x_7137_, v_s_u2082_7129_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_);
    return v___x_7138_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(
    mut v_s_u2081_7139_: *mut leanh::LeanObject,
    mut v_s_u2082_7140_: *mut leanh::LeanObject,
    mut v_a_7141_: *mut leanh::LeanObject,
    mut v_a_7142_: *mut leanh::LeanObject,
    mut v_a_7143_: *mut leanh::LeanObject,
    mut v_a_7144_: *mut leanh::LeanObject,
    mut v_a_7145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7146_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(
        v_s_u2081_7139_,
        v_s_u2082_7140_,
        v_a_7141_,
        v_a_7142_,
        v_a_7143_,
        v_a_7144_,
    );
    leanh::lean_dec(v_a_7144_);
    leanh::lean_dec_ref(v_a_7143_);
    leanh::lean_dec(v_a_7142_);
    leanh::lean_dec_ref(v_a_7141_);
    leanh::lean_dec_ref(v_s_u2081_7139_);
    return v_res_7146_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(
    mut v_ctorNames_7147_: *mut leanh::LeanObject,
    mut v_us_7148_: *mut leanh::LeanObject,
    mut v_params_7149_: *mut leanh::LeanObject,
    mut v_majorFVarId_7150_: *mut leanh::LeanObject,
    mut v_as_7151_: *mut leanh::LeanObject,
    mut v_i_7152_: *mut leanh::LeanObject,
    mut v_j_7153_: *mut leanh::LeanObject,
    mut v_bs_7154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7156_: u8 = 0;
    let mut v_one_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: u8 = 0;
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7174_: u8 = 0;
    let mut v_ctorName_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorApp_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7155_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_7156_ = lean_nat_dec_eq(v_i_7152_, v_zero_7155_);
                if v_isZero_7156_ == 1 {
                    leanh::lean_dec(v_j_7153_);
                    leanh::lean_dec(v_i_7152_);
                    leanh::lean_dec(v_majorFVarId_7150_);
                    leanh::lean_dec(v_us_7148_);
                    return v_bs_7154_;
                } else {
                    v_one_7157_ = leanh::lean_unsigned_to_nat(1);
                    v_n_7158_ = lean_nat_sub(v_i_7152_, v_one_7157_);
                    leanh::lean_dec(v_i_7152_);
                    v___x_7164_ = lean_array_fget(v_as_7151_, v_j_7153_);
                    v___x_7165_ = lean_array_get_size(v_ctorNames_7147_);
                    v___x_7166_ = lean_nat_dec_lt(v_j_7153_, v___x_7165_);
                    if v___x_7166_ == 0 {
                        v___x_7167_ = leanh::lean_box(0);
                        v___x_7168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7168_, 0, v___x_7164_);
                        leanh::lean_ctor_set(v___x_7168_, 1, v___x_7167_);
                        v___y_7160_ = v___x_7168_;
                        state = 1;
                        continue;
                    } else {
                        v_mvarId_7169_ = leanh::lean_ctor_get(v___x_7164_, 0);
                        v_fields_7170_ = leanh::lean_ctor_get(v___x_7164_, 1);
                        v_subst_7171_ = leanh::lean_ctor_get(v___x_7164_, 2);
                        v_isSharedCheck_7186_ =
                            (!leanh::lean_is_exclusive(v___x_7164_)) as u8;
                        if v_isSharedCheck_7186_ == 0 {
                            v___x_7173_ = v___x_7164_;
                            v_isShared_7174_ = v_isSharedCheck_7186_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_subst_7171_);
                            leanh::lean_inc(v_fields_7170_);
                            leanh::lean_inc(v_mvarId_7169_);
                            leanh::lean_dec(v___x_7164_);
                            v___x_7173_ = leanh::lean_box(0);
                            v_isShared_7174_ = v_isSharedCheck_7186_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7161_ = lean_nat_add(v_j_7153_, v_one_7157_);
                leanh::lean_dec(v_j_7153_);
                v___x_7162_ = lean_array_push(v_bs_7154_, v___y_7160_);
                v_i_7152_ = v_n_7158_;
                v_j_7153_ = v___x_7161_;
                v_bs_7154_ = v___x_7162_;
                state = 0;
                continue;
            }
            2 => {
                v_ctorName_7175_ = lean_array_fget_borrowed(v_ctorNames_7147_, v_j_7153_);
                leanh::lean_inc(v_us_7148_);
                leanh::lean_inc(v_ctorName_7175_);
                v___x_7176_ = l_Lean_mkConst(v_ctorName_7175_, v_us_7148_);
                v___x_7177_ = l_Lean_mkAppN(v___x_7176_, v_params_7149_);
                v_ctorApp_7178_ = l_Lean_mkAppN(v___x_7177_, v_fields_7170_);
                v___x_7179_ = l_Lean_Meta_FVarSubst_erase(v_subst_7171_, v_majorFVarId_7150_);
                leanh::lean_inc(v_majorFVarId_7150_);
                v_subst_7180_ =
                    l_Lean_Meta_FVarSubst_insert(v___x_7179_, v_majorFVarId_7150_, v_ctorApp_7178_);
                if v_isShared_7174_ == 0 {
                    leanh::lean_ctor_set(v___x_7173_, 2, v_subst_7180_);
                    v___x_7182_ = v___x_7173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7185_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7185_, 0, v_mvarId_7169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7185_, 1, v_fields_7170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7185_, 2, v_subst_7180_);
                    v___x_7182_ = v_reuseFailAlloc_7185_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ctorName_7175_);
                v___x_7183_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7183_, 0, v_ctorName_7175_);
                v___x_7184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7184_, 0, v___x_7182_);
                leanh::lean_ctor_set(v___x_7184_, 1, v___x_7183_);
                v___y_7160_ = v___x_7184_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(
    mut v_ctorNames_7187_: *mut leanh::LeanObject,
    mut v_us_7188_: *mut leanh::LeanObject,
    mut v_params_7189_: *mut leanh::LeanObject,
    mut v_majorFVarId_7190_: *mut leanh::LeanObject,
    mut v_as_7191_: *mut leanh::LeanObject,
    mut v_i_7192_: *mut leanh::LeanObject,
    mut v_j_7193_: *mut leanh::LeanObject,
    mut v_bs_7194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7195_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_7187_, v_us_7188_, v_params_7189_, v_majorFVarId_7190_, v_as_7191_, v_i_7192_, v_j_7193_, v_bs_7194_);
    leanh::lean_dec_ref(v_as_7191_);
    leanh::lean_dec_ref(v_params_7189_);
    leanh::lean_dec_ref(v_ctorNames_7187_);
    return v_res_7195_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(
    mut v_s_7196_: *mut leanh::LeanObject,
    mut v_ctorNames_7197_: *mut leanh::LeanObject,
    mut v_majorFVarId_7198_: *mut leanh::LeanObject,
    mut v_us_7199_: *mut leanh::LeanObject,
    mut v_params_7200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7201_ = lean_array_get_size(v_s_7196_);
    v___x_7202_ = leanh::lean_unsigned_to_nat(0);
    v___x_7203_ = lean_mk_empty_array_with_capacity(v___x_7201_);
    v___x_7204_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_7197_, v_us_7199_, v_params_7200_, v_majorFVarId_7198_, v_s_7196_, v___x_7201_, v___x_7202_, v___x_7203_);
    return v___x_7204_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(
    mut v_s_7205_: *mut leanh::LeanObject,
    mut v_ctorNames_7206_: *mut leanh::LeanObject,
    mut v_majorFVarId_7207_: *mut leanh::LeanObject,
    mut v_us_7208_: *mut leanh::LeanObject,
    mut v_params_7209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7210_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(
        v_s_7205_,
        v_ctorNames_7206_,
        v_majorFVarId_7207_,
        v_us_7208_,
        v_params_7209_,
    );
    leanh::lean_dec_ref(v_params_7209_);
    leanh::lean_dec_ref(v_ctorNames_7206_);
    leanh::lean_dec_ref(v_s_7205_);
    return v_res_7210_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(
    mut v_ctorNames_7211_: *mut leanh::LeanObject,
    mut v_us_7212_: *mut leanh::LeanObject,
    mut v_params_7213_: *mut leanh::LeanObject,
    mut v_majorFVarId_7214_: *mut leanh::LeanObject,
    mut v_as_7215_: *mut leanh::LeanObject,
    mut v_i_7216_: *mut leanh::LeanObject,
    mut v_j_7217_: *mut leanh::LeanObject,
    mut v_inv_7218_: *mut leanh::LeanObject,
    mut v_bs_7219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7220_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_7211_, v_us_7212_, v_params_7213_, v_majorFVarId_7214_, v_as_7215_, v_i_7216_, v_j_7217_, v_bs_7219_);
    return v___x_7220_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(
    mut v_ctorNames_7221_: *mut leanh::LeanObject,
    mut v_us_7222_: *mut leanh::LeanObject,
    mut v_params_7223_: *mut leanh::LeanObject,
    mut v_majorFVarId_7224_: *mut leanh::LeanObject,
    mut v_as_7225_: *mut leanh::LeanObject,
    mut v_i_7226_: *mut leanh::LeanObject,
    mut v_j_7227_: *mut leanh::LeanObject,
    mut v_inv_7228_: *mut leanh::LeanObject,
    mut v_bs_7229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7230_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_7221_, v_us_7222_, v_params_7223_, v_majorFVarId_7224_, v_as_7225_, v_i_7226_, v_j_7227_, v_inv_7228_, v_bs_7229_);
    leanh::lean_dec_ref(v_as_7225_);
    leanh::lean_dec_ref(v_params_7223_);
    leanh::lean_dec_ref(v_ctorNames_7221_);
    return v_res_7230_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7236_ = l_Lean_maxRecDepthErrorMessage;
    v___x_7237_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7237_, 0, v___x_7236_);
    return v___x_7237_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
    v___x_7239_ = l_Lean_MessageData_ofFormat(v___x_7238_);
    return v___x_7239_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
    v___x_7241_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2;
    v___x_7242_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7242_, 0, v___x_7241_);
    leanh::lean_ctor_set(v___x_7242_, 1, v___x_7240_);
    return v___x_7242_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(
    mut v_ref_7243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7245_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
    v___x_7246_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7246_, 0, v_ref_7243_);
    leanh::lean_ctor_set(v___x_7246_, 1, v___x_7245_);
    v___x_7247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7247_, 0, v___x_7246_);
    return v___x_7247_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(
    mut v_ref_7248_: *mut leanh::LeanObject,
    mut v___y_7249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7250_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(
        v_ref_7248_,
    );
    return v_res_7250_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(
    mut v_00_u03b1_7251_: *mut leanh::LeanObject,
    mut v_ref_7252_: *mut leanh::LeanObject,
    mut v___y_7253_: *mut leanh::LeanObject,
    mut v___y_7254_: *mut leanh::LeanObject,
    mut v___y_7255_: *mut leanh::LeanObject,
    mut v___y_7256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7258_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(
        v_ref_7252_,
    );
    return v___x_7258_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(
    mut v_00_u03b1_7259_: *mut leanh::LeanObject,
    mut v_ref_7260_: *mut leanh::LeanObject,
    mut v___y_7261_: *mut leanh::LeanObject,
    mut v___y_7262_: *mut leanh::LeanObject,
    mut v___y_7263_: *mut leanh::LeanObject,
    mut v___y_7264_: *mut leanh::LeanObject,
    mut v___y_7265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7266_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(
        v_00_u03b1_7259_,
        v_ref_7260_,
        v___y_7261_,
        v___y_7262_,
        v___y_7263_,
        v___y_7264_,
    );
    leanh::lean_dec(v___y_7264_);
    leanh::lean_dec_ref(v___y_7263_);
    leanh::lean_dec(v___y_7262_);
    leanh::lean_dec_ref(v___y_7261_);
    return v_res_7266_;
}
pub unsafe fn l_Lean_Meta_Cases_unifyEqs_x3f(
    mut v_numEqs_7268_: *mut leanh::LeanObject,
    mut v_mvarId_7269_: *mut leanh::LeanObject,
    mut v_subst_7270_: *mut leanh::LeanObject,
    mut v_caseName_x3f_7271_: *mut leanh::LeanObject,
    mut v_a_7272_: *mut leanh::LeanObject,
    mut v_a_7273_: *mut leanh::LeanObject,
    mut v_a_7274_: *mut leanh::LeanObject,
    mut v_a_7275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7289_: u8 = 0;
    let mut v_cancelTk_x3f_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7291_: u8 = 0;
    let mut v_inheritedTraceOptions_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: u8 = 0;
    let mut v___x_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7308_: u8 = 0;
    let mut v_val_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNewEqs_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7320_: u8 = 0;
    let mut v_a_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7324_: u8 = 0;
    let mut v___x_7326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7328_: u8 = 0;
    let mut v_a_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7332_: u8 = 0;
    let mut v___x_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7336_: u8 = 0;
    let mut v___x_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: u8 = 0;
    let mut v___x_7341_: u8 = 0;
    let mut v___x_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_7277_ = leanh::lean_ctor_get(v_a_7274_, 0);
                leanh::lean_inc_ref(v_fileName_7277_);
                v_fileMap_7278_ = leanh::lean_ctor_get(v_a_7274_, 1);
                leanh::lean_inc_ref(v_fileMap_7278_);
                v_options_7279_ = leanh::lean_ctor_get(v_a_7274_, 2);
                leanh::lean_inc_ref(v_options_7279_);
                v_currRecDepth_7280_ = leanh::lean_ctor_get(v_a_7274_, 3);
                leanh::lean_inc(v_currRecDepth_7280_);
                v_maxRecDepth_7281_ = leanh::lean_ctor_get(v_a_7274_, 4);
                leanh::lean_inc(v_maxRecDepth_7281_);
                v_ref_7282_ = leanh::lean_ctor_get(v_a_7274_, 5);
                leanh::lean_inc(v_ref_7282_);
                v_currNamespace_7283_ = leanh::lean_ctor_get(v_a_7274_, 6);
                leanh::lean_inc(v_currNamespace_7283_);
                v_openDecls_7284_ = leanh::lean_ctor_get(v_a_7274_, 7);
                leanh::lean_inc(v_openDecls_7284_);
                v_initHeartbeats_7285_ = leanh::lean_ctor_get(v_a_7274_, 8);
                leanh::lean_inc(v_initHeartbeats_7285_);
                v_maxHeartbeats_7286_ = leanh::lean_ctor_get(v_a_7274_, 9);
                leanh::lean_inc(v_maxHeartbeats_7286_);
                v_quotContext_7287_ = leanh::lean_ctor_get(v_a_7274_, 10);
                leanh::lean_inc(v_quotContext_7287_);
                v_currMacroScope_7288_ = leanh::lean_ctor_get(v_a_7274_, 11);
                leanh::lean_inc(v_currMacroScope_7288_);
                v_diag_7289_ = leanh::lean_ctor_get_uint8(
                    v_a_7274_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7290_ = leanh::lean_ctor_get(v_a_7274_, 12);
                leanh::lean_inc(v_cancelTk_x3f_7290_);
                v_suppressElabErrors_7291_ = leanh::lean_ctor_get_uint8(
                    v_a_7274_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7292_ = leanh::lean_ctor_get(v_a_7274_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_7292_);
                leanh::lean_dec_ref(v_a_7274_);
                v___x_7293_ = leanh::lean_unsigned_to_nat(0);
                v___x_7294_ = lean_nat_dec_eq(v_numEqs_7268_, v___x_7293_);
                v___x_7340_ = lean_nat_dec_eq(v_maxRecDepth_7281_, v___x_7293_);
                if v___x_7340_ == 0 {
                    v___x_7341_ = lean_nat_dec_eq(v_currRecDepth_7280_, v_maxRecDepth_7281_);
                    if v___x_7341_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_inheritedTraceOptions_7292_);
                        leanh::lean_dec(v_cancelTk_x3f_7290_);
                        leanh::lean_dec(v_currMacroScope_7288_);
                        leanh::lean_dec(v_quotContext_7287_);
                        leanh::lean_dec(v_maxHeartbeats_7286_);
                        leanh::lean_dec(v_initHeartbeats_7285_);
                        leanh::lean_dec(v_openDecls_7284_);
                        leanh::lean_dec(v_currNamespace_7283_);
                        leanh::lean_dec(v_maxRecDepth_7281_);
                        leanh::lean_dec(v_currRecDepth_7280_);
                        leanh::lean_dec_ref(v_options_7279_);
                        leanh::lean_dec_ref(v_fileMap_7278_);
                        leanh::lean_dec_ref(v_fileName_7277_);
                        leanh::lean_dec(v_caseName_x3f_7271_);
                        leanh::lean_dec(v_subst_7270_);
                        leanh::lean_dec(v_mvarId_7269_);
                        leanh::lean_dec(v_numEqs_7268_);
                        v___x_7342_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_7282_);
                        return v___x_7342_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___x_7294_ == 0 {
                    v___x_7296_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7297_ = lean_nat_add(v_currRecDepth_7280_, v___x_7296_);
                    leanh::lean_dec(v_currRecDepth_7280_);
                    v___x_7298_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_7298_, 0, v_fileName_7277_);
                    leanh::lean_ctor_set(v___x_7298_, 1, v_fileMap_7278_);
                    leanh::lean_ctor_set(v___x_7298_, 2, v_options_7279_);
                    leanh::lean_ctor_set(v___x_7298_, 3, v___x_7297_);
                    leanh::lean_ctor_set(v___x_7298_, 4, v_maxRecDepth_7281_);
                    leanh::lean_ctor_set(v___x_7298_, 5, v_ref_7282_);
                    leanh::lean_ctor_set(v___x_7298_, 6, v_currNamespace_7283_);
                    leanh::lean_ctor_set(v___x_7298_, 7, v_openDecls_7284_);
                    leanh::lean_ctor_set(v___x_7298_, 8, v_initHeartbeats_7285_);
                    leanh::lean_ctor_set(v___x_7298_, 9, v_maxHeartbeats_7286_);
                    leanh::lean_ctor_set(v___x_7298_, 10, v_quotContext_7287_);
                    leanh::lean_ctor_set(v___x_7298_, 11, v_currMacroScope_7288_);
                    leanh::lean_ctor_set(v___x_7298_, 12, v_cancelTk_x3f_7290_);
                    leanh::lean_ctor_set(v___x_7298_, 13, v_inheritedTraceOptions_7292_);
                    leanh::lean_ctor_set_uint8(
                        v___x_7298_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_7289_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_7298_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_7291_,
                    );
                    v___x_7299_ = l_Lean_Meta_intro1Core(
                        v_mvarId_7269_,
                        v___x_7294_,
                        v_a_7272_,
                        v_a_7273_,
                        v___x_7298_,
                        v_a_7275_,
                    );
                    if leanh::lean_obj_tag(v___x_7299_) == 0 {
                        v_a_7300_ = leanh::lean_ctor_get(v___x_7299_, 0);
                        leanh::lean_inc(v_a_7300_);
                        leanh::lean_dec_ref_known(v___x_7299_, 1);
                        v_fst_7301_ = leanh::lean_ctor_get(v_a_7300_, 0);
                        leanh::lean_inc(v_fst_7301_);
                        v_snd_7302_ = leanh::lean_ctor_get(v_a_7300_, 1);
                        leanh::lean_inc(v_snd_7302_);
                        leanh::lean_dec(v_a_7300_);
                        v___x_7303_ = l_Lean_Meta_Cases_unifyEqs_x3f___closed__0;
                        leanh::lean_inc(v_caseName_x3f_7271_);
                        v___x_7304_ = l_Lean_Meta_unifyEq_x3f(
                            v_snd_7302_,
                            v_fst_7301_,
                            v_subst_7270_,
                            v___x_7303_,
                            v_caseName_x3f_7271_,
                            v_a_7272_,
                            v_a_7273_,
                            v___x_7298_,
                            v_a_7275_,
                        );
                        if leanh::lean_obj_tag(v___x_7304_) == 0 {
                            v_a_7305_ = leanh::lean_ctor_get(v___x_7304_, 0);
                            v_isSharedCheck_7320_ =
                                (!leanh::lean_is_exclusive(v___x_7304_)) as u8;
                            if v_isSharedCheck_7320_ == 0 {
                                v___x_7307_ = v___x_7304_;
                                v_isShared_7308_ = v_isSharedCheck_7320_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7305_);
                                leanh::lean_dec(v___x_7304_);
                                v___x_7307_ = leanh::lean_box(0);
                                v_isShared_7308_ = v_isSharedCheck_7320_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_7298_, 14);
                            leanh::lean_dec(v_caseName_x3f_7271_);
                            leanh::lean_dec(v_numEqs_7268_);
                            v_a_7321_ = leanh::lean_ctor_get(v___x_7304_, 0);
                            v_isSharedCheck_7328_ =
                                (!leanh::lean_is_exclusive(v___x_7304_)) as u8;
                            if v_isSharedCheck_7328_ == 0 {
                                v___x_7323_ = v___x_7304_;
                                v_isShared_7324_ = v_isSharedCheck_7328_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7321_);
                                leanh::lean_dec(v___x_7304_);
                                v___x_7323_ = leanh::lean_box(0);
                                v_isShared_7324_ = v_isSharedCheck_7328_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_7298_, 14);
                        leanh::lean_dec(v_caseName_x3f_7271_);
                        leanh::lean_dec(v_subst_7270_);
                        leanh::lean_dec(v_numEqs_7268_);
                        v_a_7329_ = leanh::lean_ctor_get(v___x_7299_, 0);
                        v_isSharedCheck_7336_ =
                            (!leanh::lean_is_exclusive(v___x_7299_)) as u8;
                        if v_isSharedCheck_7336_ == 0 {
                            v___x_7331_ = v___x_7299_;
                            v_isShared_7332_ = v_isSharedCheck_7336_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7329_);
                            leanh::lean_dec(v___x_7299_);
                            v___x_7331_ = leanh::lean_box(0);
                            v_isShared_7332_ = v_isSharedCheck_7336_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_inheritedTraceOptions_7292_);
                    leanh::lean_dec(v_cancelTk_x3f_7290_);
                    leanh::lean_dec(v_currMacroScope_7288_);
                    leanh::lean_dec(v_quotContext_7287_);
                    leanh::lean_dec(v_maxHeartbeats_7286_);
                    leanh::lean_dec(v_initHeartbeats_7285_);
                    leanh::lean_dec(v_openDecls_7284_);
                    leanh::lean_dec(v_currNamespace_7283_);
                    leanh::lean_dec(v_ref_7282_);
                    leanh::lean_dec(v_maxRecDepth_7281_);
                    leanh::lean_dec(v_currRecDepth_7280_);
                    leanh::lean_dec_ref(v_options_7279_);
                    leanh::lean_dec_ref(v_fileMap_7278_);
                    leanh::lean_dec_ref(v_fileName_7277_);
                    leanh::lean_dec(v_caseName_x3f_7271_);
                    leanh::lean_dec(v_numEqs_7268_);
                    v___x_7337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7337_, 0, v_mvarId_7269_);
                    leanh::lean_ctor_set(v___x_7337_, 1, v_subst_7270_);
                    v___x_7338_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7338_, 0, v___x_7337_);
                    v___x_7339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7339_, 0, v___x_7338_);
                    return v___x_7339_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_7305_) == 1 {
                    leanh::lean_del_object(v___x_7307_);
                    v_val_7309_ = leanh::lean_ctor_get(v_a_7305_, 0);
                    leanh::lean_inc(v_val_7309_);
                    leanh::lean_dec_ref_known(v_a_7305_, 1);
                    v_mvarId_7310_ = leanh::lean_ctor_get(v_val_7309_, 0);
                    leanh::lean_inc(v_mvarId_7310_);
                    v_subst_7311_ = leanh::lean_ctor_get(v_val_7309_, 1);
                    leanh::lean_inc(v_subst_7311_);
                    v_numNewEqs_7312_ = leanh::lean_ctor_get(v_val_7309_, 2);
                    leanh::lean_inc(v_numNewEqs_7312_);
                    leanh::lean_dec(v_val_7309_);
                    v___x_7313_ = lean_nat_sub(v_numEqs_7268_, v___x_7296_);
                    leanh::lean_dec(v_numEqs_7268_);
                    v___x_7314_ = lean_nat_add(v___x_7313_, v_numNewEqs_7312_);
                    leanh::lean_dec(v_numNewEqs_7312_);
                    leanh::lean_dec(v___x_7313_);
                    v_numEqs_7268_ = v___x_7314_;
                    v_mvarId_7269_ = v_mvarId_7310_;
                    v_subst_7270_ = v_subst_7311_;
                    v_a_7274_ = v___x_7298_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7305_);
                    leanh::lean_dec_ref_known(v___x_7298_, 14);
                    leanh::lean_dec(v_caseName_x3f_7271_);
                    leanh::lean_dec(v_numEqs_7268_);
                    v___x_7316_ = leanh::lean_box(0);
                    if v_isShared_7308_ == 0 {
                        leanh::lean_ctor_set(v___x_7307_, 0, v___x_7316_);
                        v___x_7318_ = v___x_7307_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7319_, 0, v___x_7316_);
                        v___x_7318_ = v_reuseFailAlloc_7319_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7318_;
            }
            4 => {
                if v_isShared_7324_ == 0 {
                    v___x_7326_ = v___x_7323_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7327_, 0, v_a_7321_);
                    v___x_7326_ = v_reuseFailAlloc_7327_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7326_;
            }
            6 => {
                if v_isShared_7332_ == 0 {
                    v___x_7334_ = v___x_7331_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7335_, 0, v_a_7329_);
                    v___x_7334_ = v_reuseFailAlloc_7335_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Cases_unifyEqs_x3f___boxed(
    mut v_numEqs_7343_: *mut leanh::LeanObject,
    mut v_mvarId_7344_: *mut leanh::LeanObject,
    mut v_subst_7345_: *mut leanh::LeanObject,
    mut v_caseName_x3f_7346_: *mut leanh::LeanObject,
    mut v_a_7347_: *mut leanh::LeanObject,
    mut v_a_7348_: *mut leanh::LeanObject,
    mut v_a_7349_: *mut leanh::LeanObject,
    mut v_a_7350_: *mut leanh::LeanObject,
    mut v_a_7351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7352_ = l_Lean_Meta_Cases_unifyEqs_x3f(
        v_numEqs_7343_,
        v_mvarId_7344_,
        v_subst_7345_,
        v_caseName_x3f_7346_,
        v_a_7347_,
        v_a_7348_,
        v_a_7349_,
        v_a_7350_,
    );
    leanh::lean_dec(v_a_7350_);
    leanh::lean_dec(v_a_7348_);
    leanh::lean_dec_ref(v_a_7347_);
    return v_res_7352_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(
    mut v_snd_7353_: *mut leanh::LeanObject,
    mut v_sz_7354_: usize,
    mut v_i_7355_: usize,
    mut v_bs_7356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7357_: u8 = 0;
    let mut v_v_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: usize = 0;
    let mut v___x_7363_: usize = 0;
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7357_ = lean_usize_dec_lt(v_i_7355_, v_sz_7354_);
                if v___x_7357_ == 0 {
                    leanh::lean_dec(v_snd_7353_);
                    return v_bs_7356_;
                } else {
                    v_v_7358_ = lean_array_uget(v_bs_7356_, v_i_7355_);
                    v___x_7359_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_7360_ = lean_array_uset(v_bs_7356_, v_i_7355_, v___x_7359_);
                    leanh::lean_inc(v_snd_7353_);
                    v___x_7361_ = l_Lean_Meta_FVarSubst_apply(v_snd_7353_, v_v_7358_);
                    leanh::lean_dec(v_v_7358_);
                    v___x_7362_ = 1usize;
                    v___x_7363_ = lean_usize_add(v_i_7355_, v___x_7362_);
                    v___x_7364_ = lean_array_uset(v_bs_x27_7360_, v_i_7355_, v___x_7361_);
                    v_i_7355_ = v___x_7363_;
                    v_bs_7356_ = v___x_7364_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(
    mut v_snd_7366_: *mut leanh::LeanObject,
    mut v_sz_7367_: *mut leanh::LeanObject,
    mut v_i_7368_: *mut leanh::LeanObject,
    mut v_bs_7369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7370_: usize = 0;
    let mut v_i_boxed_7371_: usize = 0;
    let mut v_res_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7370_ = leanh::lean_unbox_usize(v_sz_7367_);
    leanh::lean_dec(v_sz_7367_);
    v_i_boxed_7371_ = leanh::lean_unbox_usize(v_i_7368_);
    leanh::lean_dec(v_i_7368_);
    v_res_7372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_7366_, v_sz_boxed_7370_, v_i_boxed_7371_, v_bs_7369_);
    return v_res_7372_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(
    mut v_numEqs_7373_: *mut leanh::LeanObject,
    mut v_as_7374_: *mut leanh::LeanObject,
    mut v_i_7375_: usize,
    mut v_stop_7376_: usize,
    mut v_b_7377_: *mut leanh::LeanObject,
    mut v___y_7378_: *mut leanh::LeanObject,
    mut v___y_7379_: *mut leanh::LeanObject,
    mut v___y_7380_: *mut leanh::LeanObject,
    mut v___y_7381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7383_: u8 = 0;
    let mut v___x_7384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7389_: u8 = 0;
    let mut v_mvarId_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7395_: u8 = 0;
    let mut v___x_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: usize = 0;
    let mut v___x_7401_: usize = 0;
    let mut v_val_7403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7406_: usize = 0;
    let mut v___x_7407_: usize = 0;
    let mut v___x_7408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7419_: u8 = 0;
    let mut v___x_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7423_: u8 = 0;
    let mut v_isSharedCheck_7424_: u8 = 0;
    let mut v_isSharedCheck_7425_: u8 = 0;
    let mut v___x_7426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7383_ = lean_usize_dec_eq(v_i_7375_, v_stop_7376_);
                if v___x_7383_ == 0 {
                    v___x_7384_ = lean_array_uget(v_as_7374_, v_i_7375_);
                    v_toInductionSubgoal_7385_ = leanh::lean_ctor_get(v___x_7384_, 0);
                    v_ctorName_7386_ = leanh::lean_ctor_get(v___x_7384_, 1);
                    v_isSharedCheck_7425_ = (!leanh::lean_is_exclusive(v___x_7384_)) as u8;
                    if v_isSharedCheck_7425_ == 0 {
                        v___x_7388_ = v___x_7384_;
                        v_isShared_7389_ = v_isSharedCheck_7425_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_ctorName_7386_);
                        leanh::lean_inc(v_toInductionSubgoal_7385_);
                        leanh::lean_dec(v___x_7384_);
                        v___x_7388_ = leanh::lean_box(0);
                        v_isShared_7389_ = v_isSharedCheck_7425_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_numEqs_7373_);
                    v___x_7426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7426_, 0, v_b_7377_);
                    return v___x_7426_;
                }
            }
            1 => {
                v_mvarId_7390_ = leanh::lean_ctor_get(v_toInductionSubgoal_7385_, 0);
                v_fields_7391_ = leanh::lean_ctor_get(v_toInductionSubgoal_7385_, 1);
                v_subst_7392_ = leanh::lean_ctor_get(v_toInductionSubgoal_7385_, 2);
                v_isSharedCheck_7424_ =
                    (!leanh::lean_is_exclusive(v_toInductionSubgoal_7385_)) as u8;
                if v_isSharedCheck_7424_ == 0 {
                    v___x_7394_ = v_toInductionSubgoal_7385_;
                    v_isShared_7395_ = v_isSharedCheck_7424_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_subst_7392_);
                    leanh::lean_inc(v_fields_7391_);
                    leanh::lean_inc(v_mvarId_7390_);
                    leanh::lean_dec(v_toInductionSubgoal_7385_);
                    v___x_7394_ = leanh::lean_box(0);
                    v_isShared_7395_ = v_isSharedCheck_7424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_7380_);
                leanh::lean_inc(v_ctorName_7386_);
                leanh::lean_inc(v_numEqs_7373_);
                v___x_7396_ = l_Lean_Meta_Cases_unifyEqs_x3f(
                    v_numEqs_7373_,
                    v_mvarId_7390_,
                    v_subst_7392_,
                    v_ctorName_7386_,
                    v___y_7378_,
                    v___y_7379_,
                    v___y_7380_,
                    v___y_7381_,
                );
                if leanh::lean_obj_tag(v___x_7396_) == 0 {
                    v_a_7397_ = leanh::lean_ctor_get(v___x_7396_, 0);
                    leanh::lean_inc(v_a_7397_);
                    leanh::lean_dec_ref_known(v___x_7396_, 1);
                    if leanh::lean_obj_tag(v_a_7397_) == 0 {
                        leanh::lean_del_object(v___x_7394_);
                        leanh::lean_dec_ref(v_fields_7391_);
                        leanh::lean_del_object(v___x_7388_);
                        leanh::lean_dec(v_ctorName_7386_);
                        v_a_7399_ = v_b_7377_;
                        state = 3;
                        continue;
                    } else {
                        v_val_7403_ = leanh::lean_ctor_get(v_a_7397_, 0);
                        leanh::lean_inc(v_val_7403_);
                        leanh::lean_dec_ref_known(v_a_7397_, 1);
                        v_fst_7404_ = leanh::lean_ctor_get(v_val_7403_, 0);
                        leanh::lean_inc(v_fst_7404_);
                        v_snd_7405_ = leanh::lean_ctor_get(v_val_7403_, 1);
                        leanh::lean_inc_n(v_snd_7405_, 2);
                        leanh::lean_dec(v_val_7403_);
                        v_sz_7406_ = lean_array_size(v_fields_7391_);
                        v___x_7407_ = 0usize;
                        v___x_7408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_7405_, v_sz_7406_, v___x_7407_, v_fields_7391_);
                        if v_isShared_7395_ == 0 {
                            leanh::lean_ctor_set(v___x_7394_, 2, v_snd_7405_);
                            leanh::lean_ctor_set(v___x_7394_, 1, v___x_7408_);
                            leanh::lean_ctor_set(v___x_7394_, 0, v_fst_7404_);
                            v___x_7410_ = v___x_7394_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7415_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 0, v_fst_7404_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 1, v___x_7408_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 2, v_snd_7405_);
                            v___x_7410_ = v_reuseFailAlloc_7415_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7394_);
                    leanh::lean_dec_ref(v_fields_7391_);
                    leanh::lean_del_object(v___x_7388_);
                    leanh::lean_dec(v_ctorName_7386_);
                    leanh::lean_dec_ref(v_b_7377_);
                    leanh::lean_dec(v_numEqs_7373_);
                    v_a_7416_ = leanh::lean_ctor_get(v___x_7396_, 0);
                    v_isSharedCheck_7423_ = (!leanh::lean_is_exclusive(v___x_7396_)) as u8;
                    if v_isSharedCheck_7423_ == 0 {
                        v___x_7418_ = v___x_7396_;
                        v_isShared_7419_ = v_isSharedCheck_7423_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7416_);
                        leanh::lean_dec(v___x_7396_);
                        v___x_7418_ = leanh::lean_box(0);
                        v_isShared_7419_ = v_isSharedCheck_7423_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7400_ = 1usize;
                v___x_7401_ = lean_usize_add(v_i_7375_, v___x_7400_);
                v_i_7375_ = v___x_7401_;
                v_b_7377_ = v_a_7399_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_7389_ == 0 {
                    leanh::lean_ctor_set(v___x_7388_, 0, v___x_7410_);
                    v___x_7412_ = v___x_7388_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 0, v___x_7410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 1, v_ctorName_7386_);
                    v___x_7412_ = v_reuseFailAlloc_7414_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7413_ = lean_array_push(v_b_7377_, v___x_7412_);
                v_a_7399_ = v___x_7413_;
                state = 3;
                continue;
            }
            6 => {
                if v_isShared_7419_ == 0 {
                    v___x_7421_ = v___x_7418_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7422_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7422_, 0, v_a_7416_);
                    v___x_7421_ = v_reuseFailAlloc_7422_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(
    mut v_numEqs_7427_: *mut leanh::LeanObject,
    mut v_as_7428_: *mut leanh::LeanObject,
    mut v_i_7429_: *mut leanh::LeanObject,
    mut v_stop_7430_: *mut leanh::LeanObject,
    mut v_b_7431_: *mut leanh::LeanObject,
    mut v___y_7432_: *mut leanh::LeanObject,
    mut v___y_7433_: *mut leanh::LeanObject,
    mut v___y_7434_: *mut leanh::LeanObject,
    mut v___y_7435_: *mut leanh::LeanObject,
    mut v___y_7436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7437_: usize = 0;
    let mut v_stop_boxed_7438_: usize = 0;
    let mut v_res_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7437_ = leanh::lean_unbox_usize(v_i_7429_);
    leanh::lean_dec(v_i_7429_);
    v_stop_boxed_7438_ = leanh::lean_unbox_usize(v_stop_7430_);
    leanh::lean_dec(v_stop_7430_);
    v_res_7439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_7427_, v_as_7428_, v_i_boxed_7437_, v_stop_boxed_7438_, v_b_7431_, v___y_7432_, v___y_7433_, v___y_7434_, v___y_7435_);
    leanh::lean_dec(v___y_7435_);
    leanh::lean_dec_ref(v___y_7434_);
    leanh::lean_dec(v___y_7433_);
    leanh::lean_dec_ref(v___y_7432_);
    leanh::lean_dec_ref(v_as_7428_);
    return v_res_7439_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(
    mut v_numEqs_7442_: *mut leanh::LeanObject,
    mut v_as_7443_: *mut leanh::LeanObject,
    mut v_start_7444_: *mut leanh::LeanObject,
    mut v_stop_7445_: *mut leanh::LeanObject,
    mut v___y_7446_: *mut leanh::LeanObject,
    mut v___y_7447_: *mut leanh::LeanObject,
    mut v___y_7448_: *mut leanh::LeanObject,
    mut v___y_7449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: u8 = 0;
    v___x_7451_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0;
    v___x_7452_ = lean_nat_dec_lt(v_start_7444_, v_stop_7445_);
    if v___x_7452_ == 0 {
        let mut v___x_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_numEqs_7442_);
        v___x_7453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7453_, 0, v___x_7451_);
        return v___x_7453_;
    } else {
        let mut v___x_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7455_: u8 = 0;
        v___x_7454_ = lean_array_get_size(v_as_7443_);
        v___x_7455_ = lean_nat_dec_le(v_stop_7445_, v___x_7454_);
        if v___x_7455_ == 0 {
            let mut v___x_7456_: u8 = 0;
            v___x_7456_ = lean_nat_dec_lt(v_start_7444_, v___x_7454_);
            if v___x_7456_ == 0 {
                let mut v___x_7457_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_numEqs_7442_);
                v___x_7457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7457_, 0, v___x_7451_);
                return v___x_7457_;
            } else {
                let mut v___x_7458_: usize = 0;
                let mut v___x_7459_: usize = 0;
                let mut v___x_7460_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_7458_ = lean_usize_of_nat(v_start_7444_);
                v___x_7459_ = lean_usize_of_nat(v___x_7454_);
                v___x_7460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_7442_, v_as_7443_, v___x_7458_, v___x_7459_, v___x_7451_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
                return v___x_7460_;
            }
        } else {
            let mut v___x_7461_: usize = 0;
            let mut v___x_7462_: usize = 0;
            let mut v___x_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_7461_ = lean_usize_of_nat(v_start_7444_);
            v___x_7462_ = lean_usize_of_nat(v_stop_7445_);
            v___x_7463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_7442_, v_as_7443_, v___x_7461_, v___x_7462_, v___x_7451_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
            return v___x_7463_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(
    mut v_numEqs_7464_: *mut leanh::LeanObject,
    mut v_as_7465_: *mut leanh::LeanObject,
    mut v_start_7466_: *mut leanh::LeanObject,
    mut v_stop_7467_: *mut leanh::LeanObject,
    mut v___y_7468_: *mut leanh::LeanObject,
    mut v___y_7469_: *mut leanh::LeanObject,
    mut v___y_7470_: *mut leanh::LeanObject,
    mut v___y_7471_: *mut leanh::LeanObject,
    mut v___y_7472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7473_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_7464_, v_as_7465_, v_start_7466_, v_stop_7467_, v___y_7468_, v___y_7469_, v___y_7470_, v___y_7471_);
    leanh::lean_dec(v___y_7471_);
    leanh::lean_dec_ref(v___y_7470_);
    leanh::lean_dec(v___y_7469_);
    leanh::lean_dec_ref(v___y_7468_);
    leanh::lean_dec(v_stop_7467_);
    leanh::lean_dec(v_start_7466_);
    leanh::lean_dec_ref(v_as_7465_);
    return v_res_7473_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(
    mut v_numEqs_7474_: *mut leanh::LeanObject,
    mut v_subgoals_7475_: *mut leanh::LeanObject,
    mut v_a_7476_: *mut leanh::LeanObject,
    mut v_a_7477_: *mut leanh::LeanObject,
    mut v_a_7478_: *mut leanh::LeanObject,
    mut v_a_7479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7481_ = leanh::lean_unsigned_to_nat(0);
    v___x_7482_ = lean_array_get_size(v_subgoals_7475_);
    v___x_7483_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_7474_, v_subgoals_7475_, v___x_7481_, v___x_7482_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_);
    return v___x_7483_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(
    mut v_numEqs_7484_: *mut leanh::LeanObject,
    mut v_subgoals_7485_: *mut leanh::LeanObject,
    mut v_a_7486_: *mut leanh::LeanObject,
    mut v_a_7487_: *mut leanh::LeanObject,
    mut v_a_7488_: *mut leanh::LeanObject,
    mut v_a_7489_: *mut leanh::LeanObject,
    mut v_a_7490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7491_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(
        v_numEqs_7484_,
        v_subgoals_7485_,
        v_a_7486_,
        v_a_7487_,
        v_a_7488_,
        v_a_7489_,
    );
    leanh::lean_dec(v_a_7489_);
    leanh::lean_dec_ref(v_a_7488_);
    leanh::lean_dec(v_a_7487_);
    leanh::lean_dec_ref(v_a_7486_);
    leanh::lean_dec_ref(v_subgoals_7485_);
    return v_res_7491_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(
    mut v___x_7503_: *mut leanh::LeanObject,
    mut v_mvarId_7504_: *mut leanh::LeanObject,
    mut v_majorFVarId_7505_: *mut leanh::LeanObject,
    mut v_givenNames_7506_: *mut leanh::LeanObject,
    mut v_ctx_7507_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7508_: u8,
    mut v_interestingCtors_x3f_7509_: *mut leanh::LeanObject,
    mut v___y_7510_: *mut leanh::LeanObject,
    mut v___y_7511_: *mut leanh::LeanObject,
    mut v___y_7512_: *mut leanh::LeanObject,
    mut v___y_7513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inductiveVal_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7532_: u8 = 0;
    let mut v_ctors_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7539_: u8 = 0;
    let mut v_a_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7543_: u8 = 0;
    let mut v___x_7545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7547_: u8 = 0;
    let mut v___y_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inductiveVal_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inductiveVal_7563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: u8 = 0;
    let mut v___x_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: u8 = 0;
    let mut v_val_7571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inductiveVal_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7580_: u8 = 0;
    let mut v___x_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: u8 = 0;
    let mut v___x_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: u8 = 0;
    let mut v___x_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7592_: u8 = 0;
    let mut v___x_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7597_: u8 = 0;
    let mut v_a_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7601_: u8 = 0;
    let mut v___x_7603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7605_: u8 = 0;
    let mut v_a_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7609_: u8 = 0;
    let mut v___x_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7613_: u8 = 0;
    let mut v___x_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: u8 = 0;
    let mut v___x_7616_: u8 = 0;
    let mut v_env_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: u8 = 0;
    let mut v_a_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7623_: u8 = 0;
    let mut v___x_7625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7627_: u8 = 0;
    let mut v_a_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7631_: u8 = 0;
    let mut v___x_7633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_7513_);
                leanh::lean_inc_ref(v___y_7512_);
                leanh::lean_inc(v___y_7511_);
                leanh::lean_inc_ref(v___y_7510_);
                v___x_7515_ = lean_infer_type(
                    v___x_7503_,
                    v___y_7510_,
                    v___y_7511_,
                    v___y_7512_,
                    v___y_7513_,
                );
                if leanh::lean_obj_tag(v___x_7515_) == 0 {
                    v_a_7516_ = leanh::lean_ctor_get(v___x_7515_, 0);
                    leanh::lean_inc(v_a_7516_);
                    leanh::lean_dec_ref_known(v___x_7515_, 1);
                    v___x_7517_ = l_Lean_Meta_getInductiveUniverseAndParams(
                        v_a_7516_,
                        v___y_7510_,
                        v___y_7511_,
                        v___y_7512_,
                        v___y_7513_,
                    );
                    if leanh::lean_obj_tag(v___x_7517_) == 0 {
                        v_a_7518_ = leanh::lean_ctor_get(v___x_7517_, 0);
                        leanh::lean_inc(v_a_7518_);
                        leanh::lean_dec_ref_known(v___x_7517_, 1);
                        v_fst_7519_ = leanh::lean_ctor_get(v_a_7518_, 0);
                        leanh::lean_inc(v_fst_7519_);
                        v_snd_7520_ = leanh::lean_ctor_get(v_a_7518_, 1);
                        leanh::lean_inc(v_snd_7520_);
                        leanh::lean_dec(v_a_7518_);
                        if leanh::lean_obj_tag(v_interestingCtors_x3f_7509_) == 1 {
                            v_val_7571_ =
                                leanh::lean_ctor_get(v_interestingCtors_x3f_7509_, 0);
                            leanh::lean_inc(v_val_7571_);
                            leanh::lean_dec_ref_known(v_interestingCtors_x3f_7509_, 1);
                            v___x_7572_ = lean_st_ref_get(v___y_7513_);
                            v___x_7573_ = lean_st_ref_get(v___y_7513_);
                            v_inductiveVal_7574_ = leanh::lean_ctor_get(v_ctx_7507_, 0);
                            v_toConstantVal_7575_ =
                                leanh::lean_ctor_get(v_inductiveVal_7574_, 0);
                            v_env_7576_ = leanh::lean_ctor_get(v___x_7572_, 0);
                            leanh::lean_inc_ref(v_env_7576_);
                            leanh::lean_dec(v___x_7572_);
                            v_ctors_7577_ = leanh::lean_ctor_get(v_inductiveVal_7574_, 4);
                            v_name_7578_ = leanh::lean_ctor_get(v_toConstantVal_7575_, 0);
                            v___x_7614_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5;
                            v___x_7615_ = 1;
                            v___x_7616_ =
                                l_Lean_Environment_contains(v_env_7576_, v___x_7614_, v___x_7615_);
                            if v___x_7616_ == 0 {
                                leanh::lean_dec(v___x_7573_);
                                v___y_7580_ = v___x_7616_;
                                state = 8;
                                continue;
                            } else {
                                v_env_7617_ = leanh::lean_ctor_get(v___x_7573_, 0);
                                leanh::lean_inc_ref(v_env_7617_);
                                leanh::lean_dec(v___x_7573_);
                                leanh::lean_inc(v_name_7578_);
                                v___x_7618_ = l_mkCtorIdxName(v_name_7578_);
                                v___x_7619_ = l_Lean_Environment_contains(
                                    v_env_7617_,
                                    v___x_7618_,
                                    v___x_7615_,
                                );
                                v___y_7580_ = v___x_7619_;
                                state = 8;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_interestingCtors_x3f_7509_);
                            v___y_7558_ = v___y_7510_;
                            v___y_7559_ = v___y_7511_;
                            v___y_7560_ = v___y_7512_;
                            v___y_7561_ = v___y_7513_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_7513_);
                        leanh::lean_dec_ref(v___y_7512_);
                        leanh::lean_dec(v___y_7511_);
                        leanh::lean_dec_ref(v___y_7510_);
                        leanh::lean_dec(v_interestingCtors_x3f_7509_);
                        leanh::lean_dec_ref(v_ctx_7507_);
                        leanh::lean_dec_ref(v_givenNames_7506_);
                        leanh::lean_dec(v_majorFVarId_7505_);
                        leanh::lean_dec(v_mvarId_7504_);
                        v_a_7620_ = leanh::lean_ctor_get(v___x_7517_, 0);
                        v_isSharedCheck_7627_ =
                            (!leanh::lean_is_exclusive(v___x_7517_)) as u8;
                        if v_isSharedCheck_7627_ == 0 {
                            v___x_7622_ = v___x_7517_;
                            v_isShared_7623_ = v_isSharedCheck_7627_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7620_);
                            leanh::lean_dec(v___x_7517_);
                            v___x_7622_ = leanh::lean_box(0);
                            v_isShared_7623_ = v_isSharedCheck_7627_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_7513_);
                    leanh::lean_dec_ref(v___y_7512_);
                    leanh::lean_dec(v___y_7511_);
                    leanh::lean_dec_ref(v___y_7510_);
                    leanh::lean_dec(v_interestingCtors_x3f_7509_);
                    leanh::lean_dec_ref(v_ctx_7507_);
                    leanh::lean_dec_ref(v_givenNames_7506_);
                    leanh::lean_dec(v_majorFVarId_7505_);
                    leanh::lean_dec(v_mvarId_7504_);
                    v_a_7628_ = leanh::lean_ctor_get(v___x_7515_, 0);
                    v_isSharedCheck_7635_ = (!leanh::lean_is_exclusive(v___x_7515_)) as u8;
                    if v_isSharedCheck_7635_ == 0 {
                        v___x_7630_ = v___x_7515_;
                        v_isShared_7631_ = v_isSharedCheck_7635_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7628_);
                        leanh::lean_dec(v___x_7515_);
                        v___x_7630_ = leanh::lean_box(0);
                        v_isShared_7631_ = v_isSharedCheck_7635_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_majorFVarId_7505_);
                v___x_7527_ = l_Lean_MVarId_induction(
                    v_mvarId_7504_,
                    v_majorFVarId_7505_,
                    v___y_7526_,
                    v_givenNames_7506_,
                    v___y_7524_,
                    v___y_7525_,
                    v___y_7523_,
                    v___y_7522_,
                );
                leanh::lean_dec(v___y_7522_);
                leanh::lean_dec_ref(v___y_7523_);
                leanh::lean_dec(v___y_7525_);
                leanh::lean_dec_ref(v___y_7524_);
                if leanh::lean_obj_tag(v___x_7527_) == 0 {
                    v_inductiveVal_7528_ = leanh::lean_ctor_get(v_ctx_7507_, 0);
                    leanh::lean_inc_ref(v_inductiveVal_7528_);
                    leanh::lean_dec_ref(v_ctx_7507_);
                    v_a_7529_ = leanh::lean_ctor_get(v___x_7527_, 0);
                    v_isSharedCheck_7539_ = (!leanh::lean_is_exclusive(v___x_7527_)) as u8;
                    if v_isSharedCheck_7539_ == 0 {
                        v___x_7531_ = v___x_7527_;
                        v_isShared_7532_ = v_isSharedCheck_7539_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7529_);
                        leanh::lean_dec(v___x_7527_);
                        v___x_7531_ = leanh::lean_box(0);
                        v_isShared_7532_ = v_isSharedCheck_7539_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_7520_);
                    leanh::lean_dec(v_fst_7519_);
                    leanh::lean_dec_ref(v_ctx_7507_);
                    leanh::lean_dec(v_majorFVarId_7505_);
                    v_a_7540_ = leanh::lean_ctor_get(v___x_7527_, 0);
                    v_isSharedCheck_7547_ = (!leanh::lean_is_exclusive(v___x_7527_)) as u8;
                    if v_isSharedCheck_7547_ == 0 {
                        v___x_7542_ = v___x_7527_;
                        v_isShared_7543_ = v_isSharedCheck_7547_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7540_);
                        leanh::lean_dec(v___x_7527_);
                        v___x_7542_ = leanh::lean_box(0);
                        v_isShared_7543_ = v_isSharedCheck_7547_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_ctors_7533_ = leanh::lean_ctor_get(v_inductiveVal_7528_, 4);
                leanh::lean_inc(v_ctors_7533_);
                leanh::lean_dec_ref(v_inductiveVal_7528_);
                v___x_7534_ = lean_array_mk(v_ctors_7533_);
                v___x_7535_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(
                    v_a_7529_,
                    v___x_7534_,
                    v_majorFVarId_7505_,
                    v_fst_7519_,
                    v_snd_7520_,
                );
                leanh::lean_dec(v_snd_7520_);
                leanh::lean_dec_ref(v___x_7534_);
                leanh::lean_dec(v_a_7529_);
                if v_isShared_7532_ == 0 {
                    leanh::lean_ctor_set(v___x_7531_, 0, v___x_7535_);
                    v___x_7537_ = v___x_7531_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7538_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7538_, 0, v___x_7535_);
                    v___x_7537_ = v_reuseFailAlloc_7538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7537_;
            }
            4 => {
                if v_isShared_7543_ == 0 {
                    v___x_7545_ = v___x_7542_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7546_, 0, v_a_7540_);
                    v___x_7545_ = v_reuseFailAlloc_7546_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7545_;
            }
            6 => {
                v_inductiveVal_7553_ = leanh::lean_ctor_get(v_ctx_7507_, 0);
                v_toConstantVal_7554_ = leanh::lean_ctor_get(v_inductiveVal_7553_, 0);
                v_name_7555_ = leanh::lean_ctor_get(v_toConstantVal_7554_, 0);
                leanh::lean_inc(v_name_7555_);
                v___x_7556_ = l_Lean_mkCasesOnName(v_name_7555_);
                v___y_7522_ = v___y_7549_;
                v___y_7523_ = v___y_7550_;
                v___y_7524_ = v___y_7551_;
                v___y_7525_ = v___y_7552_;
                v___y_7526_ = v___x_7556_;
                state = 1;
                continue;
            }
            7 => {
                v___x_7562_ = lean_st_ref_get(v___y_7561_);
                if v_useNatCasesAuxOn_7508_ == 0 {
                    leanh::lean_dec(v___x_7562_);
                    v___y_7549_ = v___y_7561_;
                    v___y_7550_ = v___y_7560_;
                    v___y_7551_ = v___y_7558_;
                    v___y_7552_ = v___y_7559_;
                    state = 6;
                    continue;
                } else {
                    v_inductiveVal_7563_ = leanh::lean_ctor_get(v_ctx_7507_, 0);
                    v_toConstantVal_7564_ = leanh::lean_ctor_get(v_inductiveVal_7563_, 0);
                    v_env_7565_ = leanh::lean_ctor_get(v___x_7562_, 0);
                    leanh::lean_inc_ref(v_env_7565_);
                    leanh::lean_dec(v___x_7562_);
                    v_name_7566_ = leanh::lean_ctor_get(v_toConstantVal_7564_, 0);
                    v___x_7567_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1;
                    v___x_7568_ = lean_name_eq(v_name_7566_, v___x_7567_);
                    if v___x_7568_ == 0 {
                        leanh::lean_dec_ref(v_env_7565_);
                        v___y_7549_ = v___y_7561_;
                        v___y_7550_ = v___y_7560_;
                        v___y_7551_ = v___y_7558_;
                        v___y_7552_ = v___y_7559_;
                        state = 6;
                        continue;
                    } else {
                        v___x_7569_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3;
                        v___x_7570_ =
                            l_Lean_Environment_contains(v_env_7565_, v___x_7569_, v___x_7568_);
                        if v___x_7570_ == 0 {
                            v___y_7549_ = v___y_7561_;
                            v___y_7550_ = v___y_7560_;
                            v___y_7551_ = v___y_7558_;
                            v___y_7552_ = v___y_7559_;
                            state = 6;
                            continue;
                        } else {
                            v___y_7522_ = v___y_7561_;
                            v___y_7523_ = v___y_7560_;
                            v___y_7524_ = v___y_7558_;
                            v___y_7525_ = v___y_7559_;
                            v___y_7526_ = v___x_7569_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v___y_7580_ == 0 {
                    leanh::lean_dec(v_val_7571_);
                    v___y_7558_ = v___y_7510_;
                    v___y_7559_ = v___y_7511_;
                    v___y_7560_ = v___y_7512_;
                    v___y_7561_ = v___y_7513_;
                    state = 7;
                    continue;
                } else {
                    v___x_7581_ = lean_array_get_size(v_val_7571_);
                    v___x_7582_ = leanh::lean_unsigned_to_nat(0);
                    v___x_7583_ = lean_nat_dec_eq(v___x_7581_, v___x_7582_);
                    if v___x_7583_ == 0 {
                        v___x_7584_ = l_List_lengthTR___redArg(v_ctors_7577_);
                        v___x_7585_ = lean_nat_dec_lt(v___x_7581_, v___x_7584_);
                        leanh::lean_dec(v___x_7584_);
                        if v___x_7585_ == 0 {
                            leanh::lean_dec(v_val_7571_);
                            v___y_7558_ = v___y_7510_;
                            v___y_7559_ = v___y_7511_;
                            v___y_7560_ = v___y_7512_;
                            v___y_7561_ = v___y_7513_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_name_7578_);
                            leanh::lean_dec_ref(v_ctx_7507_);
                            leanh::lean_inc(v_val_7571_);
                            v___x_7586_ = l_Lean_Meta_mkSparseCasesOn(
                                v_name_7578_,
                                v_val_7571_,
                                v___y_7510_,
                                v___y_7511_,
                                v___y_7512_,
                                v___y_7513_,
                            );
                            if leanh::lean_obj_tag(v___x_7586_) == 0 {
                                v_a_7587_ = leanh::lean_ctor_get(v___x_7586_, 0);
                                leanh::lean_inc(v_a_7587_);
                                leanh::lean_dec_ref_known(v___x_7586_, 1);
                                leanh::lean_inc(v_majorFVarId_7505_);
                                v___x_7588_ = l_Lean_MVarId_induction(
                                    v_mvarId_7504_,
                                    v_majorFVarId_7505_,
                                    v_a_7587_,
                                    v_givenNames_7506_,
                                    v___y_7510_,
                                    v___y_7511_,
                                    v___y_7512_,
                                    v___y_7513_,
                                );
                                leanh::lean_dec(v___y_7513_);
                                leanh::lean_dec_ref(v___y_7512_);
                                leanh::lean_dec(v___y_7511_);
                                leanh::lean_dec_ref(v___y_7510_);
                                if leanh::lean_obj_tag(v___x_7588_) == 0 {
                                    v_a_7589_ = leanh::lean_ctor_get(v___x_7588_, 0);
                                    v_isSharedCheck_7597_ =
                                        (!leanh::lean_is_exclusive(v___x_7588_)) as u8;
                                    if v_isSharedCheck_7597_ == 0 {
                                        v___x_7591_ = v___x_7588_;
                                        v_isShared_7592_ = v_isSharedCheck_7597_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7589_);
                                        leanh::lean_dec(v___x_7588_);
                                        v___x_7591_ = leanh::lean_box(0);
                                        v_isShared_7592_ = v_isSharedCheck_7597_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_7571_);
                                    leanh::lean_dec(v_snd_7520_);
                                    leanh::lean_dec(v_fst_7519_);
                                    leanh::lean_dec(v_majorFVarId_7505_);
                                    v_a_7598_ = leanh::lean_ctor_get(v___x_7588_, 0);
                                    v_isSharedCheck_7605_ =
                                        (!leanh::lean_is_exclusive(v___x_7588_)) as u8;
                                    if v_isSharedCheck_7605_ == 0 {
                                        v___x_7600_ = v___x_7588_;
                                        v_isShared_7601_ = v_isSharedCheck_7605_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7598_);
                                        leanh::lean_dec(v___x_7588_);
                                        v___x_7600_ = leanh::lean_box(0);
                                        v_isShared_7601_ = v_isSharedCheck_7605_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_7571_);
                                leanh::lean_dec(v_snd_7520_);
                                leanh::lean_dec(v_fst_7519_);
                                leanh::lean_dec(v___y_7513_);
                                leanh::lean_dec_ref(v___y_7512_);
                                leanh::lean_dec(v___y_7511_);
                                leanh::lean_dec_ref(v___y_7510_);
                                leanh::lean_dec_ref(v_givenNames_7506_);
                                leanh::lean_dec(v_majorFVarId_7505_);
                                leanh::lean_dec(v_mvarId_7504_);
                                v_a_7606_ = leanh::lean_ctor_get(v___x_7586_, 0);
                                v_isSharedCheck_7613_ =
                                    (!leanh::lean_is_exclusive(v___x_7586_)) as u8;
                                if v_isSharedCheck_7613_ == 0 {
                                    v___x_7608_ = v___x_7586_;
                                    v_isShared_7609_ = v_isSharedCheck_7613_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7606_);
                                    leanh::lean_dec(v___x_7586_);
                                    v___x_7608_ = leanh::lean_box(0);
                                    v_isShared_7609_ = v_isSharedCheck_7613_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_7571_);
                        v___y_7558_ = v___y_7510_;
                        v___y_7559_ = v___y_7511_;
                        v___y_7560_ = v___y_7512_;
                        v___y_7561_ = v___y_7513_;
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v___x_7593_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(
                    v_a_7589_,
                    v_val_7571_,
                    v_majorFVarId_7505_,
                    v_fst_7519_,
                    v_snd_7520_,
                );
                leanh::lean_dec(v_snd_7520_);
                leanh::lean_dec(v_val_7571_);
                leanh::lean_dec(v_a_7589_);
                if v_isShared_7592_ == 0 {
                    leanh::lean_ctor_set(v___x_7591_, 0, v___x_7593_);
                    v___x_7595_ = v___x_7591_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7596_, 0, v___x_7593_);
                    v___x_7595_ = v_reuseFailAlloc_7596_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7595_;
            }
            11 => {
                if v_isShared_7601_ == 0 {
                    v___x_7603_ = v___x_7600_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7604_, 0, v_a_7598_);
                    v___x_7603_ = v_reuseFailAlloc_7604_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7603_;
            }
            13 => {
                if v_isShared_7609_ == 0 {
                    v___x_7611_ = v___x_7608_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7612_, 0, v_a_7606_);
                    v___x_7611_ = v_reuseFailAlloc_7612_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7611_;
            }
            15 => {
                if v_isShared_7623_ == 0 {
                    v___x_7625_ = v___x_7622_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7626_, 0, v_a_7620_);
                    v___x_7625_ = v_reuseFailAlloc_7626_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7625_;
            }
            17 => {
                if v_isShared_7631_ == 0 {
                    v___x_7633_ = v___x_7630_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7634_, 0, v_a_7628_);
                    v___x_7633_ = v_reuseFailAlloc_7634_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(
    mut v___x_7636_: *mut leanh::LeanObject,
    mut v_mvarId_7637_: *mut leanh::LeanObject,
    mut v_majorFVarId_7638_: *mut leanh::LeanObject,
    mut v_givenNames_7639_: *mut leanh::LeanObject,
    mut v_ctx_7640_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7641_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7642_: *mut leanh::LeanObject,
    mut v___y_7643_: *mut leanh::LeanObject,
    mut v___y_7644_: *mut leanh::LeanObject,
    mut v___y_7645_: *mut leanh::LeanObject,
    mut v___y_7646_: *mut leanh::LeanObject,
    mut v___y_7647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNatCasesAuxOn_boxed_7648_: u8 = 0;
    let mut v_res_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNatCasesAuxOn_boxed_7648_ = (leanh::lean_unbox(v_useNatCasesAuxOn_7641_) as u8);
    v_res_7649_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(
        v___x_7636_,
        v_mvarId_7637_,
        v_majorFVarId_7638_,
        v_givenNames_7639_,
        v_ctx_7640_,
        v_useNatCasesAuxOn_boxed_7648_,
        v_interestingCtors_x3f_7642_,
        v___y_7643_,
        v___y_7644_,
        v___y_7645_,
        v___y_7646_,
    );
    return v_res_7649_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(
    mut v_mvarId_7650_: *mut leanh::LeanObject,
    mut v_majorFVarId_7651_: *mut leanh::LeanObject,
    mut v_givenNames_7652_: *mut leanh::LeanObject,
    mut v_ctx_7653_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7654_: u8,
    mut v_interestingCtors_x3f_7655_: *mut leanh::LeanObject,
    mut v_a_7656_: *mut leanh::LeanObject,
    mut v_a_7657_: *mut leanh::LeanObject,
    mut v_a_7658_: *mut leanh::LeanObject,
    mut v_a_7659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_majorFVarId_7651_);
    v___x_7661_ = l_Lean_mkFVar(v_majorFVarId_7651_);
    v___x_7662_ = leanh::lean_box((v_useNatCasesAuxOn_7654_) as usize);
    leanh::lean_inc(v_mvarId_7650_);
    v___f_7663_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___f_7663_, 0, v___x_7661_);
    leanh::lean_closure_set(v___f_7663_, 1, v_mvarId_7650_);
    leanh::lean_closure_set(v___f_7663_, 2, v_majorFVarId_7651_);
    leanh::lean_closure_set(v___f_7663_, 3, v_givenNames_7652_);
    leanh::lean_closure_set(v___f_7663_, 4, v_ctx_7653_);
    leanh::lean_closure_set(v___f_7663_, 5, v___x_7662_);
    leanh::lean_closure_set(v___f_7663_, 6, v_interestingCtors_x3f_7655_);
    v___x_7664_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_7650_,
        v___f_7663_,
        v_a_7656_,
        v_a_7657_,
        v_a_7658_,
        v_a_7659_,
    );
    return v___x_7664_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(
    mut v_mvarId_7665_: *mut leanh::LeanObject,
    mut v_majorFVarId_7666_: *mut leanh::LeanObject,
    mut v_givenNames_7667_: *mut leanh::LeanObject,
    mut v_ctx_7668_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7669_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7670_: *mut leanh::LeanObject,
    mut v_a_7671_: *mut leanh::LeanObject,
    mut v_a_7672_: *mut leanh::LeanObject,
    mut v_a_7673_: *mut leanh::LeanObject,
    mut v_a_7674_: *mut leanh::LeanObject,
    mut v_a_7675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNatCasesAuxOn_boxed_7676_: u8 = 0;
    let mut v_res_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNatCasesAuxOn_boxed_7676_ = (leanh::lean_unbox(v_useNatCasesAuxOn_7669_) as u8);
    v_res_7677_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(
        v_mvarId_7665_,
        v_majorFVarId_7666_,
        v_givenNames_7667_,
        v_ctx_7668_,
        v_useNatCasesAuxOn_boxed_7676_,
        v_interestingCtors_x3f_7670_,
        v_a_7671_,
        v_a_7672_,
        v_a_7673_,
        v_a_7674_,
    );
    leanh::lean_dec(v_a_7674_);
    leanh::lean_dec_ref(v_a_7673_);
    leanh::lean_dec(v_a_7672_);
    leanh::lean_dec_ref(v_a_7671_);
    return v_res_7677_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0() -> f64 {
    let mut v___x_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: f64 = 0.0;
    v___x_7678_ = leanh::lean_unsigned_to_nat(0);
    v___x_7679_ = lean_float_of_nat(v___x_7678_);
    return v___x_7679_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(
    mut v_cls_7683_: *mut leanh::LeanObject,
    mut v_msg_7684_: *mut leanh::LeanObject,
    mut v___y_7685_: *mut leanh::LeanObject,
    mut v___y_7686_: *mut leanh::LeanObject,
    mut v___y_7687_: *mut leanh::LeanObject,
    mut v___y_7688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_7690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7695_: u8 = 0;
    let mut v___x_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7708_: u8 = 0;
    let mut v_tid_7709_: u64 = 0;
    let mut v_traces_7710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7713_: u8 = 0;
    let mut v___x_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: f64 = 0.0;
    let mut v___x_7716_: u8 = 0;
    let mut v___x_7717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v_isSharedCheck_7735_: u8 = 0;
    let mut v_isSharedCheck_7736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7690_ = leanh::lean_ctor_get(v___y_7687_, 5);
                v___x_7691_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_7684_, v___y_7685_, v___y_7686_, v___y_7687_, v___y_7688_);
                v_a_7692_ = leanh::lean_ctor_get(v___x_7691_, 0);
                v_isSharedCheck_7736_ = (!leanh::lean_is_exclusive(v___x_7691_)) as u8;
                if v_isSharedCheck_7736_ == 0 {
                    v___x_7694_ = v___x_7691_;
                    v_isShared_7695_ = v_isSharedCheck_7736_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7692_);
                    leanh::lean_dec(v___x_7691_);
                    v___x_7694_ = leanh::lean_box(0);
                    v_isShared_7695_ = v_isSharedCheck_7736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7696_ = lean_st_ref_take(v___y_7688_);
                v_traceState_7697_ = leanh::lean_ctor_get(v___x_7696_, 4);
                v_env_7698_ = leanh::lean_ctor_get(v___x_7696_, 0);
                v_nextMacroScope_7699_ = leanh::lean_ctor_get(v___x_7696_, 1);
                v_ngen_7700_ = leanh::lean_ctor_get(v___x_7696_, 2);
                v_auxDeclNGen_7701_ = leanh::lean_ctor_get(v___x_7696_, 3);
                v_cache_7702_ = leanh::lean_ctor_get(v___x_7696_, 5);
                v_messages_7703_ = leanh::lean_ctor_get(v___x_7696_, 6);
                v_infoState_7704_ = leanh::lean_ctor_get(v___x_7696_, 7);
                v_snapshotTasks_7705_ = leanh::lean_ctor_get(v___x_7696_, 8);
                v_isSharedCheck_7735_ = (!leanh::lean_is_exclusive(v___x_7696_)) as u8;
                if v_isSharedCheck_7735_ == 0 {
                    v___x_7707_ = v___x_7696_;
                    v_isShared_7708_ = v_isSharedCheck_7735_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7705_);
                    leanh::lean_inc(v_infoState_7704_);
                    leanh::lean_inc(v_messages_7703_);
                    leanh::lean_inc(v_cache_7702_);
                    leanh::lean_inc(v_traceState_7697_);
                    leanh::lean_inc(v_auxDeclNGen_7701_);
                    leanh::lean_inc(v_ngen_7700_);
                    leanh::lean_inc(v_nextMacroScope_7699_);
                    leanh::lean_inc(v_env_7698_);
                    leanh::lean_dec(v___x_7696_);
                    v___x_7707_ = leanh::lean_box(0);
                    v_isShared_7708_ = v_isSharedCheck_7735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_7709_ = leanh::lean_ctor_get_uint64(
                    v_traceState_7697_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_7710_ = leanh::lean_ctor_get(v_traceState_7697_, 0);
                v_isSharedCheck_7734_ =
                    (!leanh::lean_is_exclusive(v_traceState_7697_)) as u8;
                if v_isSharedCheck_7734_ == 0 {
                    v___x_7712_ = v_traceState_7697_;
                    v_isShared_7713_ = v_isSharedCheck_7734_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_7710_);
                    leanh::lean_dec(v_traceState_7697_);
                    v___x_7712_ = leanh::lean_box(0);
                    v_isShared_7713_ = v_isSharedCheck_7734_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7714_ = leanh::lean_box(0);
                v___x_7715_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0,
                );
                v___x_7716_ = 0;
                v___x_7717_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1;
                v___x_7718_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_7718_, 0, v_cls_7683_);
                leanh::lean_ctor_set(v___x_7718_, 1, v___x_7714_);
                leanh::lean_ctor_set(v___x_7718_, 2, v___x_7717_);
                leanh::lean_ctor_set_float(
                    v___x_7718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_7715_,
                );
                leanh::lean_ctor_set_float(
                    v___x_7718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_7715_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_7716_,
                );
                v___x_7719_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2;
                v___x_7720_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7720_, 0, v___x_7718_);
                leanh::lean_ctor_set(v___x_7720_, 1, v_a_7692_);
                leanh::lean_ctor_set(v___x_7720_, 2, v___x_7719_);
                leanh::lean_inc(v_ref_7690_);
                v___x_7721_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7721_, 0, v_ref_7690_);
                leanh::lean_ctor_set(v___x_7721_, 1, v___x_7720_);
                v___x_7722_ = l_Lean_PersistentArray_push___redArg(v_traces_7710_, v___x_7721_);
                if v_isShared_7713_ == 0 {
                    leanh::lean_ctor_set(v___x_7712_, 0, v___x_7722_);
                    v___x_7724_ = v___x_7712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7733_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7733_, 0, v___x_7722_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7733_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_7709_,
                    );
                    v___x_7724_ = v_reuseFailAlloc_7733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7708_ == 0 {
                    leanh::lean_ctor_set(v___x_7707_, 4, v___x_7724_);
                    v___x_7726_ = v___x_7707_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7732_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 0, v_env_7698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 1, v_nextMacroScope_7699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 2, v_ngen_7700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 3, v_auxDeclNGen_7701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 4, v___x_7724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 5, v_cache_7702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 6, v_messages_7703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 7, v_infoState_7704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 8, v_snapshotTasks_7705_);
                    v___x_7726_ = v_reuseFailAlloc_7732_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7727_ = lean_st_ref_set(v___y_7688_, v___x_7726_);
                v___x_7728_ = leanh::lean_box(0);
                if v_isShared_7695_ == 0 {
                    leanh::lean_ctor_set(v___x_7694_, 0, v___x_7728_);
                    v___x_7730_ = v___x_7694_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v___x_7728_);
                    v___x_7730_ = v_reuseFailAlloc_7731_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(
    mut v_cls_7737_: *mut leanh::LeanObject,
    mut v_msg_7738_: *mut leanh::LeanObject,
    mut v___y_7739_: *mut leanh::LeanObject,
    mut v___y_7740_: *mut leanh::LeanObject,
    mut v___y_7741_: *mut leanh::LeanObject,
    mut v___y_7742_: *mut leanh::LeanObject,
    mut v___y_7743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7744_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(
        v_cls_7737_,
        v_msg_7738_,
        v___y_7739_,
        v___y_7740_,
        v___y_7741_,
        v___y_7742_,
    );
    leanh::lean_dec(v___y_7742_);
    leanh::lean_dec_ref(v___y_7741_);
    leanh::lean_dec(v___y_7740_);
    leanh::lean_dec_ref(v___y_7739_);
    return v_res_7744_;
}
pub unsafe fn _init_l_Lean_Meta_Cases_cases___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7748_ = l_Lean_Meta_Cases_cases___lam__0___closed__1;
    v___x_7749_ = l_Lean_MessageData_ofFormat(v___x_7748_);
    return v___x_7749_;
}
pub unsafe fn _init_l_Lean_Meta_Cases_cases___lam__0___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_7750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7750_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Cases_cases___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Cases_cases___lam__0___closed__2_once),
        _init_l_Lean_Meta_Cases_cases___lam__0___closed__2,
    );
    v___x_7751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7751_, 0, v___x_7750_);
    return v___x_7751_;
}
pub unsafe fn _init_l_Lean_Meta_Cases_cases___lam__0___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7758_ = l_Lean_Meta_Cases_cases___lam__0___closed__8;
    v___x_7759_ = l_Lean_stringToMessageData(v___x_7758_);
    return v___x_7759_;
}
pub unsafe fn l_Lean_Meta_Cases_cases___lam__0(
    mut v_mvarId_7760_: *mut leanh::LeanObject,
    mut v___x_7761_: *mut leanh::LeanObject,
    mut v_majorFVarId_7762_: *mut leanh::LeanObject,
    mut v_givenNames_7763_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7764_: *mut leanh::LeanObject,
    mut v___x_7765_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7766_: u8,
    mut v___y_7767_: *mut leanh::LeanObject,
    mut v___y_7768_: *mut leanh::LeanObject,
    mut v___y_7769_: *mut leanh::LeanObject,
    mut v___y_7770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: u8 = 0;
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEqs_7793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: u8 = 0;
    let mut v___x_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7801_: u8 = 0;
    let mut v_inheritedTraceOptions_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: u8 = 0;
    let mut v_mvarId_7809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7818_: u8 = 0;
    let mut v___x_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7822_: u8 = 0;
    let mut v_reuseFailAlloc_7823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v___x_7829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7831_: u8 = 0;
    let mut v___x_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7836_: u8 = 0;
    let mut v___x_7838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7840_: u8 = 0;
    let mut v_isSharedCheck_7841_: u8 = 0;
    let mut v_a_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7845_: u8 = 0;
    let mut v___x_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7849_: u8 = 0;
    let mut v_a_7850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7853_: u8 = 0;
    let mut v___x_7855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_7761_);
                leanh::lean_inc(v_mvarId_7760_);
                v___x_7772_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7760_,
                    v___x_7761_,
                    v___y_7767_,
                    v___y_7768_,
                    v___y_7769_,
                    v___y_7770_,
                );
                if leanh::lean_obj_tag(v___x_7772_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7772_, 1);
                    leanh::lean_inc(v_majorFVarId_7762_);
                    v___x_7773_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(
                            v_majorFVarId_7762_,
                            v___y_7767_,
                            v___y_7768_,
                            v___y_7769_,
                            v___y_7770_,
                        );
                    if leanh::lean_obj_tag(v___x_7773_) == 0 {
                        v_a_7774_ = leanh::lean_ctor_get(v___x_7773_, 0);
                        leanh::lean_inc(v_a_7774_);
                        leanh::lean_dec_ref_known(v___x_7773_, 1);
                        if leanh::lean_obj_tag(v_a_7774_) == 0 {
                            leanh::lean_dec_ref(v___x_7765_);
                            leanh::lean_dec(v_interestingCtors_x3f_7764_);
                            leanh::lean_dec_ref(v_givenNames_7763_);
                            leanh::lean_dec(v_majorFVarId_7762_);
                            v___x_7775_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Cases_cases___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Cases_cases___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_Cases_cases___lam__0___closed__3,
                            );
                            v___x_7776_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_7761_,
                                v_mvarId_7760_,
                                v___x_7775_,
                                v___y_7767_,
                                v___y_7768_,
                                v___y_7769_,
                                v___y_7770_,
                            );
                            return v___x_7776_;
                        } else {
                            leanh::lean_dec(v___x_7761_);
                            v_val_7777_ = leanh::lean_ctor_get(v_a_7774_, 0);
                            v_isSharedCheck_7841_ =
                                (!leanh::lean_is_exclusive(v_a_7774_)) as u8;
                            if v_isSharedCheck_7841_ == 0 {
                                v___x_7779_ = v_a_7774_;
                                v_isShared_7780_ = v_isSharedCheck_7841_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_7777_);
                                leanh::lean_dec(v_a_7774_);
                                v___x_7779_ = leanh::lean_box(0);
                                v_isShared_7780_ = v_isSharedCheck_7841_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7765_);
                        leanh::lean_dec(v_interestingCtors_x3f_7764_);
                        leanh::lean_dec_ref(v_givenNames_7763_);
                        leanh::lean_dec(v_majorFVarId_7762_);
                        leanh::lean_dec(v___x_7761_);
                        leanh::lean_dec(v_mvarId_7760_);
                        v_a_7842_ = leanh::lean_ctor_get(v___x_7773_, 0);
                        v_isSharedCheck_7849_ =
                            (!leanh::lean_is_exclusive(v___x_7773_)) as u8;
                        if v_isSharedCheck_7849_ == 0 {
                            v___x_7844_ = v___x_7773_;
                            v_isShared_7845_ = v_isSharedCheck_7849_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7842_);
                            leanh::lean_dec(v___x_7773_);
                            v___x_7844_ = leanh::lean_box(0);
                            v_isShared_7845_ = v_isSharedCheck_7849_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_7765_);
                    leanh::lean_dec(v_interestingCtors_x3f_7764_);
                    leanh::lean_dec_ref(v_givenNames_7763_);
                    leanh::lean_dec(v_majorFVarId_7762_);
                    leanh::lean_dec(v___x_7761_);
                    leanh::lean_dec(v_mvarId_7760_);
                    v_a_7850_ = leanh::lean_ctor_get(v___x_7772_, 0);
                    v_isSharedCheck_7857_ = (!leanh::lean_is_exclusive(v___x_7772_)) as u8;
                    if v_isSharedCheck_7857_ == 0 {
                        v___x_7852_ = v___x_7772_;
                        v_isShared_7853_ = v_isSharedCheck_7857_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7850_);
                        leanh::lean_dec(v___x_7772_);
                        v___x_7852_ = leanh::lean_box(0);
                        v_isShared_7853_ = v_isSharedCheck_7857_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_7777_);
                v___x_7781_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(
                    v_val_7777_,
                    v___y_7767_,
                    v___y_7768_,
                    v___y_7769_,
                    v___y_7770_,
                );
                if leanh::lean_obj_tag(v___x_7781_) == 0 {
                    v_a_7782_ = leanh::lean_ctor_get(v___x_7781_, 0);
                    leanh::lean_inc(v_a_7782_);
                    leanh::lean_dec_ref_known(v___x_7781_, 1);
                    v___x_7783_ = (leanh::lean_unbox(v_a_7782_) as u8);
                    if v___x_7783_ == 0 {
                        v___x_7784_ = l_Lean_Meta_generalizeIndices(
                            v_mvarId_7760_,
                            v_majorFVarId_7762_,
                            v___y_7767_,
                            v___y_7768_,
                            v___y_7769_,
                            v___y_7770_,
                        );
                        if leanh::lean_obj_tag(v___x_7784_) == 0 {
                            v_a_7785_ = leanh::lean_ctor_get(v___x_7784_, 0);
                            leanh::lean_inc(v_a_7785_);
                            leanh::lean_dec_ref_known(v___x_7784_, 1);
                            v_options_7800_ = leanh::lean_ctor_get(v___y_7769_, 2);
                            v_hasTrace_7801_ = leanh::lean_ctor_get_uint8(
                                v_options_7800_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_7801_ == 0 {
                                leanh::lean_del_object(v___x_7779_);
                                leanh::lean_dec_ref(v___x_7765_);
                                v___y_7787_ = v___y_7767_;
                                v___y_7788_ = v___y_7768_;
                                v___y_7789_ = v___y_7769_;
                                v___y_7790_ = v___y_7770_;
                                state = 2;
                                continue;
                            } else {
                                v_inheritedTraceOptions_7802_ =
                                    leanh::lean_ctor_get(v___y_7769_, 13);
                                v___x_7803_ = l_Lean_Meta_Cases_cases___lam__0___closed__4;
                                v___x_7804_ = l_Lean_Meta_Cases_cases___lam__0___closed__5;
                                v___x_7805_ =
                                    l_Lean_Name_mkStr3(v___x_7803_, v___x_7804_, v___x_7765_);
                                v___x_7806_ = l_Lean_Meta_Cases_cases___lam__0___closed__7;
                                leanh::lean_inc(v___x_7805_);
                                v___x_7807_ = l_Lean_Name_append(v___x_7806_, v___x_7805_);
                                v___x_7808_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_7802_,
                                        v_options_7800_,
                                        v___x_7807_,
                                    );
                                leanh::lean_dec(v___x_7807_);
                                if v___x_7808_ == 0 {
                                    leanh::lean_dec(v___x_7805_);
                                    leanh::lean_del_object(v___x_7779_);
                                    v___y_7787_ = v___y_7767_;
                                    v___y_7788_ = v___y_7768_;
                                    v___y_7789_ = v___y_7769_;
                                    v___y_7790_ = v___y_7770_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_mvarId_7809_ = leanh::lean_ctor_get(v_a_7785_, 0);
                                    v___x_7810_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Cases_cases___lam__0___closed__9
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Cases_cases___lam__0___closed__9_once
                                        ),
                                        _init_l_Lean_Meta_Cases_cases___lam__0___closed__9,
                                    );
                                    leanh::lean_inc(v_mvarId_7809_);
                                    if v_isShared_7780_ == 0 {
                                        leanh::lean_ctor_set(v___x_7779_, 0, v_mvarId_7809_);
                                        v___x_7812_ = v___x_7779_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7823_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7823_,
                                            0,
                                            v_mvarId_7809_,
                                        );
                                        v___x_7812_ = v_reuseFailAlloc_7823_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_7782_);
                            leanh::lean_del_object(v___x_7779_);
                            leanh::lean_dec(v_val_7777_);
                            leanh::lean_dec_ref(v___x_7765_);
                            leanh::lean_dec(v_interestingCtors_x3f_7764_);
                            leanh::lean_dec_ref(v_givenNames_7763_);
                            v_a_7824_ = leanh::lean_ctor_get(v___x_7784_, 0);
                            v_isSharedCheck_7831_ =
                                (!leanh::lean_is_exclusive(v___x_7784_)) as u8;
                            if v_isSharedCheck_7831_ == 0 {
                                v___x_7826_ = v___x_7784_;
                                v_isShared_7827_ = v_isSharedCheck_7831_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7824_);
                                leanh::lean_dec(v___x_7784_);
                                v___x_7826_ = leanh::lean_box(0);
                                v_isShared_7827_ = v_isSharedCheck_7831_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_7782_);
                        leanh::lean_del_object(v___x_7779_);
                        leanh::lean_dec_ref(v___x_7765_);
                        v___x_7832_ =
                            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(
                                v_mvarId_7760_,
                                v_majorFVarId_7762_,
                                v_givenNames_7763_,
                                v_val_7777_,
                                v_useNatCasesAuxOn_7766_,
                                v_interestingCtors_x3f_7764_,
                                v___y_7767_,
                                v___y_7768_,
                                v___y_7769_,
                                v___y_7770_,
                            );
                        return v___x_7832_;
                    }
                } else {
                    leanh::lean_del_object(v___x_7779_);
                    leanh::lean_dec(v_val_7777_);
                    leanh::lean_dec_ref(v___x_7765_);
                    leanh::lean_dec(v_interestingCtors_x3f_7764_);
                    leanh::lean_dec_ref(v_givenNames_7763_);
                    leanh::lean_dec(v_majorFVarId_7762_);
                    leanh::lean_dec(v_mvarId_7760_);
                    v_a_7833_ = leanh::lean_ctor_get(v___x_7781_, 0);
                    v_isSharedCheck_7840_ = (!leanh::lean_is_exclusive(v___x_7781_)) as u8;
                    if v_isSharedCheck_7840_ == 0 {
                        v___x_7835_ = v___x_7781_;
                        v_isShared_7836_ = v_isSharedCheck_7840_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7833_);
                        leanh::lean_dec(v___x_7781_);
                        v___x_7835_ = leanh::lean_box(0);
                        v_isShared_7836_ = v_isSharedCheck_7840_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_mvarId_7791_ = leanh::lean_ctor_get(v_a_7785_, 0);
                v_fvarId_7792_ = leanh::lean_ctor_get(v_a_7785_, 2);
                v_numEqs_7793_ = leanh::lean_ctor_get(v_a_7785_, 3);
                leanh::lean_inc(v_numEqs_7793_);
                v___x_7794_ = (leanh::lean_unbox(v_a_7782_) as u8);
                leanh::lean_dec(v_a_7782_);
                leanh::lean_inc(v_fvarId_7792_);
                leanh::lean_inc(v_mvarId_7791_);
                v___x_7795_ =
                    l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(
                        v_mvarId_7791_,
                        v_fvarId_7792_,
                        v_givenNames_7763_,
                        v_val_7777_,
                        v___x_7794_,
                        v_interestingCtors_x3f_7764_,
                        v___y_7787_,
                        v___y_7788_,
                        v___y_7789_,
                        v___y_7790_,
                    );
                if leanh::lean_obj_tag(v___x_7795_) == 0 {
                    v_a_7796_ = leanh::lean_ctor_get(v___x_7795_, 0);
                    leanh::lean_inc(v_a_7796_);
                    leanh::lean_dec_ref_known(v___x_7795_, 1);
                    v___x_7797_ =
                        l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(
                            v_a_7785_,
                            v_a_7796_,
                            v___y_7787_,
                            v___y_7788_,
                            v___y_7789_,
                            v___y_7790_,
                        );
                    leanh::lean_dec(v_a_7785_);
                    if leanh::lean_obj_tag(v___x_7797_) == 0 {
                        v_a_7798_ = leanh::lean_ctor_get(v___x_7797_, 0);
                        leanh::lean_inc(v_a_7798_);
                        leanh::lean_dec_ref_known(v___x_7797_, 1);
                        v___x_7799_ =
                            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(
                                v_numEqs_7793_,
                                v_a_7798_,
                                v___y_7787_,
                                v___y_7788_,
                                v___y_7789_,
                                v___y_7790_,
                            );
                        leanh::lean_dec(v_a_7798_);
                        return v___x_7799_;
                    } else {
                        leanh::lean_dec(v_numEqs_7793_);
                        return v___x_7797_;
                    }
                } else {
                    leanh::lean_dec(v_numEqs_7793_);
                    leanh::lean_dec(v_a_7785_);
                    return v___x_7795_;
                }
            }
            3 => {
                v___x_7813_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7813_, 0, v___x_7810_);
                leanh::lean_ctor_set(v___x_7813_, 1, v___x_7812_);
                v___x_7814_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(
                    v___x_7805_,
                    v___x_7813_,
                    v___y_7767_,
                    v___y_7768_,
                    v___y_7769_,
                    v___y_7770_,
                );
                if leanh::lean_obj_tag(v___x_7814_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7814_, 1);
                    v___y_7787_ = v___y_7767_;
                    v___y_7788_ = v___y_7768_;
                    v___y_7789_ = v___y_7769_;
                    v___y_7790_ = v___y_7770_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7785_);
                    leanh::lean_dec(v_a_7782_);
                    leanh::lean_dec(v_val_7777_);
                    leanh::lean_dec(v_interestingCtors_x3f_7764_);
                    leanh::lean_dec_ref(v_givenNames_7763_);
                    v_a_7815_ = leanh::lean_ctor_get(v___x_7814_, 0);
                    v_isSharedCheck_7822_ = (!leanh::lean_is_exclusive(v___x_7814_)) as u8;
                    if v_isSharedCheck_7822_ == 0 {
                        v___x_7817_ = v___x_7814_;
                        v_isShared_7818_ = v_isSharedCheck_7822_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7815_);
                        leanh::lean_dec(v___x_7814_);
                        v___x_7817_ = leanh::lean_box(0);
                        v_isShared_7818_ = v_isSharedCheck_7822_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7818_ == 0 {
                    v___x_7820_ = v___x_7817_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7821_, 0, v_a_7815_);
                    v___x_7820_ = v_reuseFailAlloc_7821_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7820_;
            }
            6 => {
                if v_isShared_7827_ == 0 {
                    v___x_7829_ = v___x_7826_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7830_, 0, v_a_7824_);
                    v___x_7829_ = v_reuseFailAlloc_7830_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7829_;
            }
            8 => {
                if v_isShared_7836_ == 0 {
                    v___x_7838_ = v___x_7835_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7839_, 0, v_a_7833_);
                    v___x_7838_ = v_reuseFailAlloc_7839_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7838_;
            }
            10 => {
                if v_isShared_7845_ == 0 {
                    v___x_7847_ = v___x_7844_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_a_7842_);
                    v___x_7847_ = v_reuseFailAlloc_7848_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7847_;
            }
            12 => {
                if v_isShared_7853_ == 0 {
                    v___x_7855_ = v___x_7852_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7856_, 0, v_a_7850_);
                    v___x_7855_ = v_reuseFailAlloc_7856_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Cases_cases___lam__0___boxed(
    mut v_mvarId_7858_: *mut leanh::LeanObject,
    mut v___x_7859_: *mut leanh::LeanObject,
    mut v_majorFVarId_7860_: *mut leanh::LeanObject,
    mut v_givenNames_7861_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7862_: *mut leanh::LeanObject,
    mut v___x_7863_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7864_: *mut leanh::LeanObject,
    mut v___y_7865_: *mut leanh::LeanObject,
    mut v___y_7866_: *mut leanh::LeanObject,
    mut v___y_7867_: *mut leanh::LeanObject,
    mut v___y_7868_: *mut leanh::LeanObject,
    mut v___y_7869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNatCasesAuxOn_boxed_7870_: u8 = 0;
    let mut v_res_7871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNatCasesAuxOn_boxed_7870_ = (leanh::lean_unbox(v_useNatCasesAuxOn_7864_) as u8);
    v_res_7871_ = l_Lean_Meta_Cases_cases___lam__0(
        v_mvarId_7858_,
        v___x_7859_,
        v_majorFVarId_7860_,
        v_givenNames_7861_,
        v_interestingCtors_x3f_7862_,
        v___x_7863_,
        v_useNatCasesAuxOn_boxed_7870_,
        v___y_7865_,
        v___y_7866_,
        v___y_7867_,
        v___y_7868_,
    );
    leanh::lean_dec(v___y_7868_);
    leanh::lean_dec_ref(v___y_7867_);
    leanh::lean_dec(v___y_7866_);
    leanh::lean_dec_ref(v___y_7865_);
    return v_res_7871_;
}
pub unsafe fn l_Lean_Meta_Cases_cases(
    mut v_mvarId_7875_: *mut leanh::LeanObject,
    mut v_majorFVarId_7876_: *mut leanh::LeanObject,
    mut v_givenNames_7877_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7878_: u8,
    mut v_interestingCtors_x3f_7879_: *mut leanh::LeanObject,
    mut v_a_7880_: *mut leanh::LeanObject,
    mut v_a_7881_: *mut leanh::LeanObject,
    mut v_a_7882_: *mut leanh::LeanObject,
    mut v_a_7883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7892_: u8 = 0;
    let mut v___x_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: u8 = 0;
    let mut v___x_7895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7885_ = l_Lean_Meta_Cases_cases___closed__0;
                v___x_7886_ = l_Lean_Meta_Cases_cases___closed__1;
                v___x_7887_ = leanh::lean_box((v_useNatCasesAuxOn_7878_) as usize);
                leanh::lean_inc(v_mvarId_7875_);
                v___f_7888_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Cases_cases___lam__0___boxed as *mut core::ffi::c_void,
                    12,
                    7,
                );
                leanh::lean_closure_set(v___f_7888_, 0, v_mvarId_7875_);
                leanh::lean_closure_set(v___f_7888_, 1, v___x_7886_);
                leanh::lean_closure_set(v___f_7888_, 2, v_majorFVarId_7876_);
                leanh::lean_closure_set(v___f_7888_, 3, v_givenNames_7877_);
                leanh::lean_closure_set(v___f_7888_, 4, v_interestingCtors_x3f_7879_);
                leanh::lean_closure_set(v___f_7888_, 5, v___x_7885_);
                leanh::lean_closure_set(v___f_7888_, 6, v___x_7887_);
                v___x_7889_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_7875_, v___f_7888_, v_a_7880_, v_a_7881_, v_a_7882_, v_a_7883_);
                if leanh::lean_obj_tag(v___x_7889_) == 0 {
                    return v___x_7889_;
                } else {
                    v_a_7890_ = leanh::lean_ctor_get(v___x_7889_, 0);
                    leanh::lean_inc(v_a_7890_);
                    v___x_7894_ = l_Lean_Exception_isInterrupt(v_a_7890_);
                    if v___x_7894_ == 0 {
                        leanh::lean_inc(v_a_7890_);
                        v___x_7895_ = l_Lean_Exception_isRuntime(v_a_7890_);
                        v___y_7892_ = v___x_7895_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7892_ = v___x_7894_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7892_ == 0 {
                    leanh::lean_dec_ref_known(v___x_7889_, 1);
                    v___x_7893_ = l_Lean_Meta_throwNestedTacticEx___redArg(
                        v___x_7886_,
                        v_a_7890_,
                        v_a_7880_,
                        v_a_7881_,
                        v_a_7882_,
                        v_a_7883_,
                    );
                    return v___x_7893_;
                } else {
                    leanh::lean_dec(v_a_7890_);
                    return v___x_7889_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Cases_cases___boxed(
    mut v_mvarId_7896_: *mut leanh::LeanObject,
    mut v_majorFVarId_7897_: *mut leanh::LeanObject,
    mut v_givenNames_7898_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7899_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7900_: *mut leanh::LeanObject,
    mut v_a_7901_: *mut leanh::LeanObject,
    mut v_a_7902_: *mut leanh::LeanObject,
    mut v_a_7903_: *mut leanh::LeanObject,
    mut v_a_7904_: *mut leanh::LeanObject,
    mut v_a_7905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNatCasesAuxOn_boxed_7906_: u8 = 0;
    let mut v_res_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNatCasesAuxOn_boxed_7906_ = (leanh::lean_unbox(v_useNatCasesAuxOn_7899_) as u8);
    v_res_7907_ = l_Lean_Meta_Cases_cases(
        v_mvarId_7896_,
        v_majorFVarId_7897_,
        v_givenNames_7898_,
        v_useNatCasesAuxOn_boxed_7906_,
        v_interestingCtors_x3f_7900_,
        v_a_7901_,
        v_a_7902_,
        v_a_7903_,
        v_a_7904_,
    );
    leanh::lean_dec(v_a_7904_);
    leanh::lean_dec_ref(v_a_7903_);
    leanh::lean_dec(v_a_7902_);
    leanh::lean_dec_ref(v_a_7901_);
    return v_res_7907_;
}
pub unsafe fn l_Lean_MVarId_cases(
    mut v_mvarId_7908_: *mut leanh::LeanObject,
    mut v_majorFVarId_7909_: *mut leanh::LeanObject,
    mut v_givenNames_7910_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7911_: u8,
    mut v_interestingCtors_x3f_7912_: *mut leanh::LeanObject,
    mut v_a_7913_: *mut leanh::LeanObject,
    mut v_a_7914_: *mut leanh::LeanObject,
    mut v_a_7915_: *mut leanh::LeanObject,
    mut v_a_7916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7918_ = l_Lean_Meta_Cases_cases(
        v_mvarId_7908_,
        v_majorFVarId_7909_,
        v_givenNames_7910_,
        v_useNatCasesAuxOn_7911_,
        v_interestingCtors_x3f_7912_,
        v_a_7913_,
        v_a_7914_,
        v_a_7915_,
        v_a_7916_,
    );
    return v___x_7918_;
}
pub unsafe fn l_Lean_MVarId_cases___boxed(
    mut v_mvarId_7919_: *mut leanh::LeanObject,
    mut v_majorFVarId_7920_: *mut leanh::LeanObject,
    mut v_givenNames_7921_: *mut leanh::LeanObject,
    mut v_useNatCasesAuxOn_7922_: *mut leanh::LeanObject,
    mut v_interestingCtors_x3f_7923_: *mut leanh::LeanObject,
    mut v_a_7924_: *mut leanh::LeanObject,
    mut v_a_7925_: *mut leanh::LeanObject,
    mut v_a_7926_: *mut leanh::LeanObject,
    mut v_a_7927_: *mut leanh::LeanObject,
    mut v_a_7928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNatCasesAuxOn_boxed_7929_: u8 = 0;
    let mut v_res_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNatCasesAuxOn_boxed_7929_ = (leanh::lean_unbox(v_useNatCasesAuxOn_7922_) as u8);
    v_res_7930_ = l_Lean_MVarId_cases(
        v_mvarId_7919_,
        v_majorFVarId_7920_,
        v_givenNames_7921_,
        v_useNatCasesAuxOn_boxed_7929_,
        v_interestingCtors_x3f_7923_,
        v_a_7924_,
        v_a_7925_,
        v_a_7926_,
        v_a_7927_,
    );
    leanh::lean_dec(v_a_7927_);
    leanh::lean_dec_ref(v_a_7926_);
    leanh::lean_dec(v_a_7925_);
    leanh::lean_dec_ref(v_a_7924_);
    return v_res_7930_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
    mut v_x_7931_: *mut leanh::LeanObject,
    mut v___y_7932_: *mut leanh::LeanObject,
    mut v___y_7933_: *mut leanh::LeanObject,
    mut v___y_7934_: *mut leanh::LeanObject,
    mut v___y_7935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7943_: u8 = 0;
    let mut v___x_7944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7948_: u8 = 0;
    let mut v_a_7949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7952_: u8 = 0;
    let mut v___y_7954_: u8 = 0;
    let mut v___x_7955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7958_: u8 = 0;
    let mut v___x_7959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7963_: u8 = 0;
    let mut v_unused_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7968_: u8 = 0;
    let mut v___x_7970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7972_: u8 = 0;
    let mut v___x_7974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: u8 = 0;
    let mut v___x_7977_: u8 = 0;
    let mut v_isSharedCheck_7978_: u8 = 0;
    let mut v_a_7979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7982_: u8 = 0;
    let mut v___x_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7937_ = l_Lean_Meta_saveState___redArg(v___y_7933_, v___y_7935_);
                if leanh::lean_obj_tag(v___x_7937_) == 0 {
                    v_a_7938_ = leanh::lean_ctor_get(v___x_7937_, 0);
                    leanh::lean_inc(v_a_7938_);
                    leanh::lean_dec_ref_known(v___x_7937_, 1);
                    leanh::lean_inc(v___y_7935_);
                    leanh::lean_inc_ref(v___y_7934_);
                    leanh::lean_inc(v___y_7933_);
                    leanh::lean_inc_ref(v___y_7932_);
                    v___x_7939_ = leanh::lean_apply_5(
                        v_x_7931_,
                        v___y_7932_,
                        v___y_7933_,
                        v___y_7934_,
                        v___y_7935_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7939_) == 0 {
                        leanh::lean_dec(v_a_7938_);
                        v_a_7940_ = leanh::lean_ctor_get(v___x_7939_, 0);
                        v_isSharedCheck_7948_ =
                            (!leanh::lean_is_exclusive(v___x_7939_)) as u8;
                        if v_isSharedCheck_7948_ == 0 {
                            v___x_7942_ = v___x_7939_;
                            v_isShared_7943_ = v_isSharedCheck_7948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7940_);
                            leanh::lean_dec(v___x_7939_);
                            v___x_7942_ = leanh::lean_box(0);
                            v_isShared_7943_ = v_isSharedCheck_7948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7949_ = leanh::lean_ctor_get(v___x_7939_, 0);
                        v_isSharedCheck_7978_ =
                            (!leanh::lean_is_exclusive(v___x_7939_)) as u8;
                        if v_isSharedCheck_7978_ == 0 {
                            v___x_7951_ = v___x_7939_;
                            v_isShared_7952_ = v_isSharedCheck_7978_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7949_);
                            leanh::lean_dec(v___x_7939_);
                            v___x_7951_ = leanh::lean_box(0);
                            v_isShared_7952_ = v_isSharedCheck_7978_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_7931_);
                    v_a_7979_ = leanh::lean_ctor_get(v___x_7937_, 0);
                    v_isSharedCheck_7986_ = (!leanh::lean_is_exclusive(v___x_7937_)) as u8;
                    if v_isSharedCheck_7986_ == 0 {
                        v___x_7981_ = v___x_7937_;
                        v_isShared_7982_ = v_isSharedCheck_7986_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7979_);
                        leanh::lean_dec(v___x_7937_);
                        v___x_7981_ = leanh::lean_box(0);
                        v_isShared_7982_ = v_isSharedCheck_7986_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7944_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7944_, 0, v_a_7940_);
                if v_isShared_7943_ == 0 {
                    leanh::lean_ctor_set(v___x_7942_, 0, v___x_7944_);
                    v___x_7946_ = v___x_7942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7947_, 0, v___x_7944_);
                    v___x_7946_ = v_reuseFailAlloc_7947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7946_;
            }
            3 => {
                v___x_7976_ = l_Lean_Exception_isInterrupt(v_a_7949_);
                if v___x_7976_ == 0 {
                    leanh::lean_inc(v_a_7949_);
                    v___x_7977_ = l_Lean_Exception_isRuntime(v_a_7949_);
                    v___y_7954_ = v___x_7977_;
                    state = 4;
                    continue;
                } else {
                    v___y_7954_ = v___x_7976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_7954_ == 0 {
                    leanh::lean_del_object(v___x_7951_);
                    leanh::lean_dec(v_a_7949_);
                    v___x_7955_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_7938_,
                        v___y_7933_,
                        v___y_7935_,
                    );
                    leanh::lean_dec(v_a_7938_);
                    if leanh::lean_obj_tag(v___x_7955_) == 0 {
                        v_isSharedCheck_7963_ =
                            (!leanh::lean_is_exclusive(v___x_7955_)) as u8;
                        if v_isSharedCheck_7963_ == 0 {
                            v_unused_7964_ = leanh::lean_ctor_get(v___x_7955_, 0);
                            leanh::lean_dec(v_unused_7964_);
                            v___x_7957_ = v___x_7955_;
                            v_isShared_7958_ = v_isSharedCheck_7963_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_7955_);
                            v___x_7957_ = leanh::lean_box(0);
                            v_isShared_7958_ = v_isSharedCheck_7963_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_7965_ = leanh::lean_ctor_get(v___x_7955_, 0);
                        v_isSharedCheck_7972_ =
                            (!leanh::lean_is_exclusive(v___x_7955_)) as u8;
                        if v_isSharedCheck_7972_ == 0 {
                            v___x_7967_ = v___x_7955_;
                            v_isShared_7968_ = v_isSharedCheck_7972_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7965_);
                            leanh::lean_dec(v___x_7955_);
                            v___x_7967_ = leanh::lean_box(0);
                            v_isShared_7968_ = v_isSharedCheck_7972_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_7938_);
                    if v_isShared_7952_ == 0 {
                        v___x_7974_ = v___x_7951_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_7975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7975_, 0, v_a_7949_);
                        v___x_7974_ = v_reuseFailAlloc_7975_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_7959_ = leanh::lean_box(0);
                if v_isShared_7958_ == 0 {
                    leanh::lean_ctor_set(v___x_7957_, 0, v___x_7959_);
                    v___x_7961_ = v___x_7957_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7962_, 0, v___x_7959_);
                    v___x_7961_ = v_reuseFailAlloc_7962_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7961_;
            }
            7 => {
                if v_isShared_7968_ == 0 {
                    v___x_7970_ = v___x_7967_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7971_, 0, v_a_7965_);
                    v___x_7970_ = v_reuseFailAlloc_7971_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7970_;
            }
            9 => {
                return v___x_7974_;
            }
            10 => {
                if v_isShared_7982_ == 0 {
                    v___x_7984_ = v___x_7981_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7985_, 0, v_a_7979_);
                    v___x_7984_ = v_reuseFailAlloc_7985_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(
    mut v_x_7987_: *mut leanh::LeanObject,
    mut v___y_7988_: *mut leanh::LeanObject,
    mut v___y_7989_: *mut leanh::LeanObject,
    mut v___y_7990_: *mut leanh::LeanObject,
    mut v___y_7991_: *mut leanh::LeanObject,
    mut v___y_7992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7993_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
        v_x_7987_,
        v___y_7988_,
        v___y_7989_,
        v___y_7990_,
        v___y_7991_,
    );
    leanh::lean_dec(v___y_7991_);
    leanh::lean_dec_ref(v___y_7990_);
    leanh::lean_dec(v___y_7989_);
    leanh::lean_dec_ref(v___y_7988_);
    return v_res_7993_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(
    mut v_00_u03b1_7994_: *mut leanh::LeanObject,
    mut v_x_7995_: *mut leanh::LeanObject,
    mut v___y_7996_: *mut leanh::LeanObject,
    mut v___y_7997_: *mut leanh::LeanObject,
    mut v___y_7998_: *mut leanh::LeanObject,
    mut v___y_7999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8001_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
        v_x_7995_,
        v___y_7996_,
        v___y_7997_,
        v___y_7998_,
        v___y_7999_,
    );
    return v___x_8001_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(
    mut v_00_u03b1_8002_: *mut leanh::LeanObject,
    mut v_x_8003_: *mut leanh::LeanObject,
    mut v___y_8004_: *mut leanh::LeanObject,
    mut v___y_8005_: *mut leanh::LeanObject,
    mut v___y_8006_: *mut leanh::LeanObject,
    mut v___y_8007_: *mut leanh::LeanObject,
    mut v___y_8008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8009_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(
        v_00_u03b1_8002_,
        v_x_8003_,
        v___y_8004_,
        v___y_8005_,
        v___y_8006_,
        v___y_8007_,
    );
    leanh::lean_dec(v___y_8007_);
    leanh::lean_dec_ref(v___y_8006_);
    leanh::lean_dec(v___y_8005_);
    leanh::lean_dec_ref(v___y_8004_);
    return v_res_8009_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(
    mut v_a_8010_: *mut leanh::LeanObject,
    mut v_a_8011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8018_: u8 = 0;
    let mut v_mvarId_8019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8024_: u8 = 0;
    let mut v_unused_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_8010_) == 0 {
                    v___x_8012_ = l_List_reverse___redArg(v_a_8011_);
                    return v___x_8012_;
                } else {
                    v_head_8013_ = leanh::lean_ctor_get(v_a_8010_, 0);
                    v_toInductionSubgoal_8014_ = leanh::lean_ctor_get(v_head_8013_, 0);
                    leanh::lean_inc_ref(v_toInductionSubgoal_8014_);
                    v_tail_8015_ = leanh::lean_ctor_get(v_a_8010_, 1);
                    v_isSharedCheck_8024_ = (!leanh::lean_is_exclusive(v_a_8010_)) as u8;
                    if v_isSharedCheck_8024_ == 0 {
                        v_unused_8025_ = leanh::lean_ctor_get(v_a_8010_, 0);
                        leanh::lean_dec(v_unused_8025_);
                        v___x_8017_ = v_a_8010_;
                        v_isShared_8018_ = v_isSharedCheck_8024_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_8015_);
                        leanh::lean_dec(v_a_8010_);
                        v___x_8017_ = leanh::lean_box(0);
                        v_isShared_8018_ = v_isSharedCheck_8024_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_8019_ = leanh::lean_ctor_get(v_toInductionSubgoal_8014_, 0);
                leanh::lean_inc(v_mvarId_8019_);
                leanh::lean_dec_ref(v_toInductionSubgoal_8014_);
                if v_isShared_8018_ == 0 {
                    leanh::lean_ctor_set(v___x_8017_, 1, v_a_8011_);
                    leanh::lean_ctor_set(v___x_8017_, 0, v_mvarId_8019_);
                    v___x_8021_ = v___x_8017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8023_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8023_, 0, v_mvarId_8019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8023_, 1, v_a_8011_);
                    v___x_8021_ = v_reuseFailAlloc_8023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8010_ = v_tail_8015_;
                v_a_8011_ = v___x_8021_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(
    mut v_mvarId_8026_: *mut leanh::LeanObject,
    mut v___x_8027_: *mut leanh::LeanObject,
    mut v___x_8028_: *mut leanh::LeanObject,
    mut v___x_8029_: u8,
    mut v___x_8030_: *mut leanh::LeanObject,
    mut v___y_8031_: *mut leanh::LeanObject,
    mut v___y_8032_: *mut leanh::LeanObject,
    mut v___y_8033_: *mut leanh::LeanObject,
    mut v___y_8034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8040_: u8 = 0;
    let mut v___x_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8047_: u8 = 0;
    let mut v_a_8048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8051_: u8 = 0;
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8036_ = l_Lean_Meta_Cases_cases(
                    v_mvarId_8026_,
                    v___x_8027_,
                    v___x_8028_,
                    v___x_8029_,
                    v___x_8030_,
                    v___y_8031_,
                    v___y_8032_,
                    v___y_8033_,
                    v___y_8034_,
                );
                if leanh::lean_obj_tag(v___x_8036_) == 0 {
                    v_a_8037_ = leanh::lean_ctor_get(v___x_8036_, 0);
                    v_isSharedCheck_8047_ = (!leanh::lean_is_exclusive(v___x_8036_)) as u8;
                    if v_isSharedCheck_8047_ == 0 {
                        v___x_8039_ = v___x_8036_;
                        v_isShared_8040_ = v_isSharedCheck_8047_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8037_);
                        leanh::lean_dec(v___x_8036_);
                        v___x_8039_ = leanh::lean_box(0);
                        v_isShared_8040_ = v_isSharedCheck_8047_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8048_ = leanh::lean_ctor_get(v___x_8036_, 0);
                    v_isSharedCheck_8055_ = (!leanh::lean_is_exclusive(v___x_8036_)) as u8;
                    if v_isSharedCheck_8055_ == 0 {
                        v___x_8050_ = v___x_8036_;
                        v_isShared_8051_ = v_isSharedCheck_8055_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8048_);
                        leanh::lean_dec(v___x_8036_);
                        v___x_8050_ = leanh::lean_box(0);
                        v_isShared_8051_ = v_isSharedCheck_8055_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8041_ = lean_array_to_list(v_a_8037_);
                v___x_8042_ = leanh::lean_box(0);
                v___x_8043_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(
                    v___x_8041_,
                    v___x_8042_,
                );
                if v_isShared_8040_ == 0 {
                    leanh::lean_ctor_set(v___x_8039_, 0, v___x_8043_);
                    v___x_8045_ = v___x_8039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8046_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8046_, 0, v___x_8043_);
                    v___x_8045_ = v_reuseFailAlloc_8046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8045_;
            }
            3 => {
                if v_isShared_8051_ == 0 {
                    v___x_8053_ = v___x_8050_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8054_, 0, v_a_8048_);
                    v___x_8053_ = v_reuseFailAlloc_8054_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(
    mut v_mvarId_8056_: *mut leanh::LeanObject,
    mut v___x_8057_: *mut leanh::LeanObject,
    mut v___x_8058_: *mut leanh::LeanObject,
    mut v___x_8059_: *mut leanh::LeanObject,
    mut v___x_8060_: *mut leanh::LeanObject,
    mut v___y_8061_: *mut leanh::LeanObject,
    mut v___y_8062_: *mut leanh::LeanObject,
    mut v___y_8063_: *mut leanh::LeanObject,
    mut v___y_8064_: *mut leanh::LeanObject,
    mut v___y_8065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6516__boxed_8066_: u8 = 0;
    let mut v_res_8067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6516__boxed_8066_ = (leanh::lean_unbox(v___x_8059_) as u8);
    v_res_8067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_8056_, v___x_8057_, v___x_8058_, v___x_6516__boxed_8066_, v___x_8060_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_);
    leanh::lean_dec(v___y_8064_);
    leanh::lean_dec_ref(v___y_8063_);
    leanh::lean_dec(v___y_8062_);
    leanh::lean_dec_ref(v___y_8061_);
    return v_res_8067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(
    mut v_p_8073_: *mut leanh::LeanObject,
    mut v_mvarId_8074_: *mut leanh::LeanObject,
    mut v_as_8075_: *mut leanh::LeanObject,
    mut v_sz_8076_: usize,
    mut v_i_8077_: usize,
    mut v_b_8078_: *mut leanh::LeanObject,
    mut v___y_8079_: *mut leanh::LeanObject,
    mut v___y_8080_: *mut leanh::LeanObject,
    mut v___y_8081_: *mut leanh::LeanObject,
    mut v___y_8082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8084_: u8 = 0;
    let mut v___x_8085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8089_: u8 = 0;
    let mut v___x_8090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: usize = 0;
    let mut v___x_8096_: usize = 0;
    let mut v_reuseFailAlloc_8098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8103_: u8 = 0;
    let mut v___x_8104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: u8 = 0;
    let mut v___x_8109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: u8 = 0;
    let mut v___x_8112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8118_: u8 = 0;
    let mut v___x_8120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8123_: u8 = 0;
    let mut v___x_8124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8133_: u8 = 0;
    let mut v_unused_8134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8136_: u8 = 0;
    let mut v_a_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8140_: u8 = 0;
    let mut v___x_8142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8144_: u8 = 0;
    let mut v_a_8145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8148_: u8 = 0;
    let mut v___x_8150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8152_: u8 = 0;
    let mut v_isSharedCheck_8153_: u8 = 0;
    let mut v_isSharedCheck_8154_: u8 = 0;
    let mut v_unused_8155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8084_ = lean_usize_dec_lt(v_i_8077_, v_sz_8076_);
                if v___x_8084_ == 0 {
                    leanh::lean_dec(v_mvarId_8074_);
                    leanh::lean_dec_ref(v_p_8073_);
                    v___x_8085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8085_, 0, v_b_8078_);
                    return v___x_8085_;
                } else {
                    v_snd_8086_ = leanh::lean_ctor_get(v_b_8078_, 1);
                    v_isSharedCheck_8154_ = (!leanh::lean_is_exclusive(v_b_8078_)) as u8;
                    if v_isSharedCheck_8154_ == 0 {
                        v_unused_8155_ = leanh::lean_ctor_get(v_b_8078_, 0);
                        leanh::lean_dec(v_unused_8155_);
                        v___x_8088_ = v_b_8078_;
                        v_isShared_8089_ = v_isSharedCheck_8154_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8086_);
                        leanh::lean_dec(v_b_8078_);
                        v___x_8088_ = leanh::lean_box(0);
                        v_isShared_8089_ = v_isSharedCheck_8154_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8090_ = leanh::lean_box(0);
                v_a_8099_ = lean_array_uget(v_as_8075_, v_i_8077_);
                if leanh::lean_obj_tag(v_a_8099_) == 0 {
                    v_a_8092_ = v_snd_8086_;
                    state = 2;
                    continue;
                } else {
                    v_val_8100_ = leanh::lean_ctor_get(v_a_8099_, 0);
                    v_isSharedCheck_8153_ = (!leanh::lean_is_exclusive(v_a_8099_)) as u8;
                    if v_isSharedCheck_8153_ == 0 {
                        v___x_8102_ = v_a_8099_;
                        v_isShared_8103_ = v_isSharedCheck_8153_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8100_);
                        leanh::lean_dec(v_a_8099_);
                        v___x_8102_ = leanh::lean_box(0);
                        v_isShared_8103_ = v_isSharedCheck_8153_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8089_ == 0 {
                    leanh::lean_ctor_set(v___x_8088_, 1, v_a_8092_);
                    leanh::lean_ctor_set(v___x_8088_, 0, v___x_8090_);
                    v___x_8094_ = v___x_8088_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8098_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8098_, 0, v___x_8090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8098_, 1, v_a_8092_);
                    v___x_8094_ = v_reuseFailAlloc_8098_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8095_ = 1usize;
                v___x_8096_ = lean_usize_add(v_i_8077_, v___x_8095_);
                v_i_8077_ = v___x_8096_;
                v_b_8078_ = v___x_8094_;
                state = 0;
                continue;
            }
            4 => {
                leanh::lean_inc_ref(v_p_8073_);
                leanh::lean_inc(v___y_8082_);
                leanh::lean_inc_ref(v___y_8081_);
                leanh::lean_inc(v___y_8080_);
                leanh::lean_inc_ref(v___y_8079_);
                leanh::lean_inc(v_val_8100_);
                v___x_8104_ = leanh::lean_apply_6(
                    v_p_8073_,
                    v_val_8100_,
                    v___y_8079_,
                    v___y_8080_,
                    v___y_8081_,
                    v___y_8082_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_8104_) == 0 {
                    v_a_8105_ = leanh::lean_ctor_get(v___x_8104_, 0);
                    leanh::lean_inc(v_a_8105_);
                    leanh::lean_dec_ref_known(v___x_8104_, 1);
                    v___x_8106_ = leanh::lean_box(0);
                    v___x_8107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0;
                    v___x_8108_ = (leanh::lean_unbox(v_a_8105_) as u8);
                    leanh::lean_dec(v_a_8105_);
                    if v___x_8108_ == 0 {
                        leanh::lean_del_object(v___x_8102_);
                        leanh::lean_dec(v_val_8100_);
                        leanh::lean_dec(v_snd_8086_);
                        v_a_8092_ = v___x_8107_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8109_ = l_Lean_LocalDecl_fvarId(v_val_8100_);
                        leanh::lean_dec(v_val_8100_);
                        v___x_8110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1;
                        v___x_8111_ = 0;
                        v___x_8112_ = leanh::lean_box((v___x_8111_) as usize);
                        leanh::lean_inc(v_mvarId_8074_);
                        v___f_8113_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                        leanh::lean_closure_set(v___f_8113_, 0, v_mvarId_8074_);
                        leanh::lean_closure_set(v___f_8113_, 1, v___x_8109_);
                        leanh::lean_closure_set(v___f_8113_, 2, v___x_8110_);
                        leanh::lean_closure_set(v___f_8113_, 3, v___x_8112_);
                        leanh::lean_closure_set(v___f_8113_, 4, v___x_8090_);
                        v___x_8114_ =
                            l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
                                v___f_8113_,
                                v___y_8079_,
                                v___y_8080_,
                                v___y_8081_,
                                v___y_8082_,
                            );
                        if leanh::lean_obj_tag(v___x_8114_) == 0 {
                            v_a_8115_ = leanh::lean_ctor_get(v___x_8114_, 0);
                            v_isSharedCheck_8136_ =
                                (!leanh::lean_is_exclusive(v___x_8114_)) as u8;
                            if v_isSharedCheck_8136_ == 0 {
                                v___x_8117_ = v___x_8114_;
                                v_isShared_8118_ = v_isSharedCheck_8136_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8115_);
                                leanh::lean_dec(v___x_8114_);
                                v___x_8117_ = leanh::lean_box(0);
                                v_isShared_8118_ = v_isSharedCheck_8136_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8102_);
                            leanh::lean_del_object(v___x_8088_);
                            leanh::lean_dec(v_snd_8086_);
                            leanh::lean_dec(v_mvarId_8074_);
                            leanh::lean_dec_ref(v_p_8073_);
                            v_a_8137_ = leanh::lean_ctor_get(v___x_8114_, 0);
                            v_isSharedCheck_8144_ =
                                (!leanh::lean_is_exclusive(v___x_8114_)) as u8;
                            if v_isSharedCheck_8144_ == 0 {
                                v___x_8139_ = v___x_8114_;
                                v_isShared_8140_ = v_isSharedCheck_8144_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8137_);
                                leanh::lean_dec(v___x_8114_);
                                v___x_8139_ = leanh::lean_box(0);
                                v_isShared_8140_ = v_isSharedCheck_8144_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8102_);
                    leanh::lean_dec(v_val_8100_);
                    leanh::lean_del_object(v___x_8088_);
                    leanh::lean_dec(v_snd_8086_);
                    leanh::lean_dec(v_mvarId_8074_);
                    leanh::lean_dec_ref(v_p_8073_);
                    v_a_8145_ = leanh::lean_ctor_get(v___x_8104_, 0);
                    v_isSharedCheck_8152_ = (!leanh::lean_is_exclusive(v___x_8104_)) as u8;
                    if v_isSharedCheck_8152_ == 0 {
                        v___x_8147_ = v___x_8104_;
                        v_isShared_8148_ = v_isSharedCheck_8152_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8145_);
                        leanh::lean_dec(v___x_8104_);
                        v___x_8147_ = leanh::lean_box(0);
                        v_isShared_8148_ = v_isSharedCheck_8152_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_8115_) == 0 {
                    leanh::lean_del_object(v___x_8117_);
                    leanh::lean_del_object(v___x_8102_);
                    leanh::lean_dec(v_snd_8086_);
                    v_a_8092_ = v___x_8107_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_8088_);
                    leanh::lean_dec(v_mvarId_8074_);
                    leanh::lean_dec_ref(v_p_8073_);
                    leanh::lean_inc_ref(v_a_8115_);
                    if v_isShared_8103_ == 0 {
                        leanh::lean_ctor_set(v___x_8102_, 0, v_a_8115_);
                        v___x_8120_ = v___x_8102_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8135_, 0, v_a_8115_);
                        v___x_8120_ = v_reuseFailAlloc_8135_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v_isSharedCheck_8133_ = (!leanh::lean_is_exclusive(v_a_8115_)) as u8;
                if v_isSharedCheck_8133_ == 0 {
                    v_unused_8134_ = leanh::lean_ctor_get(v_a_8115_, 0);
                    leanh::lean_dec(v_unused_8134_);
                    v___x_8122_ = v_a_8115_;
                    v_isShared_8123_ = v_isSharedCheck_8133_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_8115_);
                    v___x_8122_ = leanh::lean_box(0);
                    v_isShared_8123_ = v_isSharedCheck_8133_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_8124_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8124_, 0, v___x_8120_);
                leanh::lean_ctor_set(v___x_8124_, 1, v___x_8106_);
                if v_isShared_8123_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8122_, 0);
                    leanh::lean_ctor_set(v___x_8122_, 0, v___x_8124_);
                    v___x_8126_ = v___x_8122_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8132_, 0, v___x_8124_);
                    v___x_8126_ = v_reuseFailAlloc_8132_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8127_, 0, v___x_8126_);
                v___x_8128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8128_, 0, v___x_8127_);
                leanh::lean_ctor_set(v___x_8128_, 1, v_snd_8086_);
                if v_isShared_8118_ == 0 {
                    leanh::lean_ctor_set(v___x_8117_, 0, v___x_8128_);
                    v___x_8130_ = v___x_8117_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8131_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8131_, 0, v___x_8128_);
                    v___x_8130_ = v_reuseFailAlloc_8131_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8130_;
            }
            10 => {
                if v_isShared_8140_ == 0 {
                    v___x_8142_ = v___x_8139_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8143_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 0, v_a_8137_);
                    v___x_8142_ = v_reuseFailAlloc_8143_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8142_;
            }
            12 => {
                if v_isShared_8148_ == 0 {
                    v___x_8150_ = v___x_8147_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8151_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8151_, 0, v_a_8145_);
                    v___x_8150_ = v_reuseFailAlloc_8151_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(
    mut v_p_8156_: *mut leanh::LeanObject,
    mut v_mvarId_8157_: *mut leanh::LeanObject,
    mut v_as_8158_: *mut leanh::LeanObject,
    mut v_sz_8159_: *mut leanh::LeanObject,
    mut v_i_8160_: *mut leanh::LeanObject,
    mut v_b_8161_: *mut leanh::LeanObject,
    mut v___y_8162_: *mut leanh::LeanObject,
    mut v___y_8163_: *mut leanh::LeanObject,
    mut v___y_8164_: *mut leanh::LeanObject,
    mut v___y_8165_: *mut leanh::LeanObject,
    mut v___y_8166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8167_: usize = 0;
    let mut v_i_boxed_8168_: usize = 0;
    let mut v_res_8169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8167_ = leanh::lean_unbox_usize(v_sz_8159_);
    leanh::lean_dec(v_sz_8159_);
    v_i_boxed_8168_ = leanh::lean_unbox_usize(v_i_8160_);
    leanh::lean_dec(v_i_8160_);
    v_res_8169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_8156_, v_mvarId_8157_, v_as_8158_, v_sz_boxed_8167_, v_i_boxed_8168_, v_b_8161_, v___y_8162_, v___y_8163_, v___y_8164_, v___y_8165_);
    leanh::lean_dec(v___y_8165_);
    leanh::lean_dec_ref(v___y_8164_);
    leanh::lean_dec(v___y_8163_);
    leanh::lean_dec_ref(v___y_8162_);
    leanh::lean_dec_ref(v_as_8158_);
    return v_res_8169_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(
    mut v_p_8170_: *mut leanh::LeanObject,
    mut v_mvarId_8171_: *mut leanh::LeanObject,
    mut v_as_8172_: *mut leanh::LeanObject,
    mut v_sz_8173_: usize,
    mut v_i_8174_: usize,
    mut v_b_8175_: *mut leanh::LeanObject,
    mut v___y_8176_: *mut leanh::LeanObject,
    mut v___y_8177_: *mut leanh::LeanObject,
    mut v___y_8178_: *mut leanh::LeanObject,
    mut v___y_8179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8181_: u8 = 0;
    let mut v___x_8182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8186_: u8 = 0;
    let mut v___x_8187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: usize = 0;
    let mut v___x_8193_: usize = 0;
    let mut v___x_8194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8200_: u8 = 0;
    let mut v___x_8201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8205_: u8 = 0;
    let mut v___x_8206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: u8 = 0;
    let mut v___x_8209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8215_: u8 = 0;
    let mut v___x_8217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8220_: u8 = 0;
    let mut v___x_8221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8230_: u8 = 0;
    let mut v_unused_8231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8233_: u8 = 0;
    let mut v_a_8234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8237_: u8 = 0;
    let mut v___x_8239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8241_: u8 = 0;
    let mut v_a_8242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8245_: u8 = 0;
    let mut v___x_8247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8249_: u8 = 0;
    let mut v_isSharedCheck_8250_: u8 = 0;
    let mut v_isSharedCheck_8251_: u8 = 0;
    let mut v_unused_8252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8181_ = lean_usize_dec_lt(v_i_8174_, v_sz_8173_);
                if v___x_8181_ == 0 {
                    leanh::lean_dec(v_mvarId_8171_);
                    leanh::lean_dec_ref(v_p_8170_);
                    v___x_8182_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8182_, 0, v_b_8175_);
                    return v___x_8182_;
                } else {
                    v_snd_8183_ = leanh::lean_ctor_get(v_b_8175_, 1);
                    v_isSharedCheck_8251_ = (!leanh::lean_is_exclusive(v_b_8175_)) as u8;
                    if v_isSharedCheck_8251_ == 0 {
                        v_unused_8252_ = leanh::lean_ctor_get(v_b_8175_, 0);
                        leanh::lean_dec(v_unused_8252_);
                        v___x_8185_ = v_b_8175_;
                        v_isShared_8186_ = v_isSharedCheck_8251_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8183_);
                        leanh::lean_dec(v_b_8175_);
                        v___x_8185_ = leanh::lean_box(0);
                        v_isShared_8186_ = v_isSharedCheck_8251_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8187_ = leanh::lean_box(0);
                v_a_8196_ = lean_array_uget(v_as_8172_, v_i_8174_);
                if leanh::lean_obj_tag(v_a_8196_) == 0 {
                    v_a_8189_ = v_snd_8183_;
                    state = 2;
                    continue;
                } else {
                    v_val_8197_ = leanh::lean_ctor_get(v_a_8196_, 0);
                    v_isSharedCheck_8250_ = (!leanh::lean_is_exclusive(v_a_8196_)) as u8;
                    if v_isSharedCheck_8250_ == 0 {
                        v___x_8199_ = v_a_8196_;
                        v_isShared_8200_ = v_isSharedCheck_8250_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8197_);
                        leanh::lean_dec(v_a_8196_);
                        v___x_8199_ = leanh::lean_box(0);
                        v_isShared_8200_ = v_isSharedCheck_8250_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8186_ == 0 {
                    leanh::lean_ctor_set(v___x_8185_, 1, v_a_8189_);
                    leanh::lean_ctor_set(v___x_8185_, 0, v___x_8187_);
                    v___x_8191_ = v___x_8185_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8195_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 0, v___x_8187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 1, v_a_8189_);
                    v___x_8191_ = v_reuseFailAlloc_8195_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8192_ = 1usize;
                v___x_8193_ = lean_usize_add(v_i_8174_, v___x_8192_);
                v___x_8194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_8170_, v_mvarId_8171_, v_as_8172_, v_sz_8173_, v___x_8193_, v___x_8191_, v___y_8176_, v___y_8177_, v___y_8178_, v___y_8179_);
                return v___x_8194_;
            }
            4 => {
                leanh::lean_inc_ref(v_p_8170_);
                leanh::lean_inc(v___y_8179_);
                leanh::lean_inc_ref(v___y_8178_);
                leanh::lean_inc(v___y_8177_);
                leanh::lean_inc_ref(v___y_8176_);
                leanh::lean_inc(v_val_8197_);
                v___x_8201_ = leanh::lean_apply_6(
                    v_p_8170_,
                    v_val_8197_,
                    v___y_8176_,
                    v___y_8177_,
                    v___y_8178_,
                    v___y_8179_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_8201_) == 0 {
                    v_a_8202_ = leanh::lean_ctor_get(v___x_8201_, 0);
                    leanh::lean_inc(v_a_8202_);
                    leanh::lean_dec_ref_known(v___x_8201_, 1);
                    v___x_8203_ = leanh::lean_box(0);
                    v___x_8204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0;
                    v___x_8205_ = (leanh::lean_unbox(v_a_8202_) as u8);
                    leanh::lean_dec(v_a_8202_);
                    if v___x_8205_ == 0 {
                        leanh::lean_del_object(v___x_8199_);
                        leanh::lean_dec(v_val_8197_);
                        leanh::lean_dec(v_snd_8183_);
                        v_a_8189_ = v___x_8204_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8206_ = l_Lean_LocalDecl_fvarId(v_val_8197_);
                        leanh::lean_dec(v_val_8197_);
                        v___x_8207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1;
                        v___x_8208_ = 0;
                        v___x_8209_ = leanh::lean_box((v___x_8208_) as usize);
                        leanh::lean_inc(v_mvarId_8171_);
                        v___f_8210_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                        leanh::lean_closure_set(v___f_8210_, 0, v_mvarId_8171_);
                        leanh::lean_closure_set(v___f_8210_, 1, v___x_8206_);
                        leanh::lean_closure_set(v___f_8210_, 2, v___x_8207_);
                        leanh::lean_closure_set(v___f_8210_, 3, v___x_8209_);
                        leanh::lean_closure_set(v___f_8210_, 4, v___x_8187_);
                        v___x_8211_ =
                            l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
                                v___f_8210_,
                                v___y_8176_,
                                v___y_8177_,
                                v___y_8178_,
                                v___y_8179_,
                            );
                        if leanh::lean_obj_tag(v___x_8211_) == 0 {
                            v_a_8212_ = leanh::lean_ctor_get(v___x_8211_, 0);
                            v_isSharedCheck_8233_ =
                                (!leanh::lean_is_exclusive(v___x_8211_)) as u8;
                            if v_isSharedCheck_8233_ == 0 {
                                v___x_8214_ = v___x_8211_;
                                v_isShared_8215_ = v_isSharedCheck_8233_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8212_);
                                leanh::lean_dec(v___x_8211_);
                                v___x_8214_ = leanh::lean_box(0);
                                v_isShared_8215_ = v_isSharedCheck_8233_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8199_);
                            leanh::lean_del_object(v___x_8185_);
                            leanh::lean_dec(v_snd_8183_);
                            leanh::lean_dec(v_mvarId_8171_);
                            leanh::lean_dec_ref(v_p_8170_);
                            v_a_8234_ = leanh::lean_ctor_get(v___x_8211_, 0);
                            v_isSharedCheck_8241_ =
                                (!leanh::lean_is_exclusive(v___x_8211_)) as u8;
                            if v_isSharedCheck_8241_ == 0 {
                                v___x_8236_ = v___x_8211_;
                                v_isShared_8237_ = v_isSharedCheck_8241_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8234_);
                                leanh::lean_dec(v___x_8211_);
                                v___x_8236_ = leanh::lean_box(0);
                                v_isShared_8237_ = v_isSharedCheck_8241_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8199_);
                    leanh::lean_dec(v_val_8197_);
                    leanh::lean_del_object(v___x_8185_);
                    leanh::lean_dec(v_snd_8183_);
                    leanh::lean_dec(v_mvarId_8171_);
                    leanh::lean_dec_ref(v_p_8170_);
                    v_a_8242_ = leanh::lean_ctor_get(v___x_8201_, 0);
                    v_isSharedCheck_8249_ = (!leanh::lean_is_exclusive(v___x_8201_)) as u8;
                    if v_isSharedCheck_8249_ == 0 {
                        v___x_8244_ = v___x_8201_;
                        v_isShared_8245_ = v_isSharedCheck_8249_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8242_);
                        leanh::lean_dec(v___x_8201_);
                        v___x_8244_ = leanh::lean_box(0);
                        v_isShared_8245_ = v_isSharedCheck_8249_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_8212_) == 0 {
                    leanh::lean_del_object(v___x_8214_);
                    leanh::lean_del_object(v___x_8199_);
                    leanh::lean_dec(v_snd_8183_);
                    v_a_8189_ = v___x_8204_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_8185_);
                    leanh::lean_dec(v_mvarId_8171_);
                    leanh::lean_dec_ref(v_p_8170_);
                    leanh::lean_inc_ref(v_a_8212_);
                    if v_isShared_8200_ == 0 {
                        leanh::lean_ctor_set(v___x_8199_, 0, v_a_8212_);
                        v___x_8217_ = v___x_8199_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8232_, 0, v_a_8212_);
                        v___x_8217_ = v_reuseFailAlloc_8232_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v_isSharedCheck_8230_ = (!leanh::lean_is_exclusive(v_a_8212_)) as u8;
                if v_isSharedCheck_8230_ == 0 {
                    v_unused_8231_ = leanh::lean_ctor_get(v_a_8212_, 0);
                    leanh::lean_dec(v_unused_8231_);
                    v___x_8219_ = v_a_8212_;
                    v_isShared_8220_ = v_isSharedCheck_8230_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_8212_);
                    v___x_8219_ = leanh::lean_box(0);
                    v_isShared_8220_ = v_isSharedCheck_8230_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_8221_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8221_, 0, v___x_8217_);
                leanh::lean_ctor_set(v___x_8221_, 1, v___x_8203_);
                if v_isShared_8220_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8219_, 0);
                    leanh::lean_ctor_set(v___x_8219_, 0, v___x_8221_);
                    v___x_8223_ = v___x_8219_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8229_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8229_, 0, v___x_8221_);
                    v___x_8223_ = v_reuseFailAlloc_8229_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8224_, 0, v___x_8223_);
                v___x_8225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8225_, 0, v___x_8224_);
                leanh::lean_ctor_set(v___x_8225_, 1, v_snd_8183_);
                if v_isShared_8215_ == 0 {
                    leanh::lean_ctor_set(v___x_8214_, 0, v___x_8225_);
                    v___x_8227_ = v___x_8214_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8228_, 0, v___x_8225_);
                    v___x_8227_ = v_reuseFailAlloc_8228_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8227_;
            }
            10 => {
                if v_isShared_8237_ == 0 {
                    v___x_8239_ = v___x_8236_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8240_, 0, v_a_8234_);
                    v___x_8239_ = v_reuseFailAlloc_8240_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8239_;
            }
            12 => {
                if v_isShared_8245_ == 0 {
                    v___x_8247_ = v___x_8244_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8248_, 0, v_a_8242_);
                    v___x_8247_ = v_reuseFailAlloc_8248_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(
    mut v_p_8253_: *mut leanh::LeanObject,
    mut v_mvarId_8254_: *mut leanh::LeanObject,
    mut v_as_8255_: *mut leanh::LeanObject,
    mut v_sz_8256_: *mut leanh::LeanObject,
    mut v_i_8257_: *mut leanh::LeanObject,
    mut v_b_8258_: *mut leanh::LeanObject,
    mut v___y_8259_: *mut leanh::LeanObject,
    mut v___y_8260_: *mut leanh::LeanObject,
    mut v___y_8261_: *mut leanh::LeanObject,
    mut v___y_8262_: *mut leanh::LeanObject,
    mut v___y_8263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8264_: usize = 0;
    let mut v_i_boxed_8265_: usize = 0;
    let mut v_res_8266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8264_ = leanh::lean_unbox_usize(v_sz_8256_);
    leanh::lean_dec(v_sz_8256_);
    v_i_boxed_8265_ = leanh::lean_unbox_usize(v_i_8257_);
    leanh::lean_dec(v_i_8257_);
    v_res_8266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_8253_, v_mvarId_8254_, v_as_8255_, v_sz_boxed_8264_, v_i_boxed_8265_, v_b_8258_, v___y_8259_, v___y_8260_, v___y_8261_, v___y_8262_);
    leanh::lean_dec(v___y_8262_);
    leanh::lean_dec_ref(v___y_8261_);
    leanh::lean_dec(v___y_8260_);
    leanh::lean_dec_ref(v___y_8259_);
    leanh::lean_dec_ref(v_as_8255_);
    return v_res_8266_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(
    mut v_init_8267_: *mut leanh::LeanObject,
    mut v_p_8268_: *mut leanh::LeanObject,
    mut v_mvarId_8269_: *mut leanh::LeanObject,
    mut v_n_8270_: *mut leanh::LeanObject,
    mut v_b_8271_: *mut leanh::LeanObject,
    mut v___y_8272_: *mut leanh::LeanObject,
    mut v___y_8273_: *mut leanh::LeanObject,
    mut v___y_8274_: *mut leanh::LeanObject,
    mut v___y_8275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_8277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8280_: usize = 0;
    let mut v___x_8281_: usize = 0;
    let mut v___x_8282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8286_: u8 = 0;
    let mut v_fst_8287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8297_: u8 = 0;
    let mut v_a_8298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8301_: u8 = 0;
    let mut v___x_8303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8305_: u8 = 0;
    let mut v_vs_8306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8309_: usize = 0;
    let mut v___x_8310_: usize = 0;
    let mut v___x_8311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8315_: u8 = 0;
    let mut v_fst_8316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8326_: u8 = 0;
    let mut v_a_8327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8330_: u8 = 0;
    let mut v___x_8332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_8270_) == 0 {
                    v_cs_8277_ = leanh::lean_ctor_get(v_n_8270_, 0);
                    v___x_8278_ = leanh::lean_box(0);
                    v___x_8279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8279_, 0, v___x_8278_);
                    leanh::lean_ctor_set(v___x_8279_, 1, v_b_8271_);
                    v_sz_8280_ = lean_array_size(v_cs_8277_);
                    v___x_8281_ = 0usize;
                    v___x_8282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_8267_, v_p_8268_, v_mvarId_8269_, v_cs_8277_, v_sz_8280_, v___x_8281_, v___x_8279_, v___y_8272_, v___y_8273_, v___y_8274_, v___y_8275_);
                    if leanh::lean_obj_tag(v___x_8282_) == 0 {
                        v_a_8283_ = leanh::lean_ctor_get(v___x_8282_, 0);
                        v_isSharedCheck_8297_ =
                            (!leanh::lean_is_exclusive(v___x_8282_)) as u8;
                        if v_isSharedCheck_8297_ == 0 {
                            v___x_8285_ = v___x_8282_;
                            v_isShared_8286_ = v_isSharedCheck_8297_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8283_);
                            leanh::lean_dec(v___x_8282_);
                            v___x_8285_ = leanh::lean_box(0);
                            v_isShared_8286_ = v_isSharedCheck_8297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8298_ = leanh::lean_ctor_get(v___x_8282_, 0);
                        v_isSharedCheck_8305_ =
                            (!leanh::lean_is_exclusive(v___x_8282_)) as u8;
                        if v_isSharedCheck_8305_ == 0 {
                            v___x_8300_ = v___x_8282_;
                            v_isShared_8301_ = v_isSharedCheck_8305_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8298_);
                            leanh::lean_dec(v___x_8282_);
                            v___x_8300_ = leanh::lean_box(0);
                            v_isShared_8301_ = v_isSharedCheck_8305_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_8306_ = leanh::lean_ctor_get(v_n_8270_, 0);
                    v___x_8307_ = leanh::lean_box(0);
                    v___x_8308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8308_, 0, v___x_8307_);
                    leanh::lean_ctor_set(v___x_8308_, 1, v_b_8271_);
                    v_sz_8309_ = lean_array_size(v_vs_8306_);
                    v___x_8310_ = 0usize;
                    v___x_8311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_8268_, v_mvarId_8269_, v_vs_8306_, v_sz_8309_, v___x_8310_, v___x_8308_, v___y_8272_, v___y_8273_, v___y_8274_, v___y_8275_);
                    if leanh::lean_obj_tag(v___x_8311_) == 0 {
                        v_a_8312_ = leanh::lean_ctor_get(v___x_8311_, 0);
                        v_isSharedCheck_8326_ =
                            (!leanh::lean_is_exclusive(v___x_8311_)) as u8;
                        if v_isSharedCheck_8326_ == 0 {
                            v___x_8314_ = v___x_8311_;
                            v_isShared_8315_ = v_isSharedCheck_8326_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8312_);
                            leanh::lean_dec(v___x_8311_);
                            v___x_8314_ = leanh::lean_box(0);
                            v_isShared_8315_ = v_isSharedCheck_8326_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_8327_ = leanh::lean_ctor_get(v___x_8311_, 0);
                        v_isSharedCheck_8334_ =
                            (!leanh::lean_is_exclusive(v___x_8311_)) as u8;
                        if v_isSharedCheck_8334_ == 0 {
                            v___x_8329_ = v___x_8311_;
                            v_isShared_8330_ = v_isSharedCheck_8334_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8327_);
                            leanh::lean_dec(v___x_8311_);
                            v___x_8329_ = leanh::lean_box(0);
                            v_isShared_8330_ = v_isSharedCheck_8334_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_8287_ = leanh::lean_ctor_get(v_a_8283_, 0);
                if leanh::lean_obj_tag(v_fst_8287_) == 0 {
                    v_snd_8288_ = leanh::lean_ctor_get(v_a_8283_, 1);
                    leanh::lean_inc(v_snd_8288_);
                    leanh::lean_dec(v_a_8283_);
                    v___x_8289_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8289_, 0, v_snd_8288_);
                    if v_isShared_8286_ == 0 {
                        leanh::lean_ctor_set(v___x_8285_, 0, v___x_8289_);
                        v___x_8291_ = v___x_8285_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8292_, 0, v___x_8289_);
                        v___x_8291_ = v_reuseFailAlloc_8292_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_8287_);
                    leanh::lean_dec(v_a_8283_);
                    v_val_8293_ = leanh::lean_ctor_get(v_fst_8287_, 0);
                    leanh::lean_inc(v_val_8293_);
                    leanh::lean_dec_ref_known(v_fst_8287_, 1);
                    if v_isShared_8286_ == 0 {
                        leanh::lean_ctor_set(v___x_8285_, 0, v_val_8293_);
                        v___x_8295_ = v___x_8285_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8296_, 0, v_val_8293_);
                        v___x_8295_ = v_reuseFailAlloc_8296_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8291_;
            }
            3 => {
                return v___x_8295_;
            }
            4 => {
                if v_isShared_8301_ == 0 {
                    v___x_8303_ = v___x_8300_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8304_, 0, v_a_8298_);
                    v___x_8303_ = v_reuseFailAlloc_8304_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8303_;
            }
            6 => {
                v_fst_8316_ = leanh::lean_ctor_get(v_a_8312_, 0);
                if leanh::lean_obj_tag(v_fst_8316_) == 0 {
                    v_snd_8317_ = leanh::lean_ctor_get(v_a_8312_, 1);
                    leanh::lean_inc(v_snd_8317_);
                    leanh::lean_dec(v_a_8312_);
                    v___x_8318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8318_, 0, v_snd_8317_);
                    if v_isShared_8315_ == 0 {
                        leanh::lean_ctor_set(v___x_8314_, 0, v___x_8318_);
                        v___x_8320_ = v___x_8314_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_8321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8321_, 0, v___x_8318_);
                        v___x_8320_ = v_reuseFailAlloc_8321_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_8316_);
                    leanh::lean_dec(v_a_8312_);
                    v_val_8322_ = leanh::lean_ctor_get(v_fst_8316_, 0);
                    leanh::lean_inc(v_val_8322_);
                    leanh::lean_dec_ref_known(v_fst_8316_, 1);
                    if v_isShared_8315_ == 0 {
                        leanh::lean_ctor_set(v___x_8314_, 0, v_val_8322_);
                        v___x_8324_ = v___x_8314_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_8325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8325_, 0, v_val_8322_);
                        v___x_8324_ = v_reuseFailAlloc_8325_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_8320_;
            }
            8 => {
                return v___x_8324_;
            }
            9 => {
                if v_isShared_8330_ == 0 {
                    v___x_8332_ = v___x_8329_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8333_, 0, v_a_8327_);
                    v___x_8332_ = v_reuseFailAlloc_8333_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(
    mut v_init_8335_: *mut leanh::LeanObject,
    mut v_p_8336_: *mut leanh::LeanObject,
    mut v_mvarId_8337_: *mut leanh::LeanObject,
    mut v_as_8338_: *mut leanh::LeanObject,
    mut v_sz_8339_: usize,
    mut v_i_8340_: usize,
    mut v_b_8341_: *mut leanh::LeanObject,
    mut v___y_8342_: *mut leanh::LeanObject,
    mut v___y_8343_: *mut leanh::LeanObject,
    mut v___y_8344_: *mut leanh::LeanObject,
    mut v___y_8345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8347_: u8 = 0;
    let mut v___x_8348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8352_: u8 = 0;
    let mut v_a_8353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8358_: u8 = 0;
    let mut v___x_8359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8370_: usize = 0;
    let mut v___x_8371_: usize = 0;
    let mut v_reuseFailAlloc_8373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8374_: u8 = 0;
    let mut v_a_8375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8378_: u8 = 0;
    let mut v___x_8380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8382_: u8 = 0;
    let mut v_isSharedCheck_8383_: u8 = 0;
    let mut v_unused_8384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8347_ = lean_usize_dec_lt(v_i_8340_, v_sz_8339_);
                if v___x_8347_ == 0 {
                    leanh::lean_dec(v_mvarId_8337_);
                    leanh::lean_dec_ref(v_p_8336_);
                    v___x_8348_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8348_, 0, v_b_8341_);
                    return v___x_8348_;
                } else {
                    v_snd_8349_ = leanh::lean_ctor_get(v_b_8341_, 1);
                    v_isSharedCheck_8383_ = (!leanh::lean_is_exclusive(v_b_8341_)) as u8;
                    if v_isSharedCheck_8383_ == 0 {
                        v_unused_8384_ = leanh::lean_ctor_get(v_b_8341_, 0);
                        leanh::lean_dec(v_unused_8384_);
                        v___x_8351_ = v_b_8341_;
                        v_isShared_8352_ = v_isSharedCheck_8383_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8349_);
                        leanh::lean_dec(v_b_8341_);
                        v___x_8351_ = leanh::lean_box(0);
                        v_isShared_8352_ = v_isSharedCheck_8383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_8353_ = lean_array_uget_borrowed(v_as_8338_, v_i_8340_);
                leanh::lean_inc(v_snd_8349_);
                leanh::lean_inc(v_mvarId_8337_);
                leanh::lean_inc_ref(v_p_8336_);
                v___x_8354_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_8335_, v_p_8336_, v_mvarId_8337_, v_a_8353_, v_snd_8349_, v___y_8342_, v___y_8343_, v___y_8344_, v___y_8345_);
                if leanh::lean_obj_tag(v___x_8354_) == 0 {
                    v_a_8355_ = leanh::lean_ctor_get(v___x_8354_, 0);
                    v_isSharedCheck_8374_ = (!leanh::lean_is_exclusive(v___x_8354_)) as u8;
                    if v_isSharedCheck_8374_ == 0 {
                        v___x_8357_ = v___x_8354_;
                        v_isShared_8358_ = v_isSharedCheck_8374_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8355_);
                        leanh::lean_dec(v___x_8354_);
                        v___x_8357_ = leanh::lean_box(0);
                        v_isShared_8358_ = v_isSharedCheck_8374_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8351_);
                    leanh::lean_dec(v_snd_8349_);
                    leanh::lean_dec(v_mvarId_8337_);
                    leanh::lean_dec_ref(v_p_8336_);
                    v_a_8375_ = leanh::lean_ctor_get(v___x_8354_, 0);
                    v_isSharedCheck_8382_ = (!leanh::lean_is_exclusive(v___x_8354_)) as u8;
                    if v_isSharedCheck_8382_ == 0 {
                        v___x_8377_ = v___x_8354_;
                        v_isShared_8378_ = v_isSharedCheck_8382_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8375_);
                        leanh::lean_dec(v___x_8354_);
                        v___x_8377_ = leanh::lean_box(0);
                        v_isShared_8378_ = v_isSharedCheck_8382_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_8355_) == 0 {
                    leanh::lean_dec(v_mvarId_8337_);
                    leanh::lean_dec_ref(v_p_8336_);
                    v___x_8359_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8359_, 0, v_a_8355_);
                    if v_isShared_8352_ == 0 {
                        leanh::lean_ctor_set(v___x_8351_, 0, v___x_8359_);
                        v___x_8361_ = v___x_8351_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8365_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8365_, 0, v___x_8359_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8365_, 1, v_snd_8349_);
                        v___x_8361_ = v_reuseFailAlloc_8365_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8357_);
                    leanh::lean_dec(v_snd_8349_);
                    v_a_8366_ = leanh::lean_ctor_get(v_a_8355_, 0);
                    leanh::lean_inc(v_a_8366_);
                    leanh::lean_dec_ref_known(v_a_8355_, 1);
                    v___x_8367_ = leanh::lean_box(0);
                    if v_isShared_8352_ == 0 {
                        leanh::lean_ctor_set(v___x_8351_, 1, v_a_8366_);
                        leanh::lean_ctor_set(v___x_8351_, 0, v___x_8367_);
                        v___x_8369_ = v___x_8351_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8373_, 0, v___x_8367_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8373_, 1, v_a_8366_);
                        v___x_8369_ = v_reuseFailAlloc_8373_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8358_ == 0 {
                    leanh::lean_ctor_set(v___x_8357_, 0, v___x_8361_);
                    v___x_8363_ = v___x_8357_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8364_, 0, v___x_8361_);
                    v___x_8363_ = v_reuseFailAlloc_8364_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8363_;
            }
            5 => {
                v___x_8370_ = 1usize;
                v___x_8371_ = lean_usize_add(v_i_8340_, v___x_8370_);
                v_i_8340_ = v___x_8371_;
                v_b_8341_ = v___x_8369_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_8378_ == 0 {
                    v___x_8380_ = v___x_8377_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8381_, 0, v_a_8375_);
                    v___x_8380_ = v_reuseFailAlloc_8381_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(
    mut v_init_8385_: *mut leanh::LeanObject,
    mut v_p_8386_: *mut leanh::LeanObject,
    mut v_mvarId_8387_: *mut leanh::LeanObject,
    mut v_as_8388_: *mut leanh::LeanObject,
    mut v_sz_8389_: *mut leanh::LeanObject,
    mut v_i_8390_: *mut leanh::LeanObject,
    mut v_b_8391_: *mut leanh::LeanObject,
    mut v___y_8392_: *mut leanh::LeanObject,
    mut v___y_8393_: *mut leanh::LeanObject,
    mut v___y_8394_: *mut leanh::LeanObject,
    mut v___y_8395_: *mut leanh::LeanObject,
    mut v___y_8396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8397_: usize = 0;
    let mut v_i_boxed_8398_: usize = 0;
    let mut v_res_8399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8397_ = leanh::lean_unbox_usize(v_sz_8389_);
    leanh::lean_dec(v_sz_8389_);
    v_i_boxed_8398_ = leanh::lean_unbox_usize(v_i_8390_);
    leanh::lean_dec(v_i_8390_);
    v_res_8399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_8385_, v_p_8386_, v_mvarId_8387_, v_as_8388_, v_sz_boxed_8397_, v_i_boxed_8398_, v_b_8391_, v___y_8392_, v___y_8393_, v___y_8394_, v___y_8395_);
    leanh::lean_dec(v___y_8395_);
    leanh::lean_dec_ref(v___y_8394_);
    leanh::lean_dec(v___y_8393_);
    leanh::lean_dec_ref(v___y_8392_);
    leanh::lean_dec_ref(v_as_8388_);
    leanh::lean_dec_ref(v_init_8385_);
    return v_res_8399_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(
    mut v_init_8400_: *mut leanh::LeanObject,
    mut v_p_8401_: *mut leanh::LeanObject,
    mut v_mvarId_8402_: *mut leanh::LeanObject,
    mut v_n_8403_: *mut leanh::LeanObject,
    mut v_b_8404_: *mut leanh::LeanObject,
    mut v___y_8405_: *mut leanh::LeanObject,
    mut v___y_8406_: *mut leanh::LeanObject,
    mut v___y_8407_: *mut leanh::LeanObject,
    mut v___y_8408_: *mut leanh::LeanObject,
    mut v___y_8409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8410_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_8400_, v_p_8401_, v_mvarId_8402_, v_n_8403_, v_b_8404_, v___y_8405_, v___y_8406_, v___y_8407_, v___y_8408_);
    leanh::lean_dec(v___y_8408_);
    leanh::lean_dec_ref(v___y_8407_);
    leanh::lean_dec(v___y_8406_);
    leanh::lean_dec_ref(v___y_8405_);
    leanh::lean_dec_ref(v_n_8403_);
    leanh::lean_dec_ref(v_init_8400_);
    return v_res_8410_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(
    mut v_p_8414_: *mut leanh::LeanObject,
    mut v_mvarId_8415_: *mut leanh::LeanObject,
    mut v_as_8416_: *mut leanh::LeanObject,
    mut v_sz_8417_: usize,
    mut v_i_8418_: usize,
    mut v_b_8419_: *mut leanh::LeanObject,
    mut v___y_8420_: *mut leanh::LeanObject,
    mut v___y_8421_: *mut leanh::LeanObject,
    mut v___y_8422_: *mut leanh::LeanObject,
    mut v___y_8423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8425_: u8 = 0;
    let mut v___x_8426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8430_: u8 = 0;
    let mut v___x_8431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8436_: usize = 0;
    let mut v___x_8437_: usize = 0;
    let mut v_reuseFailAlloc_8439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8444_: u8 = 0;
    let mut v___x_8445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8449_: u8 = 0;
    let mut v___x_8450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8452_: u8 = 0;
    let mut v___x_8453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8459_: u8 = 0;
    let mut v___x_8461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8464_: u8 = 0;
    let mut v___x_8465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8473_: u8 = 0;
    let mut v_unused_8474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8476_: u8 = 0;
    let mut v_a_8477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8480_: u8 = 0;
    let mut v___x_8482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8484_: u8 = 0;
    let mut v_a_8485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8488_: u8 = 0;
    let mut v___x_8490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8492_: u8 = 0;
    let mut v_isSharedCheck_8493_: u8 = 0;
    let mut v_isSharedCheck_8494_: u8 = 0;
    let mut v_unused_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8425_ = lean_usize_dec_lt(v_i_8418_, v_sz_8417_);
                if v___x_8425_ == 0 {
                    leanh::lean_dec(v_mvarId_8415_);
                    leanh::lean_dec_ref(v_p_8414_);
                    v___x_8426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8426_, 0, v_b_8419_);
                    return v___x_8426_;
                } else {
                    v_snd_8427_ = leanh::lean_ctor_get(v_b_8419_, 1);
                    v_isSharedCheck_8494_ = (!leanh::lean_is_exclusive(v_b_8419_)) as u8;
                    if v_isSharedCheck_8494_ == 0 {
                        v_unused_8495_ = leanh::lean_ctor_get(v_b_8419_, 0);
                        leanh::lean_dec(v_unused_8495_);
                        v___x_8429_ = v_b_8419_;
                        v_isShared_8430_ = v_isSharedCheck_8494_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8427_);
                        leanh::lean_dec(v_b_8419_);
                        v___x_8429_ = leanh::lean_box(0);
                        v_isShared_8430_ = v_isSharedCheck_8494_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8431_ = leanh::lean_box(0);
                v_a_8440_ = lean_array_uget(v_as_8416_, v_i_8418_);
                if leanh::lean_obj_tag(v_a_8440_) == 0 {
                    v_a_8433_ = v_snd_8427_;
                    state = 2;
                    continue;
                } else {
                    v_val_8441_ = leanh::lean_ctor_get(v_a_8440_, 0);
                    v_isSharedCheck_8493_ = (!leanh::lean_is_exclusive(v_a_8440_)) as u8;
                    if v_isSharedCheck_8493_ == 0 {
                        v___x_8443_ = v_a_8440_;
                        v_isShared_8444_ = v_isSharedCheck_8493_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8441_);
                        leanh::lean_dec(v_a_8440_);
                        v___x_8443_ = leanh::lean_box(0);
                        v_isShared_8444_ = v_isSharedCheck_8493_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8430_ == 0 {
                    leanh::lean_ctor_set(v___x_8429_, 1, v_a_8433_);
                    leanh::lean_ctor_set(v___x_8429_, 0, v___x_8431_);
                    v___x_8435_ = v___x_8429_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8439_, 0, v___x_8431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8439_, 1, v_a_8433_);
                    v___x_8435_ = v_reuseFailAlloc_8439_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8436_ = 1usize;
                v___x_8437_ = lean_usize_add(v_i_8418_, v___x_8436_);
                v_i_8418_ = v___x_8437_;
                v_b_8419_ = v___x_8435_;
                state = 0;
                continue;
            }
            4 => {
                leanh::lean_inc_ref(v_p_8414_);
                leanh::lean_inc(v___y_8423_);
                leanh::lean_inc_ref(v___y_8422_);
                leanh::lean_inc(v___y_8421_);
                leanh::lean_inc_ref(v___y_8420_);
                leanh::lean_inc(v_val_8441_);
                v___x_8445_ = leanh::lean_apply_6(
                    v_p_8414_,
                    v_val_8441_,
                    v___y_8420_,
                    v___y_8421_,
                    v___y_8422_,
                    v___y_8423_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_8445_) == 0 {
                    v_a_8446_ = leanh::lean_ctor_get(v___x_8445_, 0);
                    leanh::lean_inc(v_a_8446_);
                    leanh::lean_dec_ref_known(v___x_8445_, 1);
                    v___x_8447_ = leanh::lean_box(0);
                    v___x_8448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0;
                    v___x_8449_ = (leanh::lean_unbox(v_a_8446_) as u8);
                    leanh::lean_dec(v_a_8446_);
                    if v___x_8449_ == 0 {
                        leanh::lean_del_object(v___x_8443_);
                        leanh::lean_dec(v_val_8441_);
                        leanh::lean_dec(v_snd_8427_);
                        v_a_8433_ = v___x_8448_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8450_ = l_Lean_LocalDecl_fvarId(v_val_8441_);
                        leanh::lean_dec(v_val_8441_);
                        v___x_8451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1;
                        v___x_8452_ = 0;
                        v___x_8453_ = leanh::lean_box((v___x_8452_) as usize);
                        leanh::lean_inc(v_mvarId_8415_);
                        v___f_8454_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                        leanh::lean_closure_set(v___f_8454_, 0, v_mvarId_8415_);
                        leanh::lean_closure_set(v___f_8454_, 1, v___x_8450_);
                        leanh::lean_closure_set(v___f_8454_, 2, v___x_8451_);
                        leanh::lean_closure_set(v___f_8454_, 3, v___x_8453_);
                        leanh::lean_closure_set(v___f_8454_, 4, v___x_8431_);
                        v___x_8455_ =
                            l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
                                v___f_8454_,
                                v___y_8420_,
                                v___y_8421_,
                                v___y_8422_,
                                v___y_8423_,
                            );
                        if leanh::lean_obj_tag(v___x_8455_) == 0 {
                            v_a_8456_ = leanh::lean_ctor_get(v___x_8455_, 0);
                            v_isSharedCheck_8476_ =
                                (!leanh::lean_is_exclusive(v___x_8455_)) as u8;
                            if v_isSharedCheck_8476_ == 0 {
                                v___x_8458_ = v___x_8455_;
                                v_isShared_8459_ = v_isSharedCheck_8476_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8456_);
                                leanh::lean_dec(v___x_8455_);
                                v___x_8458_ = leanh::lean_box(0);
                                v_isShared_8459_ = v_isSharedCheck_8476_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8443_);
                            leanh::lean_del_object(v___x_8429_);
                            leanh::lean_dec(v_snd_8427_);
                            leanh::lean_dec(v_mvarId_8415_);
                            leanh::lean_dec_ref(v_p_8414_);
                            v_a_8477_ = leanh::lean_ctor_get(v___x_8455_, 0);
                            v_isSharedCheck_8484_ =
                                (!leanh::lean_is_exclusive(v___x_8455_)) as u8;
                            if v_isSharedCheck_8484_ == 0 {
                                v___x_8479_ = v___x_8455_;
                                v_isShared_8480_ = v_isSharedCheck_8484_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8477_);
                                leanh::lean_dec(v___x_8455_);
                                v___x_8479_ = leanh::lean_box(0);
                                v_isShared_8480_ = v_isSharedCheck_8484_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8443_);
                    leanh::lean_dec(v_val_8441_);
                    leanh::lean_del_object(v___x_8429_);
                    leanh::lean_dec(v_snd_8427_);
                    leanh::lean_dec(v_mvarId_8415_);
                    leanh::lean_dec_ref(v_p_8414_);
                    v_a_8485_ = leanh::lean_ctor_get(v___x_8445_, 0);
                    v_isSharedCheck_8492_ = (!leanh::lean_is_exclusive(v___x_8445_)) as u8;
                    if v_isSharedCheck_8492_ == 0 {
                        v___x_8487_ = v___x_8445_;
                        v_isShared_8488_ = v_isSharedCheck_8492_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8485_);
                        leanh::lean_dec(v___x_8445_);
                        v___x_8487_ = leanh::lean_box(0);
                        v_isShared_8488_ = v_isSharedCheck_8492_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_8456_) == 0 {
                    leanh::lean_del_object(v___x_8458_);
                    leanh::lean_del_object(v___x_8443_);
                    leanh::lean_dec(v_snd_8427_);
                    v_a_8433_ = v___x_8448_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_8429_);
                    leanh::lean_dec(v_mvarId_8415_);
                    leanh::lean_dec_ref(v_p_8414_);
                    leanh::lean_inc_ref(v_a_8456_);
                    if v_isShared_8444_ == 0 {
                        leanh::lean_ctor_set(v___x_8443_, 0, v_a_8456_);
                        v___x_8461_ = v___x_8443_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8475_, 0, v_a_8456_);
                        v___x_8461_ = v_reuseFailAlloc_8475_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v_isSharedCheck_8473_ = (!leanh::lean_is_exclusive(v_a_8456_)) as u8;
                if v_isSharedCheck_8473_ == 0 {
                    v_unused_8474_ = leanh::lean_ctor_get(v_a_8456_, 0);
                    leanh::lean_dec(v_unused_8474_);
                    v___x_8463_ = v_a_8456_;
                    v_isShared_8464_ = v_isSharedCheck_8473_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_8456_);
                    v___x_8463_ = leanh::lean_box(0);
                    v_isShared_8464_ = v_isSharedCheck_8473_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_8465_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8465_, 0, v___x_8461_);
                leanh::lean_ctor_set(v___x_8465_, 1, v___x_8447_);
                if v_isShared_8464_ == 0 {
                    leanh::lean_ctor_set(v___x_8463_, 0, v___x_8465_);
                    v___x_8467_ = v___x_8463_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8472_, 0, v___x_8465_);
                    v___x_8467_ = v_reuseFailAlloc_8472_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8468_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8468_, 0, v___x_8467_);
                leanh::lean_ctor_set(v___x_8468_, 1, v_snd_8427_);
                if v_isShared_8459_ == 0 {
                    leanh::lean_ctor_set(v___x_8458_, 0, v___x_8468_);
                    v___x_8470_ = v___x_8458_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8471_, 0, v___x_8468_);
                    v___x_8470_ = v_reuseFailAlloc_8471_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8470_;
            }
            10 => {
                if v_isShared_8480_ == 0 {
                    v___x_8482_ = v___x_8479_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8483_, 0, v_a_8477_);
                    v___x_8482_ = v_reuseFailAlloc_8483_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8482_;
            }
            12 => {
                if v_isShared_8488_ == 0 {
                    v___x_8490_ = v___x_8487_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8491_, 0, v_a_8485_);
                    v___x_8490_ = v_reuseFailAlloc_8491_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(
    mut v_p_8496_: *mut leanh::LeanObject,
    mut v_mvarId_8497_: *mut leanh::LeanObject,
    mut v_as_8498_: *mut leanh::LeanObject,
    mut v_sz_8499_: *mut leanh::LeanObject,
    mut v_i_8500_: *mut leanh::LeanObject,
    mut v_b_8501_: *mut leanh::LeanObject,
    mut v___y_8502_: *mut leanh::LeanObject,
    mut v___y_8503_: *mut leanh::LeanObject,
    mut v___y_8504_: *mut leanh::LeanObject,
    mut v___y_8505_: *mut leanh::LeanObject,
    mut v___y_8506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8507_: usize = 0;
    let mut v_i_boxed_8508_: usize = 0;
    let mut v_res_8509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8507_ = leanh::lean_unbox_usize(v_sz_8499_);
    leanh::lean_dec(v_sz_8499_);
    v_i_boxed_8508_ = leanh::lean_unbox_usize(v_i_8500_);
    leanh::lean_dec(v_i_8500_);
    v_res_8509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_8496_, v_mvarId_8497_, v_as_8498_, v_sz_boxed_8507_, v_i_boxed_8508_, v_b_8501_, v___y_8502_, v___y_8503_, v___y_8504_, v___y_8505_);
    leanh::lean_dec(v___y_8505_);
    leanh::lean_dec_ref(v___y_8504_);
    leanh::lean_dec(v___y_8503_);
    leanh::lean_dec_ref(v___y_8502_);
    leanh::lean_dec_ref(v_as_8498_);
    return v_res_8509_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(
    mut v_p_8510_: *mut leanh::LeanObject,
    mut v_mvarId_8511_: *mut leanh::LeanObject,
    mut v_as_8512_: *mut leanh::LeanObject,
    mut v_sz_8513_: usize,
    mut v_i_8514_: usize,
    mut v_b_8515_: *mut leanh::LeanObject,
    mut v___y_8516_: *mut leanh::LeanObject,
    mut v___y_8517_: *mut leanh::LeanObject,
    mut v___y_8518_: *mut leanh::LeanObject,
    mut v___y_8519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8521_: u8 = 0;
    let mut v___x_8522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8526_: u8 = 0;
    let mut v___x_8527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8532_: usize = 0;
    let mut v___x_8533_: usize = 0;
    let mut v___x_8534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8540_: u8 = 0;
    let mut v___x_8541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8545_: u8 = 0;
    let mut v___x_8546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: u8 = 0;
    let mut v___x_8549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8555_: u8 = 0;
    let mut v___x_8557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8560_: u8 = 0;
    let mut v___x_8561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8569_: u8 = 0;
    let mut v_unused_8570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8572_: u8 = 0;
    let mut v_a_8573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8576_: u8 = 0;
    let mut v___x_8578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8580_: u8 = 0;
    let mut v_a_8581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8584_: u8 = 0;
    let mut v___x_8586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8588_: u8 = 0;
    let mut v_isSharedCheck_8589_: u8 = 0;
    let mut v_isSharedCheck_8590_: u8 = 0;
    let mut v_unused_8591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8521_ = lean_usize_dec_lt(v_i_8514_, v_sz_8513_);
                if v___x_8521_ == 0 {
                    leanh::lean_dec(v_mvarId_8511_);
                    leanh::lean_dec_ref(v_p_8510_);
                    v___x_8522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8522_, 0, v_b_8515_);
                    return v___x_8522_;
                } else {
                    v_snd_8523_ = leanh::lean_ctor_get(v_b_8515_, 1);
                    v_isSharedCheck_8590_ = (!leanh::lean_is_exclusive(v_b_8515_)) as u8;
                    if v_isSharedCheck_8590_ == 0 {
                        v_unused_8591_ = leanh::lean_ctor_get(v_b_8515_, 0);
                        leanh::lean_dec(v_unused_8591_);
                        v___x_8525_ = v_b_8515_;
                        v_isShared_8526_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8523_);
                        leanh::lean_dec(v_b_8515_);
                        v___x_8525_ = leanh::lean_box(0);
                        v_isShared_8526_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8527_ = leanh::lean_box(0);
                v_a_8536_ = lean_array_uget(v_as_8512_, v_i_8514_);
                if leanh::lean_obj_tag(v_a_8536_) == 0 {
                    v_a_8529_ = v_snd_8523_;
                    state = 2;
                    continue;
                } else {
                    v_val_8537_ = leanh::lean_ctor_get(v_a_8536_, 0);
                    v_isSharedCheck_8589_ = (!leanh::lean_is_exclusive(v_a_8536_)) as u8;
                    if v_isSharedCheck_8589_ == 0 {
                        v___x_8539_ = v_a_8536_;
                        v_isShared_8540_ = v_isSharedCheck_8589_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8537_);
                        leanh::lean_dec(v_a_8536_);
                        v___x_8539_ = leanh::lean_box(0);
                        v_isShared_8540_ = v_isSharedCheck_8589_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8526_ == 0 {
                    leanh::lean_ctor_set(v___x_8525_, 1, v_a_8529_);
                    leanh::lean_ctor_set(v___x_8525_, 0, v___x_8527_);
                    v___x_8531_ = v___x_8525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8535_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8535_, 0, v___x_8527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8535_, 1, v_a_8529_);
                    v___x_8531_ = v_reuseFailAlloc_8535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8532_ = 1usize;
                v___x_8533_ = lean_usize_add(v_i_8514_, v___x_8532_);
                v___x_8534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_8510_, v_mvarId_8511_, v_as_8512_, v_sz_8513_, v___x_8533_, v___x_8531_, v___y_8516_, v___y_8517_, v___y_8518_, v___y_8519_);
                return v___x_8534_;
            }
            4 => {
                leanh::lean_inc_ref(v_p_8510_);
                leanh::lean_inc(v___y_8519_);
                leanh::lean_inc_ref(v___y_8518_);
                leanh::lean_inc(v___y_8517_);
                leanh::lean_inc_ref(v___y_8516_);
                leanh::lean_inc(v_val_8537_);
                v___x_8541_ = leanh::lean_apply_6(
                    v_p_8510_,
                    v_val_8537_,
                    v___y_8516_,
                    v___y_8517_,
                    v___y_8518_,
                    v___y_8519_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_8541_) == 0 {
                    v_a_8542_ = leanh::lean_ctor_get(v___x_8541_, 0);
                    leanh::lean_inc(v_a_8542_);
                    leanh::lean_dec_ref_known(v___x_8541_, 1);
                    v___x_8543_ = leanh::lean_box(0);
                    v___x_8544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0;
                    v___x_8545_ = (leanh::lean_unbox(v_a_8542_) as u8);
                    leanh::lean_dec(v_a_8542_);
                    if v___x_8545_ == 0 {
                        leanh::lean_del_object(v___x_8539_);
                        leanh::lean_dec(v_val_8537_);
                        leanh::lean_dec(v_snd_8523_);
                        v_a_8529_ = v___x_8544_;
                        state = 2;
                        continue;
                    } else {
                        v___x_8546_ = l_Lean_LocalDecl_fvarId(v_val_8537_);
                        leanh::lean_dec(v_val_8537_);
                        v___x_8547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1;
                        v___x_8548_ = 0;
                        v___x_8549_ = leanh::lean_box((v___x_8548_) as usize);
                        leanh::lean_inc(v_mvarId_8511_);
                        v___f_8550_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                        leanh::lean_closure_set(v___f_8550_, 0, v_mvarId_8511_);
                        leanh::lean_closure_set(v___f_8550_, 1, v___x_8546_);
                        leanh::lean_closure_set(v___f_8550_, 2, v___x_8547_);
                        leanh::lean_closure_set(v___f_8550_, 3, v___x_8549_);
                        leanh::lean_closure_set(v___f_8550_, 4, v___x_8527_);
                        v___x_8551_ =
                            l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(
                                v___f_8550_,
                                v___y_8516_,
                                v___y_8517_,
                                v___y_8518_,
                                v___y_8519_,
                            );
                        if leanh::lean_obj_tag(v___x_8551_) == 0 {
                            v_a_8552_ = leanh::lean_ctor_get(v___x_8551_, 0);
                            v_isSharedCheck_8572_ =
                                (!leanh::lean_is_exclusive(v___x_8551_)) as u8;
                            if v_isSharedCheck_8572_ == 0 {
                                v___x_8554_ = v___x_8551_;
                                v_isShared_8555_ = v_isSharedCheck_8572_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8552_);
                                leanh::lean_dec(v___x_8551_);
                                v___x_8554_ = leanh::lean_box(0);
                                v_isShared_8555_ = v_isSharedCheck_8572_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8539_);
                            leanh::lean_del_object(v___x_8525_);
                            leanh::lean_dec(v_snd_8523_);
                            leanh::lean_dec(v_mvarId_8511_);
                            leanh::lean_dec_ref(v_p_8510_);
                            v_a_8573_ = leanh::lean_ctor_get(v___x_8551_, 0);
                            v_isSharedCheck_8580_ =
                                (!leanh::lean_is_exclusive(v___x_8551_)) as u8;
                            if v_isSharedCheck_8580_ == 0 {
                                v___x_8575_ = v___x_8551_;
                                v_isShared_8576_ = v_isSharedCheck_8580_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8573_);
                                leanh::lean_dec(v___x_8551_);
                                v___x_8575_ = leanh::lean_box(0);
                                v_isShared_8576_ = v_isSharedCheck_8580_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8539_);
                    leanh::lean_dec(v_val_8537_);
                    leanh::lean_del_object(v___x_8525_);
                    leanh::lean_dec(v_snd_8523_);
                    leanh::lean_dec(v_mvarId_8511_);
                    leanh::lean_dec_ref(v_p_8510_);
                    v_a_8581_ = leanh::lean_ctor_get(v___x_8541_, 0);
                    v_isSharedCheck_8588_ = (!leanh::lean_is_exclusive(v___x_8541_)) as u8;
                    if v_isSharedCheck_8588_ == 0 {
                        v___x_8583_ = v___x_8541_;
                        v_isShared_8584_ = v_isSharedCheck_8588_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8581_);
                        leanh::lean_dec(v___x_8541_);
                        v___x_8583_ = leanh::lean_box(0);
                        v_isShared_8584_ = v_isSharedCheck_8588_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_8552_) == 0 {
                    leanh::lean_del_object(v___x_8554_);
                    leanh::lean_del_object(v___x_8539_);
                    leanh::lean_dec(v_snd_8523_);
                    v_a_8529_ = v___x_8544_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_8525_);
                    leanh::lean_dec(v_mvarId_8511_);
                    leanh::lean_dec_ref(v_p_8510_);
                    leanh::lean_inc_ref(v_a_8552_);
                    if v_isShared_8540_ == 0 {
                        leanh::lean_ctor_set(v___x_8539_, 0, v_a_8552_);
                        v___x_8557_ = v___x_8539_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8571_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8571_, 0, v_a_8552_);
                        v___x_8557_ = v_reuseFailAlloc_8571_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v_isSharedCheck_8569_ = (!leanh::lean_is_exclusive(v_a_8552_)) as u8;
                if v_isSharedCheck_8569_ == 0 {
                    v_unused_8570_ = leanh::lean_ctor_get(v_a_8552_, 0);
                    leanh::lean_dec(v_unused_8570_);
                    v___x_8559_ = v_a_8552_;
                    v_isShared_8560_ = v_isSharedCheck_8569_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_8552_);
                    v___x_8559_ = leanh::lean_box(0);
                    v_isShared_8560_ = v_isSharedCheck_8569_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_8561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8561_, 0, v___x_8557_);
                leanh::lean_ctor_set(v___x_8561_, 1, v___x_8543_);
                if v_isShared_8560_ == 0 {
                    leanh::lean_ctor_set(v___x_8559_, 0, v___x_8561_);
                    v___x_8563_ = v___x_8559_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8568_, 0, v___x_8561_);
                    v___x_8563_ = v_reuseFailAlloc_8568_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8564_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8564_, 0, v___x_8563_);
                leanh::lean_ctor_set(v___x_8564_, 1, v_snd_8523_);
                if v_isShared_8555_ == 0 {
                    leanh::lean_ctor_set(v___x_8554_, 0, v___x_8564_);
                    v___x_8566_ = v___x_8554_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8567_, 0, v___x_8564_);
                    v___x_8566_ = v_reuseFailAlloc_8567_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8566_;
            }
            10 => {
                if v_isShared_8576_ == 0 {
                    v___x_8578_ = v___x_8575_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8579_, 0, v_a_8573_);
                    v___x_8578_ = v_reuseFailAlloc_8579_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8578_;
            }
            12 => {
                if v_isShared_8584_ == 0 {
                    v___x_8586_ = v___x_8583_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8587_, 0, v_a_8581_);
                    v___x_8586_ = v_reuseFailAlloc_8587_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(
    mut v_p_8592_: *mut leanh::LeanObject,
    mut v_mvarId_8593_: *mut leanh::LeanObject,
    mut v_as_8594_: *mut leanh::LeanObject,
    mut v_sz_8595_: *mut leanh::LeanObject,
    mut v_i_8596_: *mut leanh::LeanObject,
    mut v_b_8597_: *mut leanh::LeanObject,
    mut v___y_8598_: *mut leanh::LeanObject,
    mut v___y_8599_: *mut leanh::LeanObject,
    mut v___y_8600_: *mut leanh::LeanObject,
    mut v___y_8601_: *mut leanh::LeanObject,
    mut v___y_8602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8603_: usize = 0;
    let mut v_i_boxed_8604_: usize = 0;
    let mut v_res_8605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8603_ = leanh::lean_unbox_usize(v_sz_8595_);
    leanh::lean_dec(v_sz_8595_);
    v_i_boxed_8604_ = leanh::lean_unbox_usize(v_i_8596_);
    leanh::lean_dec(v_i_8596_);
    v_res_8605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_8592_, v_mvarId_8593_, v_as_8594_, v_sz_boxed_8603_, v_i_boxed_8604_, v_b_8597_, v___y_8598_, v___y_8599_, v___y_8600_, v___y_8601_);
    leanh::lean_dec(v___y_8601_);
    leanh::lean_dec_ref(v___y_8600_);
    leanh::lean_dec(v___y_8599_);
    leanh::lean_dec_ref(v___y_8598_);
    leanh::lean_dec_ref(v_as_8594_);
    return v_res_8605_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(
    mut v_p_8606_: *mut leanh::LeanObject,
    mut v_mvarId_8607_: *mut leanh::LeanObject,
    mut v_t_8608_: *mut leanh::LeanObject,
    mut v_init_8609_: *mut leanh::LeanObject,
    mut v___y_8610_: *mut leanh::LeanObject,
    mut v___y_8611_: *mut leanh::LeanObject,
    mut v___y_8612_: *mut leanh::LeanObject,
    mut v___y_8613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_8615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8621_: u8 = 0;
    let mut v_a_8622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8629_: usize = 0;
    let mut v___x_8630_: usize = 0;
    let mut v___x_8631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8635_: u8 = 0;
    let mut v_fst_8636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8645_: u8 = 0;
    let mut v_a_8646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8649_: u8 = 0;
    let mut v___x_8651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8653_: u8 = 0;
    let mut v_isSharedCheck_8654_: u8 = 0;
    let mut v_a_8655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8658_: u8 = 0;
    let mut v___x_8660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_8615_ = leanh::lean_ctor_get(v_t_8608_, 0);
                v_tail_8616_ = leanh::lean_ctor_get(v_t_8608_, 1);
                leanh::lean_inc(v_mvarId_8607_);
                leanh::lean_inc_ref(v_p_8606_);
                leanh::lean_inc_ref(v_init_8609_);
                v___x_8617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_8609_, v_p_8606_, v_mvarId_8607_, v_root_8615_, v_init_8609_, v___y_8610_, v___y_8611_, v___y_8612_, v___y_8613_);
                leanh::lean_dec_ref(v_init_8609_);
                if leanh::lean_obj_tag(v___x_8617_) == 0 {
                    v_a_8618_ = leanh::lean_ctor_get(v___x_8617_, 0);
                    v_isSharedCheck_8654_ = (!leanh::lean_is_exclusive(v___x_8617_)) as u8;
                    if v_isSharedCheck_8654_ == 0 {
                        v___x_8620_ = v___x_8617_;
                        v_isShared_8621_ = v_isSharedCheck_8654_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8618_);
                        leanh::lean_dec(v___x_8617_);
                        v___x_8620_ = leanh::lean_box(0);
                        v_isShared_8621_ = v_isSharedCheck_8654_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_8607_);
                    leanh::lean_dec_ref(v_p_8606_);
                    v_a_8655_ = leanh::lean_ctor_get(v___x_8617_, 0);
                    v_isSharedCheck_8662_ = (!leanh::lean_is_exclusive(v___x_8617_)) as u8;
                    if v_isSharedCheck_8662_ == 0 {
                        v___x_8657_ = v___x_8617_;
                        v_isShared_8658_ = v_isSharedCheck_8662_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8655_);
                        leanh::lean_dec(v___x_8617_);
                        v___x_8657_ = leanh::lean_box(0);
                        v_isShared_8658_ = v_isSharedCheck_8662_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_8618_) == 0 {
                    leanh::lean_dec(v_mvarId_8607_);
                    leanh::lean_dec_ref(v_p_8606_);
                    v_a_8622_ = leanh::lean_ctor_get(v_a_8618_, 0);
                    leanh::lean_inc(v_a_8622_);
                    leanh::lean_dec_ref_known(v_a_8618_, 1);
                    if v_isShared_8621_ == 0 {
                        leanh::lean_ctor_set(v___x_8620_, 0, v_a_8622_);
                        v___x_8624_ = v___x_8620_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8625_, 0, v_a_8622_);
                        v___x_8624_ = v_reuseFailAlloc_8625_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8620_);
                    v_a_8626_ = leanh::lean_ctor_get(v_a_8618_, 0);
                    leanh::lean_inc(v_a_8626_);
                    leanh::lean_dec_ref_known(v_a_8618_, 1);
                    v___x_8627_ = leanh::lean_box(0);
                    v___x_8628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8628_, 0, v___x_8627_);
                    leanh::lean_ctor_set(v___x_8628_, 1, v_a_8626_);
                    v_sz_8629_ = lean_array_size(v_tail_8616_);
                    v___x_8630_ = 0usize;
                    v___x_8631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_8606_, v_mvarId_8607_, v_tail_8616_, v_sz_8629_, v___x_8630_, v___x_8628_, v___y_8610_, v___y_8611_, v___y_8612_, v___y_8613_);
                    if leanh::lean_obj_tag(v___x_8631_) == 0 {
                        v_a_8632_ = leanh::lean_ctor_get(v___x_8631_, 0);
                        v_isSharedCheck_8645_ =
                            (!leanh::lean_is_exclusive(v___x_8631_)) as u8;
                        if v_isSharedCheck_8645_ == 0 {
                            v___x_8634_ = v___x_8631_;
                            v_isShared_8635_ = v_isSharedCheck_8645_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8632_);
                            leanh::lean_dec(v___x_8631_);
                            v___x_8634_ = leanh::lean_box(0);
                            v_isShared_8635_ = v_isSharedCheck_8645_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_8646_ = leanh::lean_ctor_get(v___x_8631_, 0);
                        v_isSharedCheck_8653_ =
                            (!leanh::lean_is_exclusive(v___x_8631_)) as u8;
                        if v_isSharedCheck_8653_ == 0 {
                            v___x_8648_ = v___x_8631_;
                            v_isShared_8649_ = v_isSharedCheck_8653_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8646_);
                            leanh::lean_dec(v___x_8631_);
                            v___x_8648_ = leanh::lean_box(0);
                            v_isShared_8649_ = v_isSharedCheck_8653_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8624_;
            }
            3 => {
                v_fst_8636_ = leanh::lean_ctor_get(v_a_8632_, 0);
                if leanh::lean_obj_tag(v_fst_8636_) == 0 {
                    v_snd_8637_ = leanh::lean_ctor_get(v_a_8632_, 1);
                    leanh::lean_inc(v_snd_8637_);
                    leanh::lean_dec(v_a_8632_);
                    if v_isShared_8635_ == 0 {
                        leanh::lean_ctor_set(v___x_8634_, 0, v_snd_8637_);
                        v___x_8639_ = v___x_8634_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8640_, 0, v_snd_8637_);
                        v___x_8639_ = v_reuseFailAlloc_8640_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_8636_);
                    leanh::lean_dec(v_a_8632_);
                    v_val_8641_ = leanh::lean_ctor_get(v_fst_8636_, 0);
                    leanh::lean_inc(v_val_8641_);
                    leanh::lean_dec_ref_known(v_fst_8636_, 1);
                    if v_isShared_8635_ == 0 {
                        leanh::lean_ctor_set(v___x_8634_, 0, v_val_8641_);
                        v___x_8643_ = v___x_8634_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8644_, 0, v_val_8641_);
                        v___x_8643_ = v_reuseFailAlloc_8644_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_8639_;
            }
            5 => {
                return v___x_8643_;
            }
            6 => {
                if v_isShared_8649_ == 0 {
                    v___x_8651_ = v___x_8648_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8652_, 0, v_a_8646_);
                    v___x_8651_ = v_reuseFailAlloc_8652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8651_;
            }
            8 => {
                if v_isShared_8658_ == 0 {
                    v___x_8660_ = v___x_8657_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8661_, 0, v_a_8655_);
                    v___x_8660_ = v_reuseFailAlloc_8661_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(
    mut v_p_8663_: *mut leanh::LeanObject,
    mut v_mvarId_8664_: *mut leanh::LeanObject,
    mut v_t_8665_: *mut leanh::LeanObject,
    mut v_init_8666_: *mut leanh::LeanObject,
    mut v___y_8667_: *mut leanh::LeanObject,
    mut v___y_8668_: *mut leanh::LeanObject,
    mut v___y_8669_: *mut leanh::LeanObject,
    mut v___y_8670_: *mut leanh::LeanObject,
    mut v___y_8671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8672_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(
        v_p_8663_,
        v_mvarId_8664_,
        v_t_8665_,
        v_init_8666_,
        v___y_8667_,
        v___y_8668_,
        v___y_8669_,
        v___y_8670_,
    );
    leanh::lean_dec(v___y_8670_);
    leanh::lean_dec_ref(v___y_8669_);
    leanh::lean_dec(v___y_8668_);
    leanh::lean_dec_ref(v___y_8667_);
    leanh::lean_dec_ref(v_t_8665_);
    return v_res_8672_;
}
pub unsafe fn l_Lean_MVarId_casesRec___lam__0(
    mut v_p_8676_: *mut leanh::LeanObject,
    mut v_mvarId_8677_: *mut leanh::LeanObject,
    mut v___y_8678_: *mut leanh::LeanObject,
    mut v___y_8679_: *mut leanh::LeanObject,
    mut v___y_8680_: *mut leanh::LeanObject,
    mut v___y_8681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_8683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_8684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8691_: u8 = 0;
    let mut v_fst_8692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8700_: u8 = 0;
    let mut v_a_8701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8704_: u8 = 0;
    let mut v___x_8706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_8683_ = leanh::lean_ctor_get(v___y_8678_, 2);
                v_decls_8684_ = leanh::lean_ctor_get(v_lctx_8683_, 1);
                v___x_8685_ = leanh::lean_box(0);
                v___x_8686_ = l_Lean_MVarId_casesRec___lam__0___closed__0;
                v___x_8687_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(
                    v_p_8676_,
                    v_mvarId_8677_,
                    v_decls_8684_,
                    v___x_8686_,
                    v___y_8678_,
                    v___y_8679_,
                    v___y_8680_,
                    v___y_8681_,
                );
                if leanh::lean_obj_tag(v___x_8687_) == 0 {
                    v_a_8688_ = leanh::lean_ctor_get(v___x_8687_, 0);
                    v_isSharedCheck_8700_ = (!leanh::lean_is_exclusive(v___x_8687_)) as u8;
                    if v_isSharedCheck_8700_ == 0 {
                        v___x_8690_ = v___x_8687_;
                        v_isShared_8691_ = v_isSharedCheck_8700_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8688_);
                        leanh::lean_dec(v___x_8687_);
                        v___x_8690_ = leanh::lean_box(0);
                        v_isShared_8691_ = v_isSharedCheck_8700_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8701_ = leanh::lean_ctor_get(v___x_8687_, 0);
                    v_isSharedCheck_8708_ = (!leanh::lean_is_exclusive(v___x_8687_)) as u8;
                    if v_isSharedCheck_8708_ == 0 {
                        v___x_8703_ = v___x_8687_;
                        v_isShared_8704_ = v_isSharedCheck_8708_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8701_);
                        leanh::lean_dec(v___x_8687_);
                        v___x_8703_ = leanh::lean_box(0);
                        v_isShared_8704_ = v_isSharedCheck_8708_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8692_ = leanh::lean_ctor_get(v_a_8688_, 0);
                leanh::lean_inc(v_fst_8692_);
                leanh::lean_dec(v_a_8688_);
                if leanh::lean_obj_tag(v_fst_8692_) == 0 {
                    if v_isShared_8691_ == 0 {
                        leanh::lean_ctor_set(v___x_8690_, 0, v___x_8685_);
                        v___x_8694_ = v___x_8690_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8695_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8695_, 0, v___x_8685_);
                        v___x_8694_ = v_reuseFailAlloc_8695_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_8696_ = leanh::lean_ctor_get(v_fst_8692_, 0);
                    leanh::lean_inc(v_val_8696_);
                    leanh::lean_dec_ref_known(v_fst_8692_, 1);
                    if v_isShared_8691_ == 0 {
                        leanh::lean_ctor_set(v___x_8690_, 0, v_val_8696_);
                        v___x_8698_ = v___x_8690_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8699_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8699_, 0, v_val_8696_);
                        v___x_8698_ = v_reuseFailAlloc_8699_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8694_;
            }
            3 => {
                return v___x_8698_;
            }
            4 => {
                if v_isShared_8704_ == 0 {
                    v___x_8706_ = v___x_8703_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8707_, 0, v_a_8701_);
                    v___x_8706_ = v_reuseFailAlloc_8707_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_casesRec___lam__0___boxed(
    mut v_p_8709_: *mut leanh::LeanObject,
    mut v_mvarId_8710_: *mut leanh::LeanObject,
    mut v___y_8711_: *mut leanh::LeanObject,
    mut v___y_8712_: *mut leanh::LeanObject,
    mut v___y_8713_: *mut leanh::LeanObject,
    mut v___y_8714_: *mut leanh::LeanObject,
    mut v___y_8715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8716_ = l_Lean_MVarId_casesRec___lam__0(
        v_p_8709_,
        v_mvarId_8710_,
        v___y_8711_,
        v___y_8712_,
        v___y_8713_,
        v___y_8714_,
    );
    leanh::lean_dec(v___y_8714_);
    leanh::lean_dec_ref(v___y_8713_);
    leanh::lean_dec(v___y_8712_);
    leanh::lean_dec_ref(v___y_8711_);
    return v_res_8716_;
}
pub unsafe fn l_Lean_MVarId_casesRec___lam__1(
    mut v_p_8717_: *mut leanh::LeanObject,
    mut v_mvarId_8718_: *mut leanh::LeanObject,
    mut v___y_8719_: *mut leanh::LeanObject,
    mut v___y_8720_: *mut leanh::LeanObject,
    mut v___y_8721_: *mut leanh::LeanObject,
    mut v___y_8722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_8718_);
    v___f_8724_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_casesRec___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_8724_, 0, v_p_8717_);
    leanh::lean_closure_set(v___f_8724_, 1, v_mvarId_8718_);
    v___x_8725_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(
        v_mvarId_8718_,
        v___f_8724_,
        v___y_8719_,
        v___y_8720_,
        v___y_8721_,
        v___y_8722_,
    );
    return v___x_8725_;
}
pub unsafe fn l_Lean_MVarId_casesRec___lam__1___boxed(
    mut v_p_8726_: *mut leanh::LeanObject,
    mut v_mvarId_8727_: *mut leanh::LeanObject,
    mut v___y_8728_: *mut leanh::LeanObject,
    mut v___y_8729_: *mut leanh::LeanObject,
    mut v___y_8730_: *mut leanh::LeanObject,
    mut v___y_8731_: *mut leanh::LeanObject,
    mut v___y_8732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8733_ = l_Lean_MVarId_casesRec___lam__1(
        v_p_8726_,
        v_mvarId_8727_,
        v___y_8728_,
        v___y_8729_,
        v___y_8730_,
        v___y_8731_,
    );
    leanh::lean_dec(v___y_8731_);
    leanh::lean_dec_ref(v___y_8730_);
    leanh::lean_dec(v___y_8729_);
    leanh::lean_dec_ref(v___y_8728_);
    return v_res_8733_;
}
pub unsafe fn l_Lean_MVarId_casesRec(
    mut v_mvarId_8734_: *mut leanh::LeanObject,
    mut v_p_8735_: *mut leanh::LeanObject,
    mut v_a_8736_: *mut leanh::LeanObject,
    mut v_a_8737_: *mut leanh::LeanObject,
    mut v_a_8738_: *mut leanh::LeanObject,
    mut v_a_8739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8741_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_casesRec___lam__1___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_8741_, 0, v_p_8735_);
    v___x_8742_ = l_Lean_Meta_saturate(
        v_mvarId_8734_,
        v___f_8741_,
        v_a_8736_,
        v_a_8737_,
        v_a_8738_,
        v_a_8739_,
    );
    return v___x_8742_;
}
pub unsafe fn l_Lean_MVarId_casesRec___boxed(
    mut v_mvarId_8743_: *mut leanh::LeanObject,
    mut v_p_8744_: *mut leanh::LeanObject,
    mut v_a_8745_: *mut leanh::LeanObject,
    mut v_a_8746_: *mut leanh::LeanObject,
    mut v_a_8747_: *mut leanh::LeanObject,
    mut v_a_8748_: *mut leanh::LeanObject,
    mut v_a_8749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8750_ = l_Lean_MVarId_casesRec(
        v_mvarId_8743_,
        v_p_8744_,
        v_a_8745_,
        v_a_8746_,
        v_a_8747_,
        v_a_8748_,
    );
    leanh::lean_dec(v_a_8748_);
    leanh::lean_dec_ref(v_a_8747_);
    leanh::lean_dec(v_a_8746_);
    leanh::lean_dec_ref(v_a_8745_);
    return v_res_8750_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(
    mut v_e_8751_: *mut leanh::LeanObject,
    mut v___y_8752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8754_: u8 = 0;
    let mut v___x_8755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_8762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_8764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8768_: u8 = 0;
    let mut v___x_8770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8774_: u8 = 0;
    let mut v_unused_8775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8754_ = l_Lean_Expr_hasMVar(v_e_8751_);
                if v___x_8754_ == 0 {
                    v___x_8755_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8755_, 0, v_e_8751_);
                    return v___x_8755_;
                } else {
                    v___x_8756_ = lean_st_ref_get(v___y_8752_);
                    v_mctx_8757_ = leanh::lean_ctor_get(v___x_8756_, 0);
                    leanh::lean_inc_ref(v_mctx_8757_);
                    leanh::lean_dec(v___x_8756_);
                    v___x_8758_ = l_Lean_instantiateMVarsCore(v_mctx_8757_, v_e_8751_);
                    v_fst_8759_ = leanh::lean_ctor_get(v___x_8758_, 0);
                    leanh::lean_inc(v_fst_8759_);
                    v_snd_8760_ = leanh::lean_ctor_get(v___x_8758_, 1);
                    leanh::lean_inc(v_snd_8760_);
                    leanh::lean_dec_ref(v___x_8758_);
                    v___x_8761_ = lean_st_ref_take(v___y_8752_);
                    v_cache_8762_ = leanh::lean_ctor_get(v___x_8761_, 1);
                    v_zetaDeltaFVarIds_8763_ = leanh::lean_ctor_get(v___x_8761_, 2);
                    v_postponed_8764_ = leanh::lean_ctor_get(v___x_8761_, 3);
                    v_diag_8765_ = leanh::lean_ctor_get(v___x_8761_, 4);
                    v_isSharedCheck_8774_ = (!leanh::lean_is_exclusive(v___x_8761_)) as u8;
                    if v_isSharedCheck_8774_ == 0 {
                        v_unused_8775_ = leanh::lean_ctor_get(v___x_8761_, 0);
                        leanh::lean_dec(v_unused_8775_);
                        v___x_8767_ = v___x_8761_;
                        v_isShared_8768_ = v_isSharedCheck_8774_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_8765_);
                        leanh::lean_inc(v_postponed_8764_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_8763_);
                        leanh::lean_inc(v_cache_8762_);
                        leanh::lean_dec(v___x_8761_);
                        v___x_8767_ = leanh::lean_box(0);
                        v_isShared_8768_ = v_isSharedCheck_8774_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8768_ == 0 {
                    leanh::lean_ctor_set(v___x_8767_, 0, v_snd_8760_);
                    v___x_8770_ = v___x_8767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8773_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 0, v_snd_8760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 1, v_cache_8762_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_8773_,
                        2,
                        v_zetaDeltaFVarIds_8763_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 3, v_postponed_8764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8773_, 4, v_diag_8765_);
                    v___x_8770_ = v_reuseFailAlloc_8773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8771_ = lean_st_ref_set(v___y_8752_, v___x_8770_);
                v___x_8772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8772_, 0, v_fst_8759_);
                return v___x_8772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(
    mut v_e_8776_: *mut leanh::LeanObject,
    mut v___y_8777_: *mut leanh::LeanObject,
    mut v___y_8778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8779_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(
        v_e_8776_,
        v___y_8777_,
    );
    leanh::lean_dec(v___y_8777_);
    return v_res_8779_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(
    mut v_e_8780_: *mut leanh::LeanObject,
    mut v___y_8781_: *mut leanh::LeanObject,
    mut v___y_8782_: *mut leanh::LeanObject,
    mut v___y_8783_: *mut leanh::LeanObject,
    mut v___y_8784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8786_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(
        v_e_8780_,
        v___y_8782_,
    );
    return v___x_8786_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(
    mut v_e_8787_: *mut leanh::LeanObject,
    mut v___y_8788_: *mut leanh::LeanObject,
    mut v___y_8789_: *mut leanh::LeanObject,
    mut v___y_8790_: *mut leanh::LeanObject,
    mut v___y_8791_: *mut leanh::LeanObject,
    mut v___y_8792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8793_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(
        v_e_8787_,
        v___y_8788_,
        v___y_8789_,
        v___y_8790_,
        v___y_8791_,
    );
    leanh::lean_dec(v___y_8791_);
    leanh::lean_dec_ref(v___y_8790_);
    leanh::lean_dec(v___y_8789_);
    leanh::lean_dec_ref(v___y_8788_);
    return v_res_8793_;
}
pub unsafe fn l_Lean_MVarId_casesAnd___lam__0(
    mut v_localDecl_8797_: *mut leanh::LeanObject,
    mut v___y_8798_: *mut leanh::LeanObject,
    mut v___y_8799_: *mut leanh::LeanObject,
    mut v___y_8800_: *mut leanh::LeanObject,
    mut v___y_8801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8808_: u8 = 0;
    let mut v___x_8809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8811_: u8 = 0;
    let mut v___x_8812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8803_ = l_Lean_LocalDecl_type(v_localDecl_8797_);
                v___x_8804_ =
                    l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(
                        v___x_8803_,
                        v___y_8799_,
                    );
                v_a_8805_ = leanh::lean_ctor_get(v___x_8804_, 0);
                v_isSharedCheck_8816_ = (!leanh::lean_is_exclusive(v___x_8804_)) as u8;
                if v_isSharedCheck_8816_ == 0 {
                    v___x_8807_ = v___x_8804_;
                    v_isShared_8808_ = v_isSharedCheck_8816_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8805_);
                    leanh::lean_dec(v___x_8804_);
                    v___x_8807_ = leanh::lean_box(0);
                    v_isShared_8808_ = v_isSharedCheck_8816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8809_ = l_Lean_MVarId_casesAnd___lam__0___closed__1;
                v___x_8810_ = leanh::lean_unsigned_to_nat(2);
                v___x_8811_ = l_Lean_Expr_isAppOfArity(v_a_8805_, v___x_8809_, v___x_8810_);
                leanh::lean_dec(v_a_8805_);
                v___x_8812_ = leanh::lean_box((v___x_8811_) as usize);
                if v_isShared_8808_ == 0 {
                    leanh::lean_ctor_set(v___x_8807_, 0, v___x_8812_);
                    v___x_8814_ = v___x_8807_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8815_, 0, v___x_8812_);
                    v___x_8814_ = v_reuseFailAlloc_8815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_casesAnd___lam__0___boxed(
    mut v_localDecl_8817_: *mut leanh::LeanObject,
    mut v___y_8818_: *mut leanh::LeanObject,
    mut v___y_8819_: *mut leanh::LeanObject,
    mut v___y_8820_: *mut leanh::LeanObject,
    mut v___y_8821_: *mut leanh::LeanObject,
    mut v___y_8822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8823_ = l_Lean_MVarId_casesAnd___lam__0(
        v_localDecl_8817_,
        v___y_8818_,
        v___y_8819_,
        v___y_8820_,
        v___y_8821_,
    );
    leanh::lean_dec(v___y_8821_);
    leanh::lean_dec_ref(v___y_8820_);
    leanh::lean_dec(v___y_8819_);
    leanh::lean_dec_ref(v___y_8818_);
    leanh::lean_dec_ref(v_localDecl_8817_);
    return v_res_8823_;
}
pub unsafe fn _init_l_Lean_MVarId_casesAnd___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_8828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8828_ = l_Lean_MVarId_casesAnd___closed__2;
    v___x_8829_ = l_Lean_MessageData_ofFormat(v___x_8828_);
    return v___x_8829_;
}
pub unsafe fn l_Lean_MVarId_casesAnd(
    mut v_mvarId_8830_: *mut leanh::LeanObject,
    mut v_a_8831_: *mut leanh::LeanObject,
    mut v_a_8832_: *mut leanh::LeanObject,
    mut v_a_8833_: *mut leanh::LeanObject,
    mut v_a_8834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8844_: u8 = 0;
    let mut v___x_8846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8836_ = l_Lean_MVarId_casesAnd___closed__0;
                v___x_8837_ = l_Lean_MVarId_casesRec(
                    v_mvarId_8830_,
                    v___f_8836_,
                    v_a_8831_,
                    v_a_8832_,
                    v_a_8833_,
                    v_a_8834_,
                );
                if leanh::lean_obj_tag(v___x_8837_) == 0 {
                    v_a_8838_ = leanh::lean_ctor_get(v___x_8837_, 0);
                    leanh::lean_inc(v_a_8838_);
                    leanh::lean_dec_ref_known(v___x_8837_, 1);
                    v___x_8839_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_casesAnd___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_casesAnd___closed__3_once),
                        _init_l_Lean_MVarId_casesAnd___closed__3,
                    );
                    v___x_8840_ = l_Lean_Meta_exactlyOne(
                        v_a_8838_,
                        v___x_8839_,
                        v_a_8831_,
                        v_a_8832_,
                        v_a_8833_,
                        v_a_8834_,
                    );
                    leanh::lean_dec(v_a_8838_);
                    return v___x_8840_;
                } else {
                    v_a_8841_ = leanh::lean_ctor_get(v___x_8837_, 0);
                    v_isSharedCheck_8848_ = (!leanh::lean_is_exclusive(v___x_8837_)) as u8;
                    if v_isSharedCheck_8848_ == 0 {
                        v___x_8843_ = v___x_8837_;
                        v_isShared_8844_ = v_isSharedCheck_8848_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8841_);
                        leanh::lean_dec(v___x_8837_);
                        v___x_8843_ = leanh::lean_box(0);
                        v_isShared_8844_ = v_isSharedCheck_8848_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8844_ == 0 {
                    v___x_8846_ = v___x_8843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8847_, 0, v_a_8841_);
                    v___x_8846_ = v_reuseFailAlloc_8847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_casesAnd___boxed(
    mut v_mvarId_8849_: *mut leanh::LeanObject,
    mut v_a_8850_: *mut leanh::LeanObject,
    mut v_a_8851_: *mut leanh::LeanObject,
    mut v_a_8852_: *mut leanh::LeanObject,
    mut v_a_8853_: *mut leanh::LeanObject,
    mut v_a_8854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8855_ =
        l_Lean_MVarId_casesAnd(v_mvarId_8849_, v_a_8850_, v_a_8851_, v_a_8852_, v_a_8853_);
    leanh::lean_dec(v_a_8853_);
    leanh::lean_dec_ref(v_a_8852_);
    leanh::lean_dec(v_a_8851_);
    leanh::lean_dec_ref(v_a_8850_);
    return v_res_8855_;
}
pub unsafe fn l_Lean_MVarId_substEqs___lam__0(
    mut v_localDecl_8856_: *mut leanh::LeanObject,
    mut v___y_8857_: *mut leanh::LeanObject,
    mut v___y_8858_: *mut leanh::LeanObject,
    mut v___y_8859_: *mut leanh::LeanObject,
    mut v___y_8860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8867_: u8 = 0;
    let mut v___x_8868_: u8 = 0;
    let mut v___x_8869_: u8 = 0;
    let mut v___x_8870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8862_ = l_Lean_LocalDecl_type(v_localDecl_8856_);
                v___x_8863_ =
                    l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(
                        v___x_8862_,
                        v___y_8858_,
                    );
                v_a_8864_ = leanh::lean_ctor_get(v___x_8863_, 0);
                v_isSharedCheck_8878_ = (!leanh::lean_is_exclusive(v___x_8863_)) as u8;
                if v_isSharedCheck_8878_ == 0 {
                    v___x_8866_ = v___x_8863_;
                    v_isShared_8867_ = v_isSharedCheck_8878_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_8864_);
                    leanh::lean_dec(v___x_8863_);
                    v___x_8866_ = leanh::lean_box(0);
                    v_isShared_8867_ = v_isSharedCheck_8878_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8868_ = l_Lean_Expr_isEq(v_a_8864_);
                if v___x_8868_ == 0 {
                    v___x_8869_ = l_Lean_Expr_isHEq(v_a_8864_);
                    leanh::lean_dec(v_a_8864_);
                    v___x_8870_ = leanh::lean_box((v___x_8869_) as usize);
                    if v_isShared_8867_ == 0 {
                        leanh::lean_ctor_set(v___x_8866_, 0, v___x_8870_);
                        v___x_8872_ = v___x_8866_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8873_, 0, v___x_8870_);
                        v___x_8872_ = v_reuseFailAlloc_8873_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8864_);
                    v___x_8874_ = leanh::lean_box((v___x_8868_) as usize);
                    if v_isShared_8867_ == 0 {
                        leanh::lean_ctor_set(v___x_8866_, 0, v___x_8874_);
                        v___x_8876_ = v___x_8866_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8877_, 0, v___x_8874_);
                        v___x_8876_ = v_reuseFailAlloc_8877_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8872_;
            }
            3 => {
                return v___x_8876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_substEqs___lam__0___boxed(
    mut v_localDecl_8879_: *mut leanh::LeanObject,
    mut v___y_8880_: *mut leanh::LeanObject,
    mut v___y_8881_: *mut leanh::LeanObject,
    mut v___y_8882_: *mut leanh::LeanObject,
    mut v___y_8883_: *mut leanh::LeanObject,
    mut v___y_8884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8885_ = l_Lean_MVarId_substEqs___lam__0(
        v_localDecl_8879_,
        v___y_8880_,
        v___y_8881_,
        v___y_8882_,
        v___y_8883_,
    );
    leanh::lean_dec(v___y_8883_);
    leanh::lean_dec_ref(v___y_8882_);
    leanh::lean_dec(v___y_8881_);
    leanh::lean_dec_ref(v___y_8880_);
    leanh::lean_dec_ref(v_localDecl_8879_);
    return v_res_8885_;
}
pub unsafe fn l_Lean_MVarId_substEqs(
    mut v_mvarId_8887_: *mut leanh::LeanObject,
    mut v_a_8888_: *mut leanh::LeanObject,
    mut v_a_8889_: *mut leanh::LeanObject,
    mut v_a_8890_: *mut leanh::LeanObject,
    mut v_a_8891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8901_: u8 = 0;
    let mut v___x_8903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8893_ = l_Lean_MVarId_substEqs___closed__0;
                v___x_8894_ = l_Lean_MVarId_casesRec(
                    v_mvarId_8887_,
                    v___f_8893_,
                    v_a_8888_,
                    v_a_8889_,
                    v_a_8890_,
                    v_a_8891_,
                );
                if leanh::lean_obj_tag(v___x_8894_) == 0 {
                    v_a_8895_ = leanh::lean_ctor_get(v___x_8894_, 0);
                    leanh::lean_inc(v_a_8895_);
                    leanh::lean_dec_ref_known(v___x_8894_, 1);
                    v___x_8896_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_casesAnd___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_casesAnd___closed__3_once),
                        _init_l_Lean_MVarId_casesAnd___closed__3,
                    );
                    v___x_8897_ = l_Lean_Meta_ensureAtMostOne(
                        v_a_8895_,
                        v___x_8896_,
                        v_a_8888_,
                        v_a_8889_,
                        v_a_8890_,
                        v_a_8891_,
                    );
                    leanh::lean_dec(v_a_8895_);
                    return v___x_8897_;
                } else {
                    v_a_8898_ = leanh::lean_ctor_get(v___x_8894_, 0);
                    v_isSharedCheck_8905_ = (!leanh::lean_is_exclusive(v___x_8894_)) as u8;
                    if v_isSharedCheck_8905_ == 0 {
                        v___x_8900_ = v___x_8894_;
                        v_isShared_8901_ = v_isSharedCheck_8905_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8898_);
                        leanh::lean_dec(v___x_8894_);
                        v___x_8900_ = leanh::lean_box(0);
                        v_isShared_8901_ = v_isSharedCheck_8905_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8901_ == 0 {
                    v___x_8903_ = v___x_8900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8904_, 0, v_a_8898_);
                    v___x_8903_ = v_reuseFailAlloc_8904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_substEqs___boxed(
    mut v_mvarId_8906_: *mut leanh::LeanObject,
    mut v_a_8907_: *mut leanh::LeanObject,
    mut v_a_8908_: *mut leanh::LeanObject,
    mut v_a_8909_: *mut leanh::LeanObject,
    mut v_a_8910_: *mut leanh::LeanObject,
    mut v_a_8911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8912_ =
        l_Lean_MVarId_substEqs(v_mvarId_8906_, v_a_8907_, v_a_8908_, v_a_8909_, v_a_8910_);
    leanh::lean_dec(v_a_8910_);
    leanh::lean_dec_ref(v_a_8909_);
    leanh::lean_dec(v_a_8908_);
    leanh::lean_dec_ref(v_a_8907_);
    return v_res_8912_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8914_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0;
    v___x_8915_ = l_Lean_stringToMessageData(v___x_8914_);
    return v___x_8915_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
    mut v_s_8916_: *mut leanh::LeanObject,
    mut v_a_8917_: *mut leanh::LeanObject,
    mut v_a_8918_: *mut leanh::LeanObject,
    mut v_a_8919_: *mut leanh::LeanObject,
    mut v_a_8920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_8929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8932_: u8 = 0;
    let mut v_mvarId_8933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_8934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8937_: u8 = 0;
    let mut v___x_8938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8945_: u8 = 0;
    let mut v_unused_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInductionSubgoal_8929_ = leanh::lean_ctor_get(v_s_8916_, 0);
                v_isSharedCheck_8945_ = (!leanh::lean_is_exclusive(v_s_8916_)) as u8;
                if v_isSharedCheck_8945_ == 0 {
                    v_unused_8946_ = leanh::lean_ctor_get(v_s_8916_, 1);
                    leanh::lean_dec(v_unused_8946_);
                    v___x_8931_ = v_s_8916_;
                    v_isShared_8932_ = v_isSharedCheck_8945_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toInductionSubgoal_8929_);
                    leanh::lean_dec(v_s_8916_);
                    v___x_8931_ = leanh::lean_box(0);
                    v_isShared_8932_ = v_isSharedCheck_8945_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
                v___x_8928_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_8927_, v___y_8923_, v___y_8924_, v___y_8925_, v___y_8926_);
                return v___x_8928_;
            }
            2 => {
                v_mvarId_8933_ = leanh::lean_ctor_get(v_toInductionSubgoal_8929_, 0);
                leanh::lean_inc(v_mvarId_8933_);
                v_fields_8934_ = leanh::lean_ctor_get(v_toInductionSubgoal_8929_, 1);
                leanh::lean_inc_ref(v_fields_8934_);
                leanh::lean_dec_ref(v_toInductionSubgoal_8929_);
                v___x_8935_ = lean_array_get_size(v_fields_8934_);
                v___x_8936_ = leanh::lean_unsigned_to_nat(1);
                v___x_8937_ = lean_nat_dec_eq(v___x_8935_, v___x_8936_);
                if v___x_8937_ == 0 {
                    leanh::lean_dec_ref(v_fields_8934_);
                    leanh::lean_dec(v_mvarId_8933_);
                    leanh::lean_del_object(v___x_8931_);
                    v___y_8923_ = v_a_8917_;
                    v___y_8924_ = v_a_8918_;
                    v___y_8925_ = v_a_8919_;
                    v___y_8926_ = v_a_8920_;
                    state = 1;
                    continue;
                } else {
                    v___x_8938_ = leanh::lean_unsigned_to_nat(0);
                    v___x_8939_ = lean_array_fget(v_fields_8934_, v___x_8938_);
                    leanh::lean_dec_ref(v_fields_8934_);
                    if leanh::lean_obj_tag(v___x_8939_) == 1 {
                        v_fvarId_8940_ = leanh::lean_ctor_get(v___x_8939_, 0);
                        leanh::lean_inc(v_fvarId_8940_);
                        leanh::lean_dec_ref_known(v___x_8939_, 1);
                        if v_isShared_8932_ == 0 {
                            leanh::lean_ctor_set(v___x_8931_, 1, v_fvarId_8940_);
                            leanh::lean_ctor_set(v___x_8931_, 0, v_mvarId_8933_);
                            v___x_8942_ = v___x_8931_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8944_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8944_, 0, v_mvarId_8933_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8944_, 1, v_fvarId_8940_);
                            v___x_8942_ = v_reuseFailAlloc_8944_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_8939_);
                        leanh::lean_dec(v_mvarId_8933_);
                        leanh::lean_del_object(v___x_8931_);
                        v___y_8923_ = v_a_8917_;
                        v___y_8924_ = v_a_8918_;
                        v___y_8925_ = v_a_8919_;
                        v___y_8926_ = v_a_8920_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_8943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8943_, 0, v___x_8942_);
                return v___x_8943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(
    mut v_s_8947_: *mut leanh::LeanObject,
    mut v_a_8948_: *mut leanh::LeanObject,
    mut v_a_8949_: *mut leanh::LeanObject,
    mut v_a_8950_: *mut leanh::LeanObject,
    mut v_a_8951_: *mut leanh::LeanObject,
    mut v_a_8952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8953_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
        v_s_8947_, v_a_8948_, v_a_8949_, v_a_8950_, v_a_8951_,
    );
    leanh::lean_dec(v_a_8951_);
    leanh::lean_dec_ref(v_a_8950_);
    leanh::lean_dec(v_a_8949_);
    leanh::lean_dec_ref(v_a_8948_);
    return v_res_8953_;
}
pub unsafe fn _init_l_Lean_MVarId_byCases___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_8958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8958_ = l_Lean_MVarId_byCases___closed__2;
    v___x_8959_ = l_Lean_stringToMessageData(v___x_8958_);
    return v___x_8959_;
}
pub unsafe fn _init_l_Lean_MVarId_byCases___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_8961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8961_ = l_Lean_MVarId_byCases___closed__4;
    v___x_8962_ = l_Lean_stringToMessageData(v___x_8961_);
    return v___x_8962_;
}
pub unsafe fn l_Lean_MVarId_byCases(
    mut v_mvarId_8963_: *mut leanh::LeanObject,
    mut v_p_8964_: *mut leanh::LeanObject,
    mut v_hName_8965_: *mut leanh::LeanObject,
    mut v_a_8966_: *mut leanh::LeanObject,
    mut v_a_8967_: *mut leanh::LeanObject,
    mut v_a_8968_: *mut leanh::LeanObject,
    mut v_a_8969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8977_: u8 = 0;
    let mut v___x_8978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8984_: u8 = 0;
    let mut v___x_8985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8996_: u8 = 0;
    let mut v___x_8997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9014_: u8 = 0;
    let mut v___x_9016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9021_: u8 = 0;
    let mut v_a_9022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9025_: u8 = 0;
    let mut v___x_9027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9029_: u8 = 0;
    let mut v_a_9030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9033_: u8 = 0;
    let mut v___x_9035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9037_: u8 = 0;
    let mut v_a_9038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9041_: u8 = 0;
    let mut v___x_9043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9045_: u8 = 0;
    let mut v_isSharedCheck_9046_: u8 = 0;
    let mut v_a_9047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9050_: u8 = 0;
    let mut v___x_9052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9054_: u8 = 0;
    let mut v_a_9055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9058_: u8 = 0;
    let mut v___x_9060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8971_ = l_Lean_MVarId_byCases___closed__1;
                leanh::lean_inc_ref_n(v_p_8964_, 3);
                v___x_8972_ = l_Lean_mkNot(v_p_8964_);
                v___x_8973_ = l_Lean_mkOr(v_p_8964_, v___x_8972_);
                v___x_8974_ = l_Lean_mkEM(v_p_8964_);
                v___x_8975_ = l_Lean_MVarId_assert(
                    v_mvarId_8963_,
                    v___x_8971_,
                    v___x_8973_,
                    v___x_8974_,
                    v_a_8966_,
                    v_a_8967_,
                    v_a_8968_,
                    v_a_8969_,
                );
                if leanh::lean_obj_tag(v___x_8975_) == 0 {
                    v_a_8976_ = leanh::lean_ctor_get(v___x_8975_, 0);
                    leanh::lean_inc(v_a_8976_);
                    leanh::lean_dec_ref_known(v___x_8975_, 1);
                    v___x_8977_ = 0;
                    v___x_8978_ = l_Lean_Meta_intro1Core(
                        v_a_8976_,
                        v___x_8977_,
                        v_a_8966_,
                        v_a_8967_,
                        v_a_8968_,
                        v_a_8969_,
                    );
                    if leanh::lean_obj_tag(v___x_8978_) == 0 {
                        v_a_8979_ = leanh::lean_ctor_get(v___x_8978_, 0);
                        leanh::lean_inc(v_a_8979_);
                        leanh::lean_dec_ref_known(v___x_8978_, 1);
                        v_fst_8980_ = leanh::lean_ctor_get(v_a_8979_, 0);
                        v_snd_8981_ = leanh::lean_ctor_get(v_a_8979_, 1);
                        v_isSharedCheck_9046_ = (!leanh::lean_is_exclusive(v_a_8979_)) as u8;
                        if v_isSharedCheck_9046_ == 0 {
                            v___x_8983_ = v_a_8979_;
                            v_isShared_8984_ = v_isSharedCheck_9046_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_8981_);
                            leanh::lean_inc(v_fst_8980_);
                            leanh::lean_dec(v_a_8979_);
                            v___x_8983_ = leanh::lean_box(0);
                            v_isShared_8984_ = v_isSharedCheck_9046_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_hName_8965_);
                        leanh::lean_dec_ref(v_p_8964_);
                        v_a_9047_ = leanh::lean_ctor_get(v___x_8978_, 0);
                        v_isSharedCheck_9054_ =
                            (!leanh::lean_is_exclusive(v___x_8978_)) as u8;
                        if v_isSharedCheck_9054_ == 0 {
                            v___x_9049_ = v___x_8978_;
                            v_isShared_9050_ = v_isSharedCheck_9054_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9047_);
                            leanh::lean_dec(v___x_8978_);
                            v___x_9049_ = leanh::lean_box(0);
                            v_isShared_9050_ = v_isSharedCheck_9054_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_hName_8965_);
                    leanh::lean_dec_ref(v_p_8964_);
                    v_a_9055_ = leanh::lean_ctor_get(v___x_8975_, 0);
                    v_isSharedCheck_9062_ = (!leanh::lean_is_exclusive(v___x_8975_)) as u8;
                    if v_isSharedCheck_9062_ == 0 {
                        v___x_9057_ = v___x_8975_;
                        v_isShared_9058_ = v_isSharedCheck_9062_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9055_);
                        leanh::lean_dec(v___x_8975_);
                        v___x_9057_ = leanh::lean_box(0);
                        v_isShared_9058_ = v_isSharedCheck_9062_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8985_ = leanh::lean_box(0);
                v___x_8986_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8986_, 0, v_hName_8965_);
                leanh::lean_ctor_set(v___x_8986_, 1, v___x_8985_);
                v___x_8987_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_8987_, 0, v___x_8986_);
                leanh::lean_ctor_set_uint8(
                    v___x_8987_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_8977_,
                );
                v___x_8988_ = leanh::lean_unsigned_to_nat(2);
                v___x_8989_ = lean_mk_empty_array_with_capacity(v___x_8988_);
                leanh::lean_inc_ref(v___x_8987_);
                v___x_8990_ = lean_array_push(v___x_8989_, v___x_8987_);
                v___x_8991_ = lean_array_push(v___x_8990_, v___x_8987_);
                v___x_8992_ = leanh::lean_box(0);
                v___x_8993_ = l_Lean_Meta_Cases_cases(
                    v_snd_8981_,
                    v_fst_8980_,
                    v___x_8991_,
                    v___x_8977_,
                    v___x_8992_,
                    v_a_8966_,
                    v_a_8967_,
                    v_a_8968_,
                    v_a_8969_,
                );
                if leanh::lean_obj_tag(v___x_8993_) == 0 {
                    v_a_8994_ = leanh::lean_ctor_get(v___x_8993_, 0);
                    leanh::lean_inc(v_a_8994_);
                    leanh::lean_dec_ref_known(v___x_8993_, 1);
                    v___x_8995_ = lean_array_get_size(v_a_8994_);
                    v___x_8996_ = lean_nat_dec_eq(v___x_8995_, v___x_8988_);
                    if v___x_8996_ == 0 {
                        leanh::lean_dec(v_a_8994_);
                        leanh::lean_del_object(v___x_8983_);
                        v___x_8997_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__3_once),
                            _init_l_Lean_MVarId_byCases___closed__3,
                        );
                        v___x_8998_ = leanh::lean_unsigned_to_nat(30);
                        v___x_8999_ = l_Lean_inlineExpr(v_p_8964_, v___x_8998_);
                        v___x_9000_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9000_, 0, v___x_8997_);
                        leanh::lean_ctor_set(v___x_9000_, 1, v___x_8999_);
                        v___x_9001_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__5_once),
                            _init_l_Lean_MVarId_byCases___closed__5,
                        );
                        v___x_9002_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9002_, 0, v___x_9000_);
                        leanh::lean_ctor_set(v___x_9002_, 1, v___x_9001_);
                        v___x_9003_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_9002_, v_a_8966_, v_a_8967_, v_a_8968_, v_a_8969_);
                        return v___x_9003_;
                    } else {
                        leanh::lean_dec_ref(v_p_8964_);
                        v___x_9004_ = leanh::lean_unsigned_to_nat(0);
                        v___x_9005_ = lean_array_fget_borrowed(v_a_8994_, v___x_9004_);
                        leanh::lean_inc(v___x_9005_);
                        v___x_9006_ =
                            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
                                v___x_9005_,
                                v_a_8966_,
                                v_a_8967_,
                                v_a_8968_,
                                v_a_8969_,
                            );
                        if leanh::lean_obj_tag(v___x_9006_) == 0 {
                            v_a_9007_ = leanh::lean_ctor_get(v___x_9006_, 0);
                            leanh::lean_inc(v_a_9007_);
                            leanh::lean_dec_ref_known(v___x_9006_, 1);
                            v___x_9008_ = leanh::lean_unsigned_to_nat(1);
                            v___x_9009_ = lean_array_fget(v_a_8994_, v___x_9008_);
                            leanh::lean_dec(v_a_8994_);
                            v___x_9010_ =
                                l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
                                    v___x_9009_,
                                    v_a_8966_,
                                    v_a_8967_,
                                    v_a_8968_,
                                    v_a_8969_,
                                );
                            if leanh::lean_obj_tag(v___x_9010_) == 0 {
                                v_a_9011_ = leanh::lean_ctor_get(v___x_9010_, 0);
                                v_isSharedCheck_9021_ =
                                    (!leanh::lean_is_exclusive(v___x_9010_)) as u8;
                                if v_isSharedCheck_9021_ == 0 {
                                    v___x_9013_ = v___x_9010_;
                                    v_isShared_9014_ = v_isSharedCheck_9021_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9011_);
                                    leanh::lean_dec(v___x_9010_);
                                    v___x_9013_ = leanh::lean_box(0);
                                    v_isShared_9014_ = v_isSharedCheck_9021_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_9007_);
                                leanh::lean_del_object(v___x_8983_);
                                v_a_9022_ = leanh::lean_ctor_get(v___x_9010_, 0);
                                v_isSharedCheck_9029_ =
                                    (!leanh::lean_is_exclusive(v___x_9010_)) as u8;
                                if v_isSharedCheck_9029_ == 0 {
                                    v___x_9024_ = v___x_9010_;
                                    v_isShared_9025_ = v_isSharedCheck_9029_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9022_);
                                    leanh::lean_dec(v___x_9010_);
                                    v___x_9024_ = leanh::lean_box(0);
                                    v_isShared_9025_ = v_isSharedCheck_9029_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_8994_);
                            leanh::lean_del_object(v___x_8983_);
                            v_a_9030_ = leanh::lean_ctor_get(v___x_9006_, 0);
                            v_isSharedCheck_9037_ =
                                (!leanh::lean_is_exclusive(v___x_9006_)) as u8;
                            if v_isSharedCheck_9037_ == 0 {
                                v___x_9032_ = v___x_9006_;
                                v_isShared_9033_ = v_isSharedCheck_9037_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9030_);
                                leanh::lean_dec(v___x_9006_);
                                v___x_9032_ = leanh::lean_box(0);
                                v_isShared_9033_ = v_isSharedCheck_9037_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8983_);
                    leanh::lean_dec_ref(v_p_8964_);
                    v_a_9038_ = leanh::lean_ctor_get(v___x_8993_, 0);
                    v_isSharedCheck_9045_ = (!leanh::lean_is_exclusive(v___x_8993_)) as u8;
                    if v_isSharedCheck_9045_ == 0 {
                        v___x_9040_ = v___x_8993_;
                        v_isShared_9041_ = v_isSharedCheck_9045_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9038_);
                        leanh::lean_dec(v___x_8993_);
                        v___x_9040_ = leanh::lean_box(0);
                        v_isShared_9041_ = v_isSharedCheck_9045_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8984_ == 0 {
                    leanh::lean_ctor_set(v___x_8983_, 1, v_a_9011_);
                    leanh::lean_ctor_set(v___x_8983_, 0, v_a_9007_);
                    v___x_9016_ = v___x_8983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9020_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9020_, 0, v_a_9007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9020_, 1, v_a_9011_);
                    v___x_9016_ = v_reuseFailAlloc_9020_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_9014_ == 0 {
                    leanh::lean_ctor_set(v___x_9013_, 0, v___x_9016_);
                    v___x_9018_ = v___x_9013_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9019_, 0, v___x_9016_);
                    v___x_9018_ = v_reuseFailAlloc_9019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9018_;
            }
            5 => {
                if v_isShared_9025_ == 0 {
                    v___x_9027_ = v___x_9024_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9028_, 0, v_a_9022_);
                    v___x_9027_ = v_reuseFailAlloc_9028_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9027_;
            }
            7 => {
                if v_isShared_9033_ == 0 {
                    v___x_9035_ = v___x_9032_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9036_, 0, v_a_9030_);
                    v___x_9035_ = v_reuseFailAlloc_9036_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9035_;
            }
            9 => {
                if v_isShared_9041_ == 0 {
                    v___x_9043_ = v___x_9040_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9044_, 0, v_a_9038_);
                    v___x_9043_ = v_reuseFailAlloc_9044_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9043_;
            }
            11 => {
                if v_isShared_9050_ == 0 {
                    v___x_9052_ = v___x_9049_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_9053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9053_, 0, v_a_9047_);
                    v___x_9052_ = v_reuseFailAlloc_9053_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_9052_;
            }
            13 => {
                if v_isShared_9058_ == 0 {
                    v___x_9060_ = v___x_9057_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_9061_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9061_, 0, v_a_9055_);
                    v___x_9060_ = v_reuseFailAlloc_9061_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_9060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_byCases___boxed(
    mut v_mvarId_9063_: *mut leanh::LeanObject,
    mut v_p_9064_: *mut leanh::LeanObject,
    mut v_hName_9065_: *mut leanh::LeanObject,
    mut v_a_9066_: *mut leanh::LeanObject,
    mut v_a_9067_: *mut leanh::LeanObject,
    mut v_a_9068_: *mut leanh::LeanObject,
    mut v_a_9069_: *mut leanh::LeanObject,
    mut v_a_9070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9071_ = l_Lean_MVarId_byCases(
        v_mvarId_9063_,
        v_p_9064_,
        v_hName_9065_,
        v_a_9066_,
        v_a_9067_,
        v_a_9068_,
        v_a_9069_,
    );
    leanh::lean_dec(v_a_9069_);
    leanh::lean_dec_ref(v_a_9068_);
    leanh::lean_dec(v_a_9067_);
    leanh::lean_dec_ref(v_a_9066_);
    return v_res_9071_;
}
pub unsafe fn _init_l_Lean_MVarId_byCasesDec___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_9075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9075_ = leanh::lean_box(0);
    v___x_9076_ = l_Lean_MVarId_byCasesDec___closed__1;
    v___x_9077_ = l_Lean_mkConst(v___x_9076_, v___x_9075_);
    return v___x_9077_;
}
pub unsafe fn _init_l_Lean_MVarId_byCasesDec___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_9079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9079_ = l_Lean_MVarId_byCasesDec___closed__3;
    v___x_9080_ = l_Lean_stringToMessageData(v___x_9079_);
    return v___x_9080_;
}
pub unsafe fn l_Lean_MVarId_byCasesDec(
    mut v_mvarId_9081_: *mut leanh::LeanObject,
    mut v_p_9082_: *mut leanh::LeanObject,
    mut v_dec_9083_: *mut leanh::LeanObject,
    mut v_hName_9084_: *mut leanh::LeanObject,
    mut v_a_9085_: *mut leanh::LeanObject,
    mut v_a_9086_: *mut leanh::LeanObject,
    mut v_a_9087_: *mut leanh::LeanObject,
    mut v_a_9088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: u8 = 0;
    let mut v___x_9097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_9099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9103_: u8 = 0;
    let mut v___x_9104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9114_: u8 = 0;
    let mut v___x_9115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9132_: u8 = 0;
    let mut v___x_9134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9139_: u8 = 0;
    let mut v_a_9140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9143_: u8 = 0;
    let mut v___x_9145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9147_: u8 = 0;
    let mut v_a_9148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9151_: u8 = 0;
    let mut v___x_9153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9155_: u8 = 0;
    let mut v_a_9156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9159_: u8 = 0;
    let mut v___x_9161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9163_: u8 = 0;
    let mut v_isSharedCheck_9164_: u8 = 0;
    let mut v_a_9165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9168_: u8 = 0;
    let mut v___x_9170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9172_: u8 = 0;
    let mut v_a_9173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9176_: u8 = 0;
    let mut v___x_9178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9090_ = l_Lean_MVarId_byCases___closed__1;
                v___x_9091_ = leanh::lean_box(0);
                v___x_9092_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_byCasesDec___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_byCasesDec___closed__2_once),
                    _init_l_Lean_MVarId_byCasesDec___closed__2,
                );
                leanh::lean_inc_ref(v_p_9082_);
                v___x_9093_ = l_Lean_Expr_app___override(v___x_9092_, v_p_9082_);
                v___x_9094_ = l_Lean_MVarId_assert(
                    v_mvarId_9081_,
                    v___x_9090_,
                    v___x_9093_,
                    v_dec_9083_,
                    v_a_9085_,
                    v_a_9086_,
                    v_a_9087_,
                    v_a_9088_,
                );
                if leanh::lean_obj_tag(v___x_9094_) == 0 {
                    v_a_9095_ = leanh::lean_ctor_get(v___x_9094_, 0);
                    leanh::lean_inc(v_a_9095_);
                    leanh::lean_dec_ref_known(v___x_9094_, 1);
                    v___x_9096_ = 0;
                    v___x_9097_ = l_Lean_Meta_intro1Core(
                        v_a_9095_,
                        v___x_9096_,
                        v_a_9085_,
                        v_a_9086_,
                        v_a_9087_,
                        v_a_9088_,
                    );
                    if leanh::lean_obj_tag(v___x_9097_) == 0 {
                        v_a_9098_ = leanh::lean_ctor_get(v___x_9097_, 0);
                        leanh::lean_inc(v_a_9098_);
                        leanh::lean_dec_ref_known(v___x_9097_, 1);
                        v_fst_9099_ = leanh::lean_ctor_get(v_a_9098_, 0);
                        v_snd_9100_ = leanh::lean_ctor_get(v_a_9098_, 1);
                        v_isSharedCheck_9164_ = (!leanh::lean_is_exclusive(v_a_9098_)) as u8;
                        if v_isSharedCheck_9164_ == 0 {
                            v___x_9102_ = v_a_9098_;
                            v_isShared_9103_ = v_isSharedCheck_9164_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_9100_);
                            leanh::lean_inc(v_fst_9099_);
                            leanh::lean_dec(v_a_9098_);
                            v___x_9102_ = leanh::lean_box(0);
                            v_isShared_9103_ = v_isSharedCheck_9164_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_hName_9084_);
                        leanh::lean_dec_ref(v_p_9082_);
                        v_a_9165_ = leanh::lean_ctor_get(v___x_9097_, 0);
                        v_isSharedCheck_9172_ =
                            (!leanh::lean_is_exclusive(v___x_9097_)) as u8;
                        if v_isSharedCheck_9172_ == 0 {
                            v___x_9167_ = v___x_9097_;
                            v_isShared_9168_ = v_isSharedCheck_9172_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9165_);
                            leanh::lean_dec(v___x_9097_);
                            v___x_9167_ = leanh::lean_box(0);
                            v_isShared_9168_ = v_isSharedCheck_9172_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_hName_9084_);
                    leanh::lean_dec_ref(v_p_9082_);
                    v_a_9173_ = leanh::lean_ctor_get(v___x_9094_, 0);
                    v_isSharedCheck_9180_ = (!leanh::lean_is_exclusive(v___x_9094_)) as u8;
                    if v_isSharedCheck_9180_ == 0 {
                        v___x_9175_ = v___x_9094_;
                        v_isShared_9176_ = v_isSharedCheck_9180_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9173_);
                        leanh::lean_dec(v___x_9094_);
                        v___x_9175_ = leanh::lean_box(0);
                        v_isShared_9176_ = v_isSharedCheck_9180_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9104_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9104_, 0, v_hName_9084_);
                leanh::lean_ctor_set(v___x_9104_, 1, v___x_9091_);
                v___x_9105_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_9105_, 0, v___x_9104_);
                leanh::lean_ctor_set_uint8(
                    v___x_9105_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_9096_,
                );
                v___x_9106_ = leanh::lean_unsigned_to_nat(2);
                v___x_9107_ = lean_mk_empty_array_with_capacity(v___x_9106_);
                leanh::lean_inc_ref(v___x_9105_);
                v___x_9108_ = lean_array_push(v___x_9107_, v___x_9105_);
                v___x_9109_ = lean_array_push(v___x_9108_, v___x_9105_);
                v___x_9110_ = leanh::lean_box(0);
                v___x_9111_ = l_Lean_Meta_Cases_cases(
                    v_snd_9100_,
                    v_fst_9099_,
                    v___x_9109_,
                    v___x_9096_,
                    v___x_9110_,
                    v_a_9085_,
                    v_a_9086_,
                    v_a_9087_,
                    v_a_9088_,
                );
                if leanh::lean_obj_tag(v___x_9111_) == 0 {
                    v_a_9112_ = leanh::lean_ctor_get(v___x_9111_, 0);
                    leanh::lean_inc(v_a_9112_);
                    leanh::lean_dec_ref_known(v___x_9111_, 1);
                    v___x_9113_ = lean_array_get_size(v_a_9112_);
                    v___x_9114_ = lean_nat_dec_eq(v___x_9113_, v___x_9106_);
                    if v___x_9114_ == 0 {
                        leanh::lean_dec(v_a_9112_);
                        leanh::lean_del_object(v___x_9102_);
                        v___x_9115_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCasesDec___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCasesDec___closed__4_once),
                            _init_l_Lean_MVarId_byCasesDec___closed__4,
                        );
                        v___x_9116_ = leanh::lean_unsigned_to_nat(30);
                        v___x_9117_ = l_Lean_inlineExpr(v_p_9082_, v___x_9116_);
                        v___x_9118_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9118_, 0, v___x_9115_);
                        leanh::lean_ctor_set(v___x_9118_, 1, v___x_9117_);
                        v___x_9119_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_byCases___closed__5_once),
                            _init_l_Lean_MVarId_byCases___closed__5,
                        );
                        v___x_9120_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9120_, 0, v___x_9118_);
                        leanh::lean_ctor_set(v___x_9120_, 1, v___x_9119_);
                        v___x_9121_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_9120_, v_a_9085_, v_a_9086_, v_a_9087_, v_a_9088_);
                        return v___x_9121_;
                    } else {
                        leanh::lean_dec_ref(v_p_9082_);
                        v___x_9122_ = leanh::lean_unsigned_to_nat(1);
                        v___x_9123_ = lean_array_fget_borrowed(v_a_9112_, v___x_9122_);
                        leanh::lean_inc(v___x_9123_);
                        v___x_9124_ =
                            l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
                                v___x_9123_,
                                v_a_9085_,
                                v_a_9086_,
                                v_a_9087_,
                                v_a_9088_,
                            );
                        if leanh::lean_obj_tag(v___x_9124_) == 0 {
                            v_a_9125_ = leanh::lean_ctor_get(v___x_9124_, 0);
                            leanh::lean_inc(v_a_9125_);
                            leanh::lean_dec_ref_known(v___x_9124_, 1);
                            v___x_9126_ = leanh::lean_unsigned_to_nat(0);
                            v___x_9127_ = lean_array_fget(v_a_9112_, v___x_9126_);
                            leanh::lean_dec(v_a_9112_);
                            v___x_9128_ =
                                l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(
                                    v___x_9127_,
                                    v_a_9085_,
                                    v_a_9086_,
                                    v_a_9087_,
                                    v_a_9088_,
                                );
                            if leanh::lean_obj_tag(v___x_9128_) == 0 {
                                v_a_9129_ = leanh::lean_ctor_get(v___x_9128_, 0);
                                v_isSharedCheck_9139_ =
                                    (!leanh::lean_is_exclusive(v___x_9128_)) as u8;
                                if v_isSharedCheck_9139_ == 0 {
                                    v___x_9131_ = v___x_9128_;
                                    v_isShared_9132_ = v_isSharedCheck_9139_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9129_);
                                    leanh::lean_dec(v___x_9128_);
                                    v___x_9131_ = leanh::lean_box(0);
                                    v_isShared_9132_ = v_isSharedCheck_9139_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_9125_);
                                leanh::lean_del_object(v___x_9102_);
                                v_a_9140_ = leanh::lean_ctor_get(v___x_9128_, 0);
                                v_isSharedCheck_9147_ =
                                    (!leanh::lean_is_exclusive(v___x_9128_)) as u8;
                                if v_isSharedCheck_9147_ == 0 {
                                    v___x_9142_ = v___x_9128_;
                                    v_isShared_9143_ = v_isSharedCheck_9147_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9140_);
                                    leanh::lean_dec(v___x_9128_);
                                    v___x_9142_ = leanh::lean_box(0);
                                    v_isShared_9143_ = v_isSharedCheck_9147_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_9112_);
                            leanh::lean_del_object(v___x_9102_);
                            v_a_9148_ = leanh::lean_ctor_get(v___x_9124_, 0);
                            v_isSharedCheck_9155_ =
                                (!leanh::lean_is_exclusive(v___x_9124_)) as u8;
                            if v_isSharedCheck_9155_ == 0 {
                                v___x_9150_ = v___x_9124_;
                                v_isShared_9151_ = v_isSharedCheck_9155_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9148_);
                                leanh::lean_dec(v___x_9124_);
                                v___x_9150_ = leanh::lean_box(0);
                                v_isShared_9151_ = v_isSharedCheck_9155_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_9102_);
                    leanh::lean_dec_ref(v_p_9082_);
                    v_a_9156_ = leanh::lean_ctor_get(v___x_9111_, 0);
                    v_isSharedCheck_9163_ = (!leanh::lean_is_exclusive(v___x_9111_)) as u8;
                    if v_isSharedCheck_9163_ == 0 {
                        v___x_9158_ = v___x_9111_;
                        v_isShared_9159_ = v_isSharedCheck_9163_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9156_);
                        leanh::lean_dec(v___x_9111_);
                        v___x_9158_ = leanh::lean_box(0);
                        v_isShared_9159_ = v_isSharedCheck_9163_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_9103_ == 0 {
                    leanh::lean_ctor_set(v___x_9102_, 1, v_a_9129_);
                    leanh::lean_ctor_set(v___x_9102_, 0, v_a_9125_);
                    v___x_9134_ = v___x_9102_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9138_, 0, v_a_9125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9138_, 1, v_a_9129_);
                    v___x_9134_ = v_reuseFailAlloc_9138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_9132_ == 0 {
                    leanh::lean_ctor_set(v___x_9131_, 0, v___x_9134_);
                    v___x_9136_ = v___x_9131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9137_, 0, v___x_9134_);
                    v___x_9136_ = v_reuseFailAlloc_9137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9136_;
            }
            5 => {
                if v_isShared_9143_ == 0 {
                    v___x_9145_ = v___x_9142_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9146_, 0, v_a_9140_);
                    v___x_9145_ = v_reuseFailAlloc_9146_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9145_;
            }
            7 => {
                if v_isShared_9151_ == 0 {
                    v___x_9153_ = v___x_9150_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9154_, 0, v_a_9148_);
                    v___x_9153_ = v_reuseFailAlloc_9154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9153_;
            }
            9 => {
                if v_isShared_9159_ == 0 {
                    v___x_9161_ = v___x_9158_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9162_, 0, v_a_9156_);
                    v___x_9161_ = v_reuseFailAlloc_9162_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9161_;
            }
            11 => {
                if v_isShared_9168_ == 0 {
                    v___x_9170_ = v___x_9167_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_9171_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9171_, 0, v_a_9165_);
                    v___x_9170_ = v_reuseFailAlloc_9171_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_9170_;
            }
            13 => {
                if v_isShared_9176_ == 0 {
                    v___x_9178_ = v___x_9175_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_9179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9179_, 0, v_a_9173_);
                    v___x_9178_ = v_reuseFailAlloc_9179_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_9178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_byCasesDec___boxed(
    mut v_mvarId_9181_: *mut leanh::LeanObject,
    mut v_p_9182_: *mut leanh::LeanObject,
    mut v_dec_9183_: *mut leanh::LeanObject,
    mut v_hName_9184_: *mut leanh::LeanObject,
    mut v_a_9185_: *mut leanh::LeanObject,
    mut v_a_9186_: *mut leanh::LeanObject,
    mut v_a_9187_: *mut leanh::LeanObject,
    mut v_a_9188_: *mut leanh::LeanObject,
    mut v_a_9189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9190_ = l_Lean_MVarId_byCasesDec(
        v_mvarId_9181_,
        v_p_9182_,
        v_dec_9183_,
        v_hName_9184_,
        v_a_9185_,
        v_a_9186_,
        v_a_9187_,
        v_a_9188_,
    );
    leanh::lean_dec(v_a_9188_);
    leanh::lean_dec_ref(v_a_9187_);
    leanh::lean_dec(v_a_9186_);
    leanh::lean_dec_ref(v_a_9185_);
    return v_res_9190_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9242_ = leanh::lean_unsigned_to_nat(4241171151);
    v___x_9243_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
    v___x_9244_ = l_Lean_Name_num___override(v___x_9243_, v___x_9242_);
    return v___x_9244_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9246_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
    v___x_9247_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
    v___x_9248_ = l_Lean_Name_str___override(v___x_9247_, v___x_9246_);
    return v___x_9248_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9250_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
    v___x_9251_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
    v___x_9252_ = l_Lean_Name_str___override(v___x_9251_, v___x_9250_);
    return v___x_9252_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9253_ = leanh::lean_unsigned_to_nat(2);
    v___x_9254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
    v___x_9255_ = l_Lean_Name_num___override(v___x_9254_, v___x_9253_);
    return v___x_9255_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_9257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9258_: u8 = 0;
    let mut v___x_9259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9257_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
    v___x_9258_ = 0;
    v___x_9259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
    v___x_9260_ = l_Lean_registerTraceClass(v___x_9257_, v___x_9258_, v___x_9259_);
    return v___x_9260_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(
    mut v_a_9261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9262_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
    return v_res_9262_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cases(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Induction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Acyclic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cases(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cases(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Induction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Acyclic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_UnifyEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cases(builtin);
}