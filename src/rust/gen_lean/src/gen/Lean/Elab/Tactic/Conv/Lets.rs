// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Lets
// Imports: Lean.Elab.Tactic.Lets Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getNameOfIdent_x27,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg,
    l_Lean_Elab_Tactic_Conv_mkConvGoalFor, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Lets::{
    initialize_Lean_Elab_Tactic_Lets, l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg,
    l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg, l_Lean_Elab_Tactic_extractLetsAddVarInfo,
    runtime_initialize_Lean_Elab_Tactic_Lets,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_mvar___override, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::LetToHave::l_Lean_Meta_letToHave;
use crate::r#gen::Lean::Meta::Tactic::Lets::{
    l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp, l_Lean_Meta_liftLets,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::ffi::{lean_st_ref_set, lean_st_ref_take};
use crate::ffi::lean_expr_eqv;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        40, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 41, 32, 110, 111,
        110, 45, 100, 101, 102, 101, 113, 32, 105, 110, 32, 97, 115, 115, 105, 103, 110, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4644032510077903208 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 111, 110, 118, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
            as *mut crate::leanh::LeanObject,
        3123354491248406356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut crate::leanh::LeanObject,4698081872094885029 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 105, 102, 116, 95, 108, 101, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7326091052943921366 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 105, 102, 116, 76, 101, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15211363250062378073 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 76, 105, 102, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut crate::leanh::LeanObject,5567011710448919931 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6130153969274943757 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 84, 111, 72, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1576434579341158445 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 76, 101, 116, 84, 111, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut crate::leanh::LeanObject,7421465252802819374 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = crate::leanh::lean_box(0);
    v___x_1103_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1104_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    crate::leanh::lean_ctor_set(v___x_1104_, 1, v___x_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
    v___x_1107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(
    mut v___y_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v_res_1109_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(
    mut v_00_u03b1_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v___x_1120_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(
    mut v_00_u03b1_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(
            v_00_u03b1_1121_,
            v___y_1122_,
            v___y_1123_,
            v___y_1124_,
            v___y_1125_,
            v___y_1126_,
            v___y_1127_,
            v___y_1128_,
            v___y_1129_,
        );
    crate::leanh::lean_dec(v___y_1129_);
    crate::leanh::lean_dec_ref(v___y_1128_);
    crate::leanh::lean_dec(v___y_1127_);
    crate::leanh::lean_dec_ref(v___y_1126_);
    crate::leanh::lean_dec(v___y_1125_);
    crate::leanh::lean_dec_ref(v___y_1124_);
    crate::leanh::lean_dec(v___y_1123_);
    crate::leanh::lean_dec_ref(v___y_1122_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
    mut v_mvarId_1132_: *mut crate::leanh::LeanObject,
    mut v_x_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1132_,
                    v_x_1133_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                );
                if crate::leanh::lean_obj_tag(v___x_1139_) == 0 {
                    v_a_1140_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1147_ = (!crate::leanh::lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1142_ = v___x_1139_;
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1140_);
                        crate::leanh::lean_dec(v___x_1139_);
                        v___x_1142_ = crate::leanh::lean_box(0);
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1148_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1155_ = (!crate::leanh::lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1155_ == 0 {
                        v___x_1150_ = v___x_1139_;
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1148_);
                        crate::leanh::lean_dec(v___x_1139_);
                        v___x_1150_ = crate::leanh::lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1145_;
            }
            3 => {
                if v_isShared_1151_ == 0 {
                    v___x_1153_ = v___x_1150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
                    v___x_1153_ = v_reuseFailAlloc_1154_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(
    mut v_mvarId_1156_: *mut crate::leanh::LeanObject,
    mut v_x_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
            v_mvarId_1156_,
            v_x_1157_,
            v___y_1158_,
            v___y_1159_,
            v___y_1160_,
            v___y_1161_,
        );
    crate::leanh::lean_dec(v___y_1161_);
    crate::leanh::lean_dec_ref(v___y_1160_);
    crate::leanh::lean_dec(v___y_1159_);
    crate::leanh::lean_dec_ref(v___y_1158_);
    return v_res_1163_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
    mut v_00_u03b1_1164_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1165_: *mut crate::leanh::LeanObject,
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
            v_mvarId_1165_,
            v_x_1166_,
            v___y_1167_,
            v___y_1168_,
            v___y_1169_,
            v___y_1170_,
        );
    return v___x_1172_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(
    mut v_00_u03b1_1173_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1174_: *mut crate::leanh::LeanObject,
    mut v_x_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
        v_00_u03b1_1173_,
        v_mvarId_1174_,
        v_x_1175_,
        v___y_1176_,
        v___y_1177_,
        v___y_1178_,
        v___y_1179_,
    );
    crate::leanh::lean_dec(v___y_1179_);
    crate::leanh::lean_dec_ref(v___y_1178_);
    crate::leanh::lean_dec(v___y_1177_);
    crate::leanh::lean_dec_ref(v___y_1176_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(
    mut v_k_1182_: *mut crate::leanh::LeanObject,
    mut v_b_1183_: *mut crate::leanh::LeanObject,
    mut v_c_1184_: *mut crate::leanh::LeanObject,
    mut v_d_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1189_);
    crate::leanh::lean_inc_ref(v___y_1188_);
    crate::leanh::lean_inc(v___y_1187_);
    crate::leanh::lean_inc_ref(v___y_1186_);
    v___x_1191_ = crate::leanh::lean_apply_8(
        v_k_1182_,
        v_b_1183_,
        v_c_1184_,
        v_d_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        crate::leanh::lean_box(0),
    );
    return v___x_1191_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(
    mut v_k_1192_: *mut crate::leanh::LeanObject,
    mut v_b_1193_: *mut crate::leanh::LeanObject,
    mut v_c_1194_: *mut crate::leanh::LeanObject,
    mut v_d_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_1192_, v_b_1193_, v_c_1194_, v_d_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
    crate::leanh::lean_dec(v___y_1199_);
    crate::leanh::lean_dec_ref(v___y_1198_);
    crate::leanh::lean_dec(v___y_1197_);
    crate::leanh::lean_dec_ref(v___y_1196_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
    mut v_es_1202_: *mut crate::leanh::LeanObject,
    mut v_givenNames_1203_: *mut crate::leanh::LeanObject,
    mut v_k_1204_: *mut crate::leanh::LeanObject,
    mut v_config_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1216_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut v_a_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1211_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                crate::leanh::lean_closure_set(v___f_1211_, 0, v_k_1204_);
                v___x_1212_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(
                    crate::leanh::lean_box(0),
                    v_es_1202_,
                    v_givenNames_1203_,
                    v___f_1211_,
                    v_config_1205_,
                    v___y_1206_,
                    v___y_1207_,
                    v___y_1208_,
                    v___y_1209_,
                );
                if crate::leanh::lean_obj_tag(v___x_1212_) == 0 {
                    v_a_1213_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1220_ = (!crate::leanh::lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1220_ == 0 {
                        v___x_1215_ = v___x_1212_;
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1213_);
                        crate::leanh::lean_dec(v___x_1212_);
                        v___x_1215_ = crate::leanh::lean_box(0);
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1221_ = crate::leanh::lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1228_ = (!crate::leanh::lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1228_ == 0 {
                        v___x_1223_ = v___x_1212_;
                        v_isShared_1224_ = v_isSharedCheck_1228_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1221_);
                        crate::leanh::lean_dec(v___x_1212_);
                        v___x_1223_ = crate::leanh::lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1228_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1216_ == 0 {
                    v___x_1218_ = v___x_1215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
                    v___x_1218_ = v_reuseFailAlloc_1219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1218_;
            }
            3 => {
                if v_isShared_1224_ == 0 {
                    v___x_1226_ = v___x_1223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
                    v___x_1226_ = v_reuseFailAlloc_1227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(
    mut v_es_1229_: *mut crate::leanh::LeanObject,
    mut v_givenNames_1230_: *mut crate::leanh::LeanObject,
    mut v_k_1231_: *mut crate::leanh::LeanObject,
    mut v_config_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ =
        l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
            v_es_1229_,
            v_givenNames_1230_,
            v_k_1231_,
            v_config_1232_,
            v___y_1233_,
            v___y_1234_,
            v___y_1235_,
            v___y_1236_,
        );
    crate::leanh::lean_dec(v___y_1236_);
    crate::leanh::lean_dec_ref(v___y_1235_);
    crate::leanh::lean_dec(v___y_1234_);
    crate::leanh::lean_dec_ref(v___y_1233_);
    crate::leanh::lean_dec_ref(v_config_1232_);
    return v_res_1238_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(
    mut v_00_u03b1_1239_: *mut crate::leanh::LeanObject,
    mut v_es_1240_: *mut crate::leanh::LeanObject,
    mut v_givenNames_1241_: *mut crate::leanh::LeanObject,
    mut v_k_1242_: *mut crate::leanh::LeanObject,
    mut v_config_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ =
        l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
            v_es_1240_,
            v_givenNames_1241_,
            v_k_1242_,
            v_config_1243_,
            v___y_1244_,
            v___y_1245_,
            v___y_1246_,
            v___y_1247_,
        );
    return v___x_1249_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(
    mut v_00_u03b1_1250_: *mut crate::leanh::LeanObject,
    mut v_es_1251_: *mut crate::leanh::LeanObject,
    mut v_givenNames_1252_: *mut crate::leanh::LeanObject,
    mut v_k_1253_: *mut crate::leanh::LeanObject,
    mut v_config_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(
        v_00_u03b1_1250_,
        v_es_1251_,
        v_givenNames_1252_,
        v_k_1253_,
        v_config_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
        v___y_1258_,
    );
    crate::leanh::lean_dec(v___y_1258_);
    crate::leanh::lean_dec_ref(v___y_1257_);
    crate::leanh::lean_dec(v___y_1256_);
    crate::leanh::lean_dec_ref(v___y_1255_);
    crate::leanh::lean_dec_ref(v_config_1254_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(
    mut v_x_1261_: *mut crate::leanh::LeanObject,
    mut v_x_1262_: *mut crate::leanh::LeanObject,
    mut v_x_1263_: *mut crate::leanh::LeanObject,
    mut v_x_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1265_ = crate::leanh::lean_ctor_get(v_x_1261_, 0);
                v_vs_1266_ = crate::leanh::lean_ctor_get(v_x_1261_, 1);
                v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v_x_1261_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1268_ = v_x_1261_;
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1266_);
                    crate::leanh::lean_inc(v_ks_1265_);
                    crate::leanh::lean_dec(v_x_1261_);
                    v___x_1268_ = crate::leanh::lean_box(0);
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1270_ = lean_array_get_size(v_ks_1265_);
                v___x_1271_ = lean_nat_dec_lt(v_x_1262_, v___x_1270_);
                if v___x_1271_ == 0 {
                    crate::leanh::lean_dec(v_x_1262_);
                    v___x_1272_ = lean_array_push(v_ks_1265_, v_x_1263_);
                    v___x_1273_ = lean_array_push(v_vs_1266_, v_x_1264_);
                    if v_isShared_1269_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1268_, 1, v___x_1273_);
                        crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1272_);
                        v___x_1275_ = v___x_1268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1276_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
                        v___x_1275_ = v_reuseFailAlloc_1276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1277_ = lean_array_fget_borrowed(v_ks_1265_, v_x_1262_);
                    v___x_1278_ = l_Lean_instBEqMVarId_beq(v_x_1263_, v_k_x27_1277_);
                    if v___x_1278_ == 0 {
                        if v_isShared_1269_ == 0 {
                            v___x_1280_ = v___x_1268_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1284_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ks_1265_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_vs_1266_);
                            v___x_1280_ = v_reuseFailAlloc_1284_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1285_ = lean_array_fset(v_ks_1265_, v_x_1262_, v_x_1263_);
                        v___x_1286_ = lean_array_fset(v_vs_1266_, v_x_1262_, v_x_1264_);
                        crate::leanh::lean_dec(v_x_1262_);
                        if v_isShared_1269_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1268_, 1, v___x_1286_);
                            crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1285_);
                            v___x_1288_ = v___x_1268_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1289_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1285_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
                            v___x_1288_ = v_reuseFailAlloc_1289_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1275_;
            }
            3 => {
                v___x_1281_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1282_ = lean_nat_add(v_x_1262_, v___x_1281_);
                crate::leanh::lean_dec(v_x_1262_);
                v_x_1261_ = v___x_1280_;
                v_x_1262_ = v___x_1282_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(
    mut v_n_1291_: *mut crate::leanh::LeanObject,
    mut v_k_1292_: *mut crate::leanh::LeanObject,
    mut v_v_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1295_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_n_1291_, v___x_1294_, v_k_1292_, v_v_1293_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: usize = 0;
    v___x_1296_ = 5usize;
    v___x_1297_ = 1usize;
    v___x_1298_ = lean_usize_shift_left(v___x_1297_, v___x_1296_);
    return v___x_1298_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: usize = 0;
    let mut v___x_1301_: usize = 0;
    v___x_1299_ = 1usize;
    v___x_1300_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
    v___x_1301_ = lean_usize_sub(v___x_1300_, v___x_1299_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(
    mut v_x_1303_: *mut crate::leanh::LeanObject,
    mut v_x_1304_: usize,
    mut v_x_1305_: usize,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
    mut v_x_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: usize = 0;
    let mut v___x_1312_: usize = 0;
    let mut v_j_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v_v_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut v_node_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_unused_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1363_: u8 = 0;
    let mut v_ks_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v_reuseFailAlloc_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1303_) == 0 {
                    v_es_1308_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
                    v___x_1309_ = 5usize;
                    v___x_1310_ = 1usize;
                    v___x_1311_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1);
                    v___x_1312_ = lean_usize_land(v_x_1304_, v___x_1311_);
                    v_j_1313_ = lean_usize_to_nat(v___x_1312_);
                    v___x_1314_ = lean_array_get_size(v_es_1308_);
                    v___x_1315_ = lean_nat_dec_lt(v_j_1313_, v___x_1314_);
                    if v___x_1315_ == 0 {
                        crate::leanh::lean_dec(v_j_1313_);
                        crate::leanh::lean_dec(v_x_1307_);
                        crate::leanh::lean_dec(v_x_1306_);
                        return v_x_1303_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1308_);
                        v_isSharedCheck_1352_ = (!crate::leanh::lean_is_exclusive(v_x_1303_)) as u8;
                        if v_isSharedCheck_1352_ == 0 {
                            v_unused_1353_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
                            crate::leanh::lean_dec(v_unused_1353_);
                            v___x_1317_ = v_x_1303_;
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1303_);
                            v___x_1317_ = crate::leanh::lean_box(0);
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1354_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
                    v_vs_1355_ = crate::leanh::lean_ctor_get(v_x_1303_, 1);
                    v_isSharedCheck_1375_ = (!crate::leanh::lean_is_exclusive(v_x_1303_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1357_ = v_x_1303_;
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1355_);
                        crate::leanh::lean_inc(v_ks_1354_);
                        crate::leanh::lean_dec(v_x_1303_);
                        v___x_1357_ = crate::leanh::lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1319_ = lean_array_fget(v_es_1308_, v_j_1313_);
                v___x_1320_ = crate::leanh::lean_box(0);
                v_xs_x27_1321_ = lean_array_fset(v_es_1308_, v_j_1313_, v___x_1320_);
                match crate::leanh::lean_obj_tag(v_v_1319_) {
                    0 => {
                        v_key_1328_ = crate::leanh::lean_ctor_get(v_v_1319_, 0);
                        v_val_1329_ = crate::leanh::lean_ctor_get(v_v_1319_, 1);
                        v_isSharedCheck_1339_ = (!crate::leanh::lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1339_ == 0 {
                            v___x_1331_ = v_v_1319_;
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1329_);
                            crate::leanh::lean_inc(v_key_1328_);
                            crate::leanh::lean_dec(v_v_1319_);
                            v___x_1331_ = crate::leanh::lean_box(0);
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1340_ = crate::leanh::lean_ctor_get(v_v_1319_, 0);
                        v_isSharedCheck_1350_ = (!crate::leanh::lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1350_ == 0 {
                            v___x_1342_ = v_v_1319_;
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1340_);
                            crate::leanh::lean_dec(v_v_1319_);
                            v___x_1342_ = crate::leanh::lean_box(0);
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1351_, 0, v_x_1306_);
                        crate::leanh::lean_ctor_set(v___x_1351_, 1, v_x_1307_);
                        v___y_1323_ = v___x_1351_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1324_ = lean_array_fset(v_xs_x27_1321_, v_j_1313_, v___y_1323_);
                crate::leanh::lean_dec(v_j_1313_);
                if v_isShared_1318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1324_);
                    v___x_1326_ = v___x_1317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1326_;
            }
            4 => {
                v___x_1333_ = l_Lean_instBEqMVarId_beq(v_x_1306_, v_key_1328_);
                if v___x_1333_ == 0 {
                    crate::leanh::lean_del_object(v___x_1331_);
                    v___x_1334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1328_,
                        v_val_1329_,
                        v_x_1306_,
                        v_x_1307_,
                    );
                    v___x_1335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
                    v___y_1323_ = v___x_1335_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1329_);
                    crate::leanh::lean_dec(v_key_1328_);
                    if v_isShared_1332_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1331_, 1, v_x_1307_);
                        crate::leanh::lean_ctor_set(v___x_1331_, 0, v_x_1306_);
                        v___x_1337_ = v___x_1331_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_x_1306_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_x_1307_);
                        v___x_1337_ = v_reuseFailAlloc_1338_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1323_ = v___x_1337_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1344_ = lean_usize_shift_right(v_x_1304_, v___x_1309_);
                v___x_1345_ = lean_usize_add(v_x_1305_, v___x_1310_);
                v___x_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_node_1340_, v___x_1344_, v___x_1345_, v_x_1306_, v_x_1307_);
                if v_isShared_1343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1346_);
                    v___x_1348_ = v___x_1342_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
                    v___x_1348_ = v_reuseFailAlloc_1349_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1323_ = v___x_1348_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v___x_1360_, v_x_1306_, v_x_1307_);
                v___x_1369_ = 7usize;
                v___x_1370_ = lean_usize_dec_le(v___x_1369_, v_x_1305_);
                if v___x_1370_ == 0 {
                    v___x_1371_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1361_);
                    v___x_1372_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1373_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
                    crate::leanh::lean_dec(v___x_1371_);
                    v___y_1363_ = v___x_1373_;
                    state = 10;
                    continue;
                } else {
                    v___y_1363_ = v___x_1370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1363_ == 0 {
                    v_ks_1364_ = crate::leanh::lean_ctor_get(v_newNode_1361_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1364_);
                    v_vs_1365_ = crate::leanh::lean_ctor_get(v_newNode_1361_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1365_);
                    crate::leanh::lean_dec_ref(v_newNode_1361_);
                    v___x_1366_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2);
                    v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_1305_, v_ks_1364_, v_vs_1365_, v___x_1366_, v___x_1367_);
                    crate::leanh::lean_dec_ref(v_vs_1365_);
                    crate::leanh::lean_dec_ref(v_ks_1364_);
                    return v___x_1368_;
                } else {
                    return v_newNode_1361_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(
    mut v_depth_1376_: usize,
    mut v_keys_1377_: *mut crate::leanh::LeanObject,
    mut v_vals_1378_: *mut crate::leanh::LeanObject,
    mut v_i_1379_: *mut crate::leanh::LeanObject,
    mut v_entries_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v_k_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u64 = 0;
    let mut v_h_1386_: usize = 0;
    let mut v___x_1387_: usize = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v_h_1392_: usize = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1381_ = lean_array_get_size(v_keys_1377_);
                v___x_1382_ = lean_nat_dec_lt(v_i_1379_, v___x_1381_);
                if v___x_1382_ == 0 {
                    crate::leanh::lean_dec(v_i_1379_);
                    return v_entries_1380_;
                } else {
                    v_k_1383_ = lean_array_fget_borrowed(v_keys_1377_, v_i_1379_);
                    v_v_1384_ = lean_array_fget_borrowed(v_vals_1378_, v_i_1379_);
                    v___x_1385_ = l_Lean_instHashableMVarId_hash(v_k_1383_);
                    v_h_1386_ = lean_uint64_to_usize(v___x_1385_);
                    v___x_1387_ = 5usize;
                    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1389_ = 1usize;
                    v___x_1390_ = lean_usize_sub(v_depth_1376_, v___x_1389_);
                    v___x_1391_ = lean_usize_mul(v___x_1387_, v___x_1390_);
                    v_h_1392_ = lean_usize_shift_right(v_h_1386_, v___x_1391_);
                    v___x_1393_ = lean_nat_add(v_i_1379_, v___x_1388_);
                    crate::leanh::lean_dec(v_i_1379_);
                    crate::leanh::lean_inc(v_v_1384_);
                    crate::leanh::lean_inc(v_k_1383_);
                    v___x_1394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_entries_1380_, v_h_1392_, v_depth_1376_, v_k_1383_, v_v_1384_);
                    v_i_1379_ = v___x_1393_;
                    v_entries_1380_ = v___x_1394_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_depth_1396_: *mut crate::leanh::LeanObject,
    mut v_keys_1397_: *mut crate::leanh::LeanObject,
    mut v_vals_1398_: *mut crate::leanh::LeanObject,
    mut v_i_1399_: *mut crate::leanh::LeanObject,
    mut v_entries_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1401_: usize = 0;
    let mut v_res_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1401_ = crate::leanh::lean_unbox_usize(v_depth_1396_);
    crate::leanh::lean_dec(v_depth_1396_);
    v_res_1402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_1401_, v_keys_1397_, v_vals_1398_, v_i_1399_, v_entries_1400_);
    crate::leanh::lean_dec_ref(v_vals_1398_);
    crate::leanh::lean_dec_ref(v_keys_1397_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(
    mut v_x_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
    mut v_x_1405_: *mut crate::leanh::LeanObject,
    mut v_x_1406_: *mut crate::leanh::LeanObject,
    mut v_x_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6152__boxed_1408_: usize = 0;
    let mut v_x_6153__boxed_1409_: usize = 0;
    let mut v_res_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6152__boxed_1408_ = crate::leanh::lean_unbox_usize(v_x_1404_);
    crate::leanh::lean_dec(v_x_1404_);
    v_x_6153__boxed_1409_ = crate::leanh::lean_unbox_usize(v_x_1405_);
    crate::leanh::lean_dec(v_x_1405_);
    v_res_1410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1403_, v_x_6152__boxed_1408_, v_x_6153__boxed_1409_, v_x_1406_, v_x_1407_);
    return v_res_1410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(
    mut v_x_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
    mut v_x_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: u64 = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Lean_instHashableMVarId_hash(v_x_1412_);
    v___x_1415_ = lean_uint64_to_usize(v___x_1414_);
    v___x_1416_ = 1usize;
    v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1411_, v___x_1415_, v___x_1416_, v_x_1412_, v_x_1413_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
    mut v_mvarId_1418_: *mut crate::leanh::LeanObject,
    mut v_val_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_depth_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1422_ = lean_st_ref_take(v___y_1420_);
                v_mctx_1423_ = crate::leanh::lean_ctor_get(v___x_1422_, 0);
                v_cache_1424_ = crate::leanh::lean_ctor_get(v___x_1422_, 1);
                v_zetaDeltaFVarIds_1425_ = crate::leanh::lean_ctor_get(v___x_1422_, 2);
                v_postponed_1426_ = crate::leanh::lean_ctor_get(v___x_1422_, 3);
                v_diag_1427_ = crate::leanh::lean_ctor_get(v___x_1422_, 4);
                v_isSharedCheck_1455_ = (!crate::leanh::lean_is_exclusive(v___x_1422_)) as u8;
                if v_isSharedCheck_1455_ == 0 {
                    v___x_1429_ = v___x_1422_;
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1427_);
                    crate::leanh::lean_inc(v_postponed_1426_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1425_);
                    crate::leanh::lean_inc(v_cache_1424_);
                    crate::leanh::lean_inc(v_mctx_1423_);
                    crate::leanh::lean_dec(v___x_1422_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1431_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 0);
                v_levelAssignDepth_1432_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 1);
                v_lmvarCounter_1433_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 2);
                v_mvarCounter_1434_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 3);
                v_lDecls_1435_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 4);
                v_decls_1436_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 5);
                v_userNames_1437_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 6);
                v_lAssignment_1438_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 7);
                v_eAssignment_1439_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 8);
                v_dAssignment_1440_ = crate::leanh::lean_ctor_get(v_mctx_1423_, 9);
                v_isSharedCheck_1454_ = (!crate::leanh::lean_is_exclusive(v_mctx_1423_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v___x_1442_ = v_mctx_1423_;
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1440_);
                    crate::leanh::lean_inc(v_eAssignment_1439_);
                    crate::leanh::lean_inc(v_lAssignment_1438_);
                    crate::leanh::lean_inc(v_userNames_1437_);
                    crate::leanh::lean_inc(v_decls_1436_);
                    crate::leanh::lean_inc(v_lDecls_1435_);
                    crate::leanh::lean_inc(v_mvarCounter_1434_);
                    crate::leanh::lean_inc(v_lmvarCounter_1433_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1432_);
                    crate::leanh::lean_inc(v_depth_1431_);
                    crate::leanh::lean_dec(v_mctx_1423_);
                    v___x_1442_ = crate::leanh::lean_box(0);
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_1439_, v_mvarId_1418_, v_val_1419_);
                if v_isShared_1443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1442_, 8, v___x_1444_);
                    v___x_1446_ = v___x_1442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_depth_1431_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1453_,
                        1,
                        v_levelAssignDepth_1432_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_lmvarCounter_1433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_mvarCounter_1434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_lDecls_1435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 5, v_decls_1436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 6, v_userNames_1437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 7, v_lAssignment_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 8, v___x_1444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 9, v_dAssignment_1440_);
                    v___x_1446_ = v_reuseFailAlloc_1453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v___x_1446_);
                    v___x_1448_ = v___x_1429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_cache_1424_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1452_,
                        2,
                        v_zetaDeltaFVarIds_1425_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_postponed_1426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_diag_1427_);
                    v___x_1448_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1449_ = lean_st_ref_set(v___y_1420_, v___x_1448_);
                v___x_1450_ = crate::leanh::lean_box(0);
                v___x_1451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(
    mut v_mvarId_1456_: *mut crate::leanh::LeanObject,
    mut v_val_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1456_,
            v_val_1457_,
            v___y_1458_,
        );
    crate::leanh::lean_dec(v___y_1458_);
    return v_res_1460_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0;
    v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1,
    );
    v___x_1465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(
    mut v___x_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v___x_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
    mut v_mvar_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_1467_);
                v___x_1476_ = l_Lean_Meta_isExprDefEq(
                    v___x_1466_,
                    v_a_1467_,
                    v___y_1471_,
                    v___y_1472_,
                    v___y_1473_,
                    v___y_1474_,
                );
                if crate::leanh::lean_obj_tag(v___x_1476_) == 0 {
                    v_a_1477_ = crate::leanh::lean_ctor_get(v___x_1476_, 0);
                    crate::leanh::lean_inc(v_a_1477_);
                    crate::leanh::lean_dec_ref_known(v___x_1476_, 1);
                    v___x_1478_ = (crate::leanh::lean_unbox(v_a_1477_) as u8);
                    crate::leanh::lean_dec(v_a_1477_);
                    if v___x_1478_ == 0 {
                        v___x_1479_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2,
                        );
                        v___x_1480_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_1468_,
                            v_a_1469_,
                            v___x_1479_,
                            v___y_1471_,
                            v___y_1472_,
                            v___y_1473_,
                            v___y_1474_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1480_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1480_, 1);
                            v___x_1481_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                            return v___x_1481_;
                        } else {
                            crate::leanh::lean_dec(v_mvar_1470_);
                            crate::leanh::lean_dec_ref(v_a_1467_);
                            return v___x_1480_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1469_);
                        crate::leanh::lean_dec(v___x_1468_);
                        v___x_1482_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                        return v___x_1482_;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvar_1470_);
                    crate::leanh::lean_dec(v_a_1469_);
                    crate::leanh::lean_dec(v___x_1468_);
                    crate::leanh::lean_dec_ref(v_a_1467_);
                    v_a_1483_ = crate::leanh::lean_ctor_get(v___x_1476_, 0);
                    v_isSharedCheck_1490_ = (!crate::leanh::lean_is_exclusive(v___x_1476_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1485_ = v___x_1476_;
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1483_);
                        crate::leanh::lean_dec(v___x_1476_);
                        v___x_1485_ = crate::leanh::lean_box(0);
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1486_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(
    mut v___x_1491_: *mut crate::leanh::LeanObject,
    mut v_a_1492_: *mut crate::leanh::LeanObject,
    mut v___x_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
    mut v_mvar_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(
        v___x_1491_,
        v_a_1492_,
        v___x_1493_,
        v_a_1494_,
        v_mvar_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
    );
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
    mut v___x_1502_: *mut crate::leanh::LeanObject,
    mut v___x_1503_: u8,
    mut v___x_1504_: u8,
    mut v___x_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_mvar_1507_: *mut crate::leanh::LeanObject,
    mut v_e_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1514_ = 1;
                v___x_1515_ = l_Lean_Meta_mkLetFVars(
                    v___x_1502_,
                    v_e_1508_,
                    v___x_1503_,
                    v___x_1504_,
                    v___x_1514_,
                    v___y_1509_,
                    v___y_1510_,
                    v___y_1511_,
                    v___y_1512_,
                );
                if crate::leanh::lean_obj_tag(v___x_1515_) == 0 {
                    v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                    crate::leanh::lean_inc(v_a_1516_);
                    crate::leanh::lean_dec_ref_known(v___x_1515_, 1);
                    crate::leanh::lean_inc_n(v_mvar_1507_, 2);
                    v___x_1517_ = l_Lean_Expr_mvar___override(v_mvar_1507_);
                    v___f_1518_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_1518_, 0, v___x_1517_);
                    crate::leanh::lean_closure_set(v___f_1518_, 1, v_a_1516_);
                    crate::leanh::lean_closure_set(v___f_1518_, 2, v___x_1505_);
                    crate::leanh::lean_closure_set(v___f_1518_, 3, v_a_1506_);
                    crate::leanh::lean_closure_set(v___f_1518_, 4, v_mvar_1507_);
                    v___x_1519_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_1507_, v___f_1518_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
                    return v___x_1519_;
                } else {
                    crate::leanh::lean_dec(v_mvar_1507_);
                    crate::leanh::lean_dec(v_a_1506_);
                    crate::leanh::lean_dec(v___x_1505_);
                    v_a_1520_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                    v_isSharedCheck_1527_ = (!crate::leanh::lean_is_exclusive(v___x_1515_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1522_ = v___x_1515_;
                        v_isShared_1523_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1520_);
                        crate::leanh::lean_dec(v___x_1515_);
                        v___x_1522_ = crate::leanh::lean_box(0);
                        v_isShared_1523_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1523_ == 0 {
                    v___x_1525_ = v___x_1522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(
    mut v___x_1528_: *mut crate::leanh::LeanObject,
    mut v___x_1529_: *mut crate::leanh::LeanObject,
    mut v___x_1530_: *mut crate::leanh::LeanObject,
    mut v___x_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_mvar_1533_: *mut crate::leanh::LeanObject,
    mut v_e_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6446__boxed_1540_: u8 = 0;
    let mut v___x_6447__boxed_1541_: u8 = 0;
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6446__boxed_1540_ = (crate::leanh::lean_unbox(v___x_1529_) as u8);
    v___x_6447__boxed_1541_ = (crate::leanh::lean_unbox(v___x_1530_) as u8);
    v_res_1542_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
        v___x_1528_,
        v___x_6446__boxed_1540_,
        v___x_6447__boxed_1541_,
        v___x_1531_,
        v_a_1532_,
        v_mvar_1533_,
        v_e_1534_,
        v___y_1535_,
        v___y_1536_,
        v___y_1537_,
        v___y_1538_,
    );
    crate::leanh::lean_dec(v___y_1538_);
    crate::leanh::lean_dec_ref(v___y_1537_);
    crate::leanh::lean_dec(v___y_1536_);
    crate::leanh::lean_dec_ref(v___y_1535_);
    crate::leanh::lean_dec_ref(v___x_1528_);
    return v_res_1542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(
    mut v_sz_1543_: usize,
    mut v_i_1544_: usize,
    mut v_bs_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: u8 = 0;
    let mut v_v_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
                if v___x_1546_ == 0 {
                    return v_bs_1545_;
                } else {
                    v_v_1547_ = lean_array_uget(v_bs_1545_, v_i_1544_);
                    v___x_1548_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1549_ = lean_array_uset(v_bs_1545_, v_i_1544_, v___x_1548_);
                    v___x_1550_ = l_Lean_Expr_fvar___override(v_v_1547_);
                    v___x_1551_ = 1usize;
                    v___x_1552_ = lean_usize_add(v_i_1544_, v___x_1551_);
                    v___x_1553_ = lean_array_uset(v_bs_x27_1549_, v_i_1544_, v___x_1550_);
                    v_i_1544_ = v___x_1552_;
                    v_bs_1545_ = v___x_1553_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(
    mut v_sz_1555_: *mut crate::leanh::LeanObject,
    mut v_i_1556_: *mut crate::leanh::LeanObject,
    mut v_bs_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1558_: usize = 0;
    let mut v_i_boxed_1559_: usize = 0;
    let mut v_res_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1558_ = crate::leanh::lean_unbox_usize(v_sz_1555_);
    crate::leanh::lean_dec(v_sz_1555_);
    v_i_boxed_1559_ = crate::leanh::lean_unbox_usize(v_i_1556_);
    crate::leanh::lean_dec(v_i_1556_);
    v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_1558_, v_i_boxed_1559_, v_bs_1557_);
    return v_res_1560_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0;
    v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1,
    );
    v___x_1565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(
    mut v___x_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v___x_1568_: usize,
    mut v___x_1569_: u8,
    mut v___x_1570_: u8,
    mut v___x_1571_: *mut crate::leanh::LeanObject,
    mut v_snd_1572_: *mut crate::leanh::LeanObject,
    mut v_fst_1573_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1574_: *mut crate::leanh::LeanObject,
    mut v_es_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v_sz_1594_: usize = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1611_: u8 = 0;
    let mut v_unused_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v_a_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = l_Lean_instInhabitedExpr;
                v___x_1583_ = lean_array_get_borrowed(v___x_1582_, v_es_1575_, v___x_1566_);
                v___x_1646_ = lean_array_get_size(v_fvarIds_1574_);
                v___x_1647_ = lean_nat_dec_eq(v___x_1646_, v___x_1566_);
                if v___x_1647_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1648_ = lean_expr_eqv(v_fst_1573_, v___x_1583_);
                    if v___x_1648_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1649_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2,
                        );
                        crate::leanh::lean_inc(v_a_1567_);
                        crate::leanh::lean_inc(v___x_1571_);
                        v___x_1650_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_1571_,
                            v_a_1567_,
                            v___x_1649_,
                            v___y_1577_,
                            v___y_1578_,
                            v___y_1579_,
                            v___y_1580_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1650_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1650_, 1);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_fvarIds_1574_);
                            crate::leanh::lean_dec_ref(v_snd_1572_);
                            crate::leanh::lean_dec(v___x_1571_);
                            crate::leanh::lean_dec(v_a_1567_);
                            v_a_1651_ = crate::leanh::lean_ctor_get(v___x_1650_, 0);
                            v_isSharedCheck_1658_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1650_)) as u8;
                            if v_isSharedCheck_1658_ == 0 {
                                v___x_1653_ = v___x_1650_;
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1651_);
                                crate::leanh::lean_dec(v___x_1650_);
                                v___x_1653_ = crate::leanh::lean_box(0);
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1567_);
                v___x_1585_ = l_Lean_MVarId_getTag(
                    v_a_1567_,
                    v___y_1577_,
                    v___y_1578_,
                    v___y_1579_,
                    v___y_1580_,
                );
                if crate::leanh::lean_obj_tag(v___x_1585_) == 0 {
                    v_a_1586_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                    crate::leanh::lean_inc(v_a_1586_);
                    crate::leanh::lean_dec_ref_known(v___x_1585_, 1);
                    crate::leanh::lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                        v___x_1583_,
                        v_a_1586_,
                        v___y_1577_,
                        v___y_1578_,
                        v___y_1579_,
                        v___y_1580_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1587_) == 0 {
                        v_a_1588_ = crate::leanh::lean_ctor_get(v___x_1587_, 0);
                        crate::leanh::lean_inc(v_a_1588_);
                        crate::leanh::lean_dec_ref_known(v___x_1587_, 1);
                        v_fst_1589_ = crate::leanh::lean_ctor_get(v_a_1588_, 0);
                        v_snd_1590_ = crate::leanh::lean_ctor_get(v_a_1588_, 1);
                        v_isSharedCheck_1629_ = (!crate::leanh::lean_is_exclusive(v_a_1588_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1592_ = v_a_1588_;
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1590_);
                            crate::leanh::lean_inc(v_fst_1589_);
                            crate::leanh::lean_dec(v_a_1588_);
                            v___x_1592_ = crate::leanh::lean_box(0);
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvarIds_1574_);
                        crate::leanh::lean_dec_ref(v_snd_1572_);
                        crate::leanh::lean_dec(v___x_1571_);
                        crate::leanh::lean_dec(v_a_1567_);
                        v_a_1630_ = crate::leanh::lean_ctor_get(v___x_1587_, 0);
                        v_isSharedCheck_1637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1587_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1587_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1630_);
                            crate::leanh::lean_dec(v___x_1587_);
                            v___x_1632_ = crate::leanh::lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fvarIds_1574_);
                    crate::leanh::lean_dec_ref(v_snd_1572_);
                    crate::leanh::lean_dec(v___x_1571_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v_a_1638_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                    v_isSharedCheck_1645_ = (!crate::leanh::lean_is_exclusive(v___x_1585_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1640_ = v___x_1585_;
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1638_);
                        crate::leanh::lean_dec(v___x_1585_);
                        v___x_1640_ = crate::leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_sz_1594_ = lean_array_size(v_fvarIds_1574_);
                crate::leanh::lean_inc_ref(v_fvarIds_1574_);
                v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_1594_, v___x_1568_, v_fvarIds_1574_);
                v___x_1596_ = l_Lean_Expr_mvarId_x21(v_fst_1589_);
                crate::leanh::lean_dec(v_fst_1589_);
                crate::leanh::lean_inc(v_a_1567_);
                crate::leanh::lean_inc(v___x_1571_);
                v___x_1597_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
                    v___x_1595_,
                    v___x_1569_,
                    v___x_1570_,
                    v___x_1571_,
                    v_a_1567_,
                    v___x_1596_,
                    v_snd_1572_,
                    v___y_1577_,
                    v___y_1578_,
                    v___y_1579_,
                    v___y_1580_,
                );
                if crate::leanh::lean_obj_tag(v___x_1597_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1597_, 1);
                    crate::leanh::lean_inc(v_snd_1590_);
                    crate::leanh::lean_inc(v_a_1567_);
                    v___x_1598_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
                        v___x_1595_,
                        v___x_1569_,
                        v___x_1570_,
                        v___x_1571_,
                        v_a_1567_,
                        v_a_1567_,
                        v_snd_1590_,
                        v___y_1577_,
                        v___y_1578_,
                        v___y_1579_,
                        v___y_1580_,
                    );
                    crate::leanh::lean_dec_ref(v___x_1595_);
                    if crate::leanh::lean_obj_tag(v___x_1598_) == 0 {
                        v_isSharedCheck_1611_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1611_ == 0 {
                            v_unused_1612_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                            crate::leanh::lean_dec(v_unused_1612_);
                            v___x_1600_ = v___x_1598_;
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1598_);
                            v___x_1600_ = crate::leanh::lean_box(0);
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1592_);
                        crate::leanh::lean_dec(v_snd_1590_);
                        crate::leanh::lean_dec_ref(v_fvarIds_1574_);
                        v_a_1613_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                        v_isSharedCheck_1620_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1620_ == 0 {
                            v___x_1615_ = v___x_1598_;
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1613_);
                            crate::leanh::lean_dec(v___x_1598_);
                            v___x_1615_ = crate::leanh::lean_box(0);
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1595_);
                    crate::leanh::lean_del_object(v___x_1592_);
                    crate::leanh::lean_dec(v_snd_1590_);
                    crate::leanh::lean_dec_ref(v_fvarIds_1574_);
                    crate::leanh::lean_dec(v___x_1571_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v_a_1621_ = crate::leanh::lean_ctor_get(v___x_1597_, 0);
                    v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___x_1597_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1597_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1621_);
                        crate::leanh::lean_dec(v___x_1597_);
                        v___x_1623_ = crate::leanh::lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1602_ = l_Lean_Expr_mvarId_x21(v_snd_1590_);
                crate::leanh::lean_dec(v_snd_1590_);
                v___x_1603_ = crate::leanh::lean_box(0);
                v___x_1604_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                crate::leanh::lean_ctor_set(v___x_1604_, 1, v___x_1603_);
                if v_isShared_1593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1592_, 1, v___x_1604_);
                    crate::leanh::lean_ctor_set(v___x_1592_, 0, v_fvarIds_1574_);
                    v___x_1606_ = v___x_1592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fvarIds_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1604_);
                    v___x_1606_ = v_reuseFailAlloc_1610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1606_);
                    v___x_1608_ = v___x_1600_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
                    v___x_1608_ = v_reuseFailAlloc_1609_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1608_;
            }
            6 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1618_;
            }
            8 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1626_;
            }
            10 => {
                if v_isShared_1633_ == 0 {
                    v___x_1635_ = v___x_1632_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
                    v___x_1635_ = v_reuseFailAlloc_1636_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1635_;
            }
            12 => {
                if v_isShared_1641_ == 0 {
                    v___x_1643_ = v___x_1640_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
                    v___x_1643_ = v_reuseFailAlloc_1644_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1643_;
            }
            14 => {
                if v_isShared_1654_ == 0 {
                    v___x_1656_ = v___x_1653_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(
    mut v___x_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v___x_1661_: *mut crate::leanh::LeanObject,
    mut v___x_1662_: *mut crate::leanh::LeanObject,
    mut v___x_1663_: *mut crate::leanh::LeanObject,
    mut v___x_1664_: *mut crate::leanh::LeanObject,
    mut v_snd_1665_: *mut crate::leanh::LeanObject,
    mut v_fst_1666_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1667_: *mut crate::leanh::LeanObject,
    mut v_es_1668_: *mut crate::leanh::LeanObject,
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6529__boxed_1675_: usize = 0;
    let mut v___x_6530__boxed_1676_: u8 = 0;
    let mut v___x_6531__boxed_1677_: u8 = 0;
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6529__boxed_1675_ = crate::leanh::lean_unbox_usize(v___x_1661_);
    crate::leanh::lean_dec(v___x_1661_);
    v___x_6530__boxed_1676_ = (crate::leanh::lean_unbox(v___x_1662_) as u8);
    v___x_6531__boxed_1677_ = (crate::leanh::lean_unbox(v___x_1663_) as u8);
    v_res_1678_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(
        v___x_1659_,
        v_a_1660_,
        v___x_6529__boxed_1675_,
        v___x_6530__boxed_1676_,
        v___x_6531__boxed_1677_,
        v___x_1664_,
        v_snd_1665_,
        v_fst_1666_,
        v_fvarIds_1667_,
        v_es_1668_,
        v_x_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
    );
    crate::leanh::lean_dec(v___y_1673_);
    crate::leanh::lean_dec_ref(v___y_1672_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v___y_1670_);
    crate::leanh::lean_dec(v_x_1669_);
    crate::leanh::lean_dec_ref(v_es_1668_);
    crate::leanh::lean_dec_ref(v_fst_1666_);
    crate::leanh::lean_dec(v___x_1659_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(
    mut v___x_1682_: *mut crate::leanh::LeanObject,
    mut v___x_1683_: usize,
    mut v___x_1684_: u8,
    mut v___x_1685_: u8,
    mut v_snd_1686_: *mut crate::leanh::LeanObject,
    mut v_fst_1687_: *mut crate::leanh::LeanObject,
    mut v___x_1688_: *mut crate::leanh::LeanObject,
    mut v___x_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_unused_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut v_a_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1700_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1692_,
                    v___y_1695_,
                    v___y_1696_,
                    v___y_1697_,
                    v___y_1698_,
                );
                if crate::leanh::lean_obj_tag(v___x_1700_) == 0 {
                    v_a_1701_ = crate::leanh::lean_ctor_get(v___x_1700_, 0);
                    crate::leanh::lean_inc_n(v_a_1701_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1700_, 1);
                    v___x_1702_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1;
                    v___x_1703_ = l_Lean_MVarId_checkNotAssigned(
                        v_a_1701_,
                        v___x_1702_,
                        v___y_1695_,
                        v___y_1696_,
                        v___y_1697_,
                        v___y_1698_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1703_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1703_, 1);
                        v___x_1704_ = crate::leanh::lean_box_usize(v___x_1683_);
                        v___x_1705_ = crate::leanh::lean_box((v___x_1684_) as usize);
                        v___x_1706_ = crate::leanh::lean_box((v___x_1685_) as usize);
                        crate::leanh::lean_inc_ref(v_fst_1687_);
                        v___f_1707_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            8,
                        );
                        crate::leanh::lean_closure_set(v___f_1707_, 0, v___x_1682_);
                        crate::leanh::lean_closure_set(v___f_1707_, 1, v_a_1701_);
                        crate::leanh::lean_closure_set(v___f_1707_, 2, v___x_1704_);
                        crate::leanh::lean_closure_set(v___f_1707_, 3, v___x_1705_);
                        crate::leanh::lean_closure_set(v___f_1707_, 4, v___x_1706_);
                        crate::leanh::lean_closure_set(v___f_1707_, 5, v___x_1702_);
                        crate::leanh::lean_closure_set(v___f_1707_, 6, v_snd_1686_);
                        crate::leanh::lean_closure_set(v___f_1707_, 7, v_fst_1687_);
                        v___x_1708_ = lean_mk_empty_array_with_capacity(v___x_1688_);
                        v___x_1709_ = lean_array_push(v___x_1708_, v_fst_1687_);
                        v___x_1710_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_1709_, v___x_1689_, v___f_1707_, v_a_1690_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
                        if crate::leanh::lean_obj_tag(v___x_1710_) == 0 {
                            v_a_1711_ = crate::leanh::lean_ctor_get(v___x_1710_, 0);
                            crate::leanh::lean_inc(v_a_1711_);
                            crate::leanh::lean_dec_ref_known(v___x_1710_, 1);
                            v_fst_1712_ = crate::leanh::lean_ctor_get(v_a_1711_, 0);
                            crate::leanh::lean_inc(v_fst_1712_);
                            v_snd_1713_ = crate::leanh::lean_ctor_get(v_a_1711_, 1);
                            crate::leanh::lean_inc(v_snd_1713_);
                            crate::leanh::lean_dec(v_a_1711_);
                            v___x_1714_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v_snd_1713_,
                                v___y_1692_,
                                v___y_1695_,
                                v___y_1696_,
                                v___y_1697_,
                                v___y_1698_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1714_) == 0 {
                                v_isSharedCheck_1721_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1721_ == 0 {
                                    v_unused_1722_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                                    crate::leanh::lean_dec(v_unused_1722_);
                                    v___x_1716_ = v___x_1714_;
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1714_);
                                    v___x_1716_ = crate::leanh::lean_box(0);
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_1712_);
                                v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                                v_isSharedCheck_1730_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1730_ == 0 {
                                    v___x_1725_ = v___x_1714_;
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1723_);
                                    crate::leanh::lean_dec(v___x_1714_);
                                    v___x_1725_ = crate::leanh::lean_box(0);
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1731_ = crate::leanh::lean_ctor_get(v___x_1710_, 0);
                            v_isSharedCheck_1738_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1710_)) as u8;
                            if v_isSharedCheck_1738_ == 0 {
                                v___x_1733_ = v___x_1710_;
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1731_);
                                crate::leanh::lean_dec(v___x_1710_);
                                v___x_1733_ = crate::leanh::lean_box(0);
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1701_);
                        crate::leanh::lean_dec(v___x_1689_);
                        crate::leanh::lean_dec_ref(v_fst_1687_);
                        crate::leanh::lean_dec_ref(v_snd_1686_);
                        crate::leanh::lean_dec(v___x_1682_);
                        v_a_1739_ = crate::leanh::lean_ctor_get(v___x_1703_, 0);
                        v_isSharedCheck_1746_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1703_)) as u8;
                        if v_isSharedCheck_1746_ == 0 {
                            v___x_1741_ = v___x_1703_;
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1739_);
                            crate::leanh::lean_dec(v___x_1703_);
                            v___x_1741_ = crate::leanh::lean_box(0);
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1689_);
                    crate::leanh::lean_dec_ref(v_fst_1687_);
                    crate::leanh::lean_dec_ref(v_snd_1686_);
                    crate::leanh::lean_dec(v___x_1682_);
                    v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1754_ = (!crate::leanh::lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v___x_1749_ = v___x_1700_;
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1747_);
                        crate::leanh::lean_dec(v___x_1700_);
                        v___x_1749_ = crate::leanh::lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1716_, 0, v_fst_1712_);
                    v___x_1719_ = v___x_1716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1712_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1719_;
            }
            3 => {
                if v_isShared_1726_ == 0 {
                    v___x_1728_ = v___x_1725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
                    v___x_1728_ = v_reuseFailAlloc_1729_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1728_;
            }
            5 => {
                if v_isShared_1734_ == 0 {
                    v___x_1736_ = v___x_1733_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
                    v___x_1736_ = v_reuseFailAlloc_1737_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1736_;
            }
            7 => {
                if v_isShared_1742_ == 0 {
                    v___x_1744_ = v___x_1741_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1744_;
            }
            9 => {
                if v_isShared_1750_ == 0 {
                    v___x_1752_ = v___x_1749_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1756_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_1757_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1758_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_snd_1759_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_fst_1760_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_1761_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_1762_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_1763_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1764_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1765_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1766_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1767_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1768_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1769_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1770_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1771_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1772_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_6736__boxed_1773_: usize = 0;
    let mut v___x_6737__boxed_1774_: u8 = 0;
    let mut v___x_6738__boxed_1775_: u8 = 0;
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6736__boxed_1773_ = crate::leanh::lean_unbox_usize(v___x_1756_);
    crate::leanh::lean_dec(v___x_1756_);
    v___x_6737__boxed_1774_ = (crate::leanh::lean_unbox(v___x_1757_) as u8);
    v___x_6738__boxed_1775_ = (crate::leanh::lean_unbox(v___x_1758_) as u8);
    v_res_1776_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(
        v___x_1755_,
        v___x_6736__boxed_1773_,
        v___x_6737__boxed_1774_,
        v___x_6738__boxed_1775_,
        v_snd_1759_,
        v_fst_1760_,
        v___x_1761_,
        v___x_1762_,
        v_a_1763_,
        v___y_1764_,
        v___y_1765_,
        v___y_1766_,
        v___y_1767_,
        v___y_1768_,
        v___y_1769_,
        v___y_1770_,
        v___y_1771_,
    );
    crate::leanh::lean_dec(v___y_1771_);
    crate::leanh::lean_dec_ref(v___y_1770_);
    crate::leanh::lean_dec(v___y_1769_);
    crate::leanh::lean_dec_ref(v___y_1768_);
    crate::leanh::lean_dec(v___y_1767_);
    crate::leanh::lean_dec_ref(v___y_1766_);
    crate::leanh::lean_dec(v___y_1765_);
    crate::leanh::lean_dec_ref(v___y_1764_);
    crate::leanh::lean_dec_ref(v_a_1763_);
    crate::leanh::lean_dec(v___x_1761_);
    return v_res_1776_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(
    mut v_sz_1777_: usize,
    mut v_i_1778_: usize,
    mut v_bs_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: u8 = 0;
    let mut v_v_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1780_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
                if v___x_1780_ == 0 {
                    return v_bs_1779_;
                } else {
                    v_v_1781_ = lean_array_uget(v_bs_1779_, v_i_1778_);
                    v___x_1782_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1783_ = lean_array_uset(v_bs_1779_, v_i_1778_, v___x_1782_);
                    v___x_1784_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_1781_);
                    crate::leanh::lean_dec(v_v_1781_);
                    v___x_1785_ = 1usize;
                    v___x_1786_ = lean_usize_add(v_i_1778_, v___x_1785_);
                    v___x_1787_ = lean_array_uset(v_bs_x27_1783_, v_i_1778_, v___x_1784_);
                    v_i_1778_ = v___x_1786_;
                    v_bs_1779_ = v___x_1787_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(
    mut v_sz_1789_: *mut crate::leanh::LeanObject,
    mut v_i_1790_: *mut crate::leanh::LeanObject,
    mut v_bs_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1792_: usize = 0;
    let mut v_i_boxed_1793_: usize = 0;
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1792_ = crate::leanh::lean_unbox_usize(v_sz_1789_);
    crate::leanh::lean_dec(v_sz_1789_);
    v_i_boxed_1793_ = crate::leanh::lean_unbox_usize(v_i_1790_);
    crate::leanh::lean_dec(v_i_1790_);
    v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_1792_, v_i_boxed_1793_, v_bs_1791_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets(
    mut v_x_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1843_: usize = 0;
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: usize = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
                crate::leanh::lean_inc(v_x_1814_);
                v___x_1825_ = l_Lean_Syntax_isOfKind(v_x_1814_, v___x_1824_);
                if v___x_1825_ == 0 {
                    crate::leanh::lean_dec(v_x_1814_);
                    v___x_1826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_1826_;
                } else {
                    v___x_1827_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1828_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1827_);
                    v___x_1829_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    crate::leanh::lean_inc(v___x_1828_);
                    v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1828_, v___x_1829_);
                    if v___x_1830_ == 0 {
                        crate::leanh::lean_dec(v___x_1828_);
                        crate::leanh::lean_dec(v_x_1814_);
                        v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_1831_;
                    } else {
                        v___x_1832_ = 0;
                        v___x_1833_ = crate::leanh::lean_alloc_ctor(0, 0, (11) as u32);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 0 as u32, v___x_1832_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 1 as u32, v___x_1830_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 2 as u32, v___x_1832_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 3 as u32, v___x_1830_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 4 as u32, v___x_1830_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 5 as u32, v___x_1832_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 6 as u32, v___x_1830_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 7 as u32, v___x_1830_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 8 as u32, v___x_1832_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 9 as u32, v___x_1832_);
                        crate::leanh::lean_ctor_set_uint8(v___x_1833_, 10 as u32, v___x_1832_);
                        v___x_1834_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
                            v___x_1828_,
                            v___x_1833_,
                            v___x_1830_,
                            v_a_1815_,
                            v_a_1821_,
                            v_a_1822_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                            v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                            crate::leanh::lean_inc(v_a_1835_);
                            crate::leanh::lean_dec_ref_known(v___x_1834_, 1);
                            v___x_1836_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
                                v_a_1816_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1836_) == 0 {
                                v_a_1837_ = crate::leanh::lean_ctor_get(v___x_1836_, 0);
                                crate::leanh::lean_inc(v_a_1837_);
                                crate::leanh::lean_dec_ref_known(v___x_1836_, 1);
                                v_fst_1838_ = crate::leanh::lean_ctor_get(v_a_1837_, 0);
                                crate::leanh::lean_inc(v_fst_1838_);
                                v_snd_1839_ = crate::leanh::lean_ctor_get(v_a_1837_, 1);
                                crate::leanh::lean_inc(v_snd_1839_);
                                crate::leanh::lean_dec(v_a_1837_);
                                v___x_1840_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_1841_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1840_);
                                crate::leanh::lean_dec(v_x_1814_);
                                v_ids_1842_ = l_Lean_Syntax_getArgs(v___x_1841_);
                                crate::leanh::lean_dec(v___x_1841_);
                                v_sz_1843_ = lean_array_size(v_ids_1842_);
                                v___x_1844_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_1845_ = 0usize;
                                crate::leanh::lean_inc_ref(v_ids_1842_);
                                v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_1843_, v___x_1845_, v_ids_1842_);
                                v___x_1847_ = lean_array_to_list(v___x_1846_);
                                v___x_1848_ =
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1;
                                v___x_1849_ = crate::leanh::lean_box((v___x_1832_) as usize);
                                v___x_1850_ = crate::leanh::lean_box((v___x_1830_) as usize);
                                v___f_1851_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed
                                        as *mut core::ffi::c_void,
                                    18,
                                    9,
                                );
                                crate::leanh::lean_closure_set(v___f_1851_, 0, v___x_1844_);
                                crate::leanh::lean_closure_set(v___f_1851_, 1, v___x_1848_);
                                crate::leanh::lean_closure_set(v___f_1851_, 2, v___x_1849_);
                                crate::leanh::lean_closure_set(v___f_1851_, 3, v___x_1850_);
                                crate::leanh::lean_closure_set(v___f_1851_, 4, v_snd_1839_);
                                crate::leanh::lean_closure_set(v___f_1851_, 5, v_fst_1838_);
                                crate::leanh::lean_closure_set(v___f_1851_, 6, v___x_1827_);
                                crate::leanh::lean_closure_set(v___f_1851_, 7, v___x_1847_);
                                crate::leanh::lean_closure_set(v___f_1851_, 8, v_a_1835_);
                                v___x_1852_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                    v___f_1851_,
                                    v_a_1815_,
                                    v_a_1816_,
                                    v_a_1817_,
                                    v_a_1818_,
                                    v_a_1819_,
                                    v_a_1820_,
                                    v_a_1821_,
                                    v_a_1822_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1852_) == 0 {
                                    v_a_1853_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                                    crate::leanh::lean_inc(v_a_1853_);
                                    crate::leanh::lean_dec_ref_known(v___x_1852_, 1);
                                    v___x_1854_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(
                                        v_ids_1842_,
                                        v_a_1853_,
                                        v_a_1815_,
                                        v_a_1816_,
                                        v_a_1817_,
                                        v_a_1818_,
                                        v_a_1819_,
                                        v_a_1820_,
                                        v_a_1821_,
                                        v_a_1822_,
                                    );
                                    return v___x_1854_;
                                } else {
                                    crate::leanh::lean_dec_ref(v_ids_1842_);
                                    v_a_1855_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                                    v_isSharedCheck_1862_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1852_)) as u8;
                                    if v_isSharedCheck_1862_ == 0 {
                                        v___x_1857_ = v___x_1852_;
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1855_);
                                        crate::leanh::lean_dec(v___x_1852_);
                                        v___x_1857_ = crate::leanh::lean_box(0);
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1835_);
                                crate::leanh::lean_dec(v_x_1814_);
                                v_a_1863_ = crate::leanh::lean_ctor_get(v___x_1836_, 0);
                                v_isSharedCheck_1870_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1836_)) as u8;
                                if v_isSharedCheck_1870_ == 0 {
                                    v___x_1865_ = v___x_1836_;
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1863_);
                                    crate::leanh::lean_dec(v___x_1836_);
                                    v___x_1865_ = crate::leanh::lean_box(0);
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_1814_);
                            v_a_1871_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                            v_isSharedCheck_1878_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                            if v_isSharedCheck_1878_ == 0 {
                                v___x_1873_ = v___x_1834_;
                                v_isShared_1874_ = v_isSharedCheck_1878_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1871_);
                                crate::leanh::lean_dec(v___x_1834_);
                                v___x_1873_ = crate::leanh::lean_box(0);
                                v_isShared_1874_ = v_isSharedCheck_1878_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1858_ == 0 {
                    v___x_1860_ = v___x_1857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1860_;
            }
            3 => {
                if v_isShared_1866_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1868_;
            }
            5 => {
                if v_isShared_1874_ == 0 {
                    v___x_1876_ = v___x_1873_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
                    v___x_1876_ = v_reuseFailAlloc_1877_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(
    mut v_x_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(
        v_x_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_,
        v_a_1887_,
    );
    crate::leanh::lean_dec(v_a_1887_);
    crate::leanh::lean_dec_ref(v_a_1886_);
    crate::leanh::lean_dec(v_a_1885_);
    crate::leanh::lean_dec_ref(v_a_1884_);
    crate::leanh::lean_dec(v_a_1883_);
    crate::leanh::lean_dec_ref(v_a_1882_);
    crate::leanh::lean_dec(v_a_1881_);
    crate::leanh::lean_dec_ref(v_a_1880_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
    mut v_mvarId_1890_: *mut crate::leanh::LeanObject,
    mut v_val_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1890_,
            v_val_1891_,
            v___y_1893_,
        );
    return v___x_1897_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(
    mut v_mvarId_1898_: *mut crate::leanh::LeanObject,
    mut v_val_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
        v_mvarId_1898_,
        v_val_1899_,
        v___y_1900_,
        v___y_1901_,
        v___y_1902_,
        v___y_1903_,
    );
    crate::leanh::lean_dec(v___y_1903_);
    crate::leanh::lean_dec_ref(v___y_1902_);
    crate::leanh::lean_dec(v___y_1901_);
    crate::leanh::lean_dec_ref(v___y_1900_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(
    mut v_00_u03b2_1906_: *mut crate::leanh::LeanObject,
    mut v_x_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_1907_, v_x_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(
    mut v_00_u03b2_1911_: *mut crate::leanh::LeanObject,
    mut v_x_1912_: *mut crate::leanh::LeanObject,
    mut v_x_1913_: usize,
    mut v_x_1914_: usize,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1912_, v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(
    mut v_00_u03b2_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
    mut v_x_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: *mut crate::leanh::LeanObject,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7111__boxed_1924_: usize = 0;
    let mut v_x_7112__boxed_1925_: usize = 0;
    let mut v_res_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7111__boxed_1924_ = crate::leanh::lean_unbox_usize(v_x_1920_);
    crate::leanh::lean_dec(v_x_1920_);
    v_x_7112__boxed_1925_ = crate::leanh::lean_unbox_usize(v_x_1921_);
    crate::leanh::lean_dec(v_x_1921_);
    v_res_1926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_1918_, v_x_1919_, v_x_7111__boxed_1924_, v_x_7112__boxed_1925_, v_x_1922_, v_x_1923_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(
    mut v_00_u03b2_1927_: *mut crate::leanh::LeanObject,
    mut v_n_1928_: *mut crate::leanh::LeanObject,
    mut v_k_1929_: *mut crate::leanh::LeanObject,
    mut v_v_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_1928_, v_k_1929_, v_v_1930_);
    return v___x_1931_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(
    mut v_00_u03b2_1932_: *mut crate::leanh::LeanObject,
    mut v_depth_1933_: usize,
    mut v_keys_1934_: *mut crate::leanh::LeanObject,
    mut v_vals_1935_: *mut crate::leanh::LeanObject,
    mut v_heq_1936_: *mut crate::leanh::LeanObject,
    mut v_i_1937_: *mut crate::leanh::LeanObject,
    mut v_entries_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_1933_, v_keys_1934_, v_vals_1935_, v_i_1937_, v_entries_1938_);
    return v___x_1939_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_1940_: *mut crate::leanh::LeanObject,
    mut v_depth_1941_: *mut crate::leanh::LeanObject,
    mut v_keys_1942_: *mut crate::leanh::LeanObject,
    mut v_vals_1943_: *mut crate::leanh::LeanObject,
    mut v_heq_1944_: *mut crate::leanh::LeanObject,
    mut v_i_1945_: *mut crate::leanh::LeanObject,
    mut v_entries_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1947_ = crate::leanh::lean_unbox_usize(v_depth_1941_);
    crate::leanh::lean_dec(v_depth_1941_);
    v_res_1948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_1940_, v_depth_boxed_1947_, v_keys_1942_, v_vals_1943_, v_heq_1944_, v_i_1945_, v_entries_1946_);
    crate::leanh::lean_dec_ref(v_vals_1943_);
    crate::leanh::lean_dec_ref(v_keys_1942_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(
    mut v_00_u03b2_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
    mut v_x_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
    mut v_x_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1954_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
    return v___x_1954_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1965_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
    v___x_1966_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2;
    v___x_1967_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1968_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1964_,
        v___x_1965_,
        v___x_1966_,
        v___x_1967_,
    );
    return v___x_1968_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(
    mut v_a_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    return v_res_1970_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
    mut v___y_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_a_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_1976_,
                    v___y_1979_,
                    v___y_1980_,
                    v___y_1981_,
                    v___y_1982_,
                );
                if crate::leanh::lean_obj_tag(v___x_1984_) == 0 {
                    v_a_1985_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
                    crate::leanh::lean_inc_n(v_a_1985_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1984_, 1);
                    v___x_1986_ = l_Lean_Meta_liftLets(
                        v_a_1985_,
                        v_a_1974_,
                        v___y_1979_,
                        v___y_1980_,
                        v___y_1981_,
                        v___y_1982_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1986_) == 0 {
                        v_a_1987_ = crate::leanh::lean_ctor_get(v___x_1986_, 0);
                        crate::leanh::lean_inc(v_a_1987_);
                        crate::leanh::lean_dec_ref_known(v___x_1986_, 1);
                        v___x_1988_ = lean_expr_eqv(v_a_1985_, v_a_1987_);
                        crate::leanh::lean_dec(v_a_1985_);
                        if v___x_1988_ == 0 {
                            v___x_1989_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_1987_,
                                v___y_1975_,
                                v___y_1976_,
                                v___y_1977_,
                                v___y_1978_,
                                v___y_1979_,
                                v___y_1980_,
                                v___y_1981_,
                                v___y_1982_,
                            );
                            return v___x_1989_;
                        } else {
                            v___x_1990_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_1976_,
                                v___y_1979_,
                                v___y_1980_,
                                v___y_1981_,
                                v___y_1982_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                                v_a_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                                crate::leanh::lean_inc(v_a_1991_);
                                crate::leanh::lean_dec_ref_known(v___x_1990_, 1);
                                v___x_1992_ =
                                    l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1;
                                v___x_1993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_1994_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_1992_,
                                    v_a_1991_,
                                    v___x_1993_,
                                    v___y_1979_,
                                    v___y_1980_,
                                    v___y_1981_,
                                    v___y_1982_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1994_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1994_, 1);
                                    v___x_1995_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_1987_,
                                        v___y_1975_,
                                        v___y_1976_,
                                        v___y_1977_,
                                        v___y_1978_,
                                        v___y_1979_,
                                        v___y_1980_,
                                        v___y_1981_,
                                        v___y_1982_,
                                    );
                                    return v___x_1995_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1987_);
                                    return v___x_1994_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1987_);
                                v_a_1996_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                                v_isSharedCheck_2003_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                                if v_isSharedCheck_2003_ == 0 {
                                    v___x_1998_ = v___x_1990_;
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1996_);
                                    crate::leanh::lean_dec(v___x_1990_);
                                    v___x_1998_ = crate::leanh::lean_box(0);
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1985_);
                        v_a_2004_ = crate::leanh::lean_ctor_get(v___x_1986_, 0);
                        v_isSharedCheck_2011_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1986_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2006_ = v___x_1986_;
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2004_);
                            crate::leanh::lean_dec(v___x_1986_);
                            v___x_2006_ = crate::leanh::lean_box(0);
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1974_);
                    v_a_2012_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v___x_1984_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_1984_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2012_);
                        crate::leanh::lean_dec(v___x_1984_);
                        v___x_2014_ = crate::leanh::lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2001_;
            }
            3 => {
                if v_isShared_2007_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2009_;
            }
            5 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
    mut v___y_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(
        v_a_2020_,
        v___y_2021_,
        v___y_2022_,
        v___y_2023_,
        v___y_2024_,
        v___y_2025_,
        v___y_2026_,
        v___y_2027_,
        v___y_2028_,
    );
    crate::leanh::lean_dec(v___y_2028_);
    crate::leanh::lean_dec_ref(v___y_2027_);
    crate::leanh::lean_dec(v___y_2026_);
    crate::leanh::lean_dec_ref(v___y_2025_);
    crate::leanh::lean_dec(v___y_2024_);
    crate::leanh::lean_dec_ref(v___y_2023_);
    crate::leanh::lean_dec(v___y_2022_);
    crate::leanh::lean_dec_ref(v___y_2021_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets(
    mut v_x_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2048_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
                crate::leanh::lean_inc(v_x_2038_);
                v___x_2049_ = l_Lean_Syntax_isOfKind(v_x_2038_, v___x_2048_);
                if v___x_2049_ == 0 {
                    crate::leanh::lean_dec(v_x_2038_);
                    v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_2050_;
                } else {
                    v___x_2051_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2052_ = l_Lean_Syntax_getArg(v_x_2038_, v___x_2051_);
                    crate::leanh::lean_dec(v_x_2038_);
                    v___x_2053_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    crate::leanh::lean_inc(v___x_2052_);
                    v___x_2054_ = l_Lean_Syntax_isOfKind(v___x_2052_, v___x_2053_);
                    if v___x_2054_ == 0 {
                        crate::leanh::lean_dec(v___x_2052_);
                        v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_2055_;
                    } else {
                        v___x_2056_ = 0;
                        v___x_2057_ = crate::leanh::lean_alloc_ctor(0, 0, (11) as u32);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 0 as u32, v___x_2056_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 1 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 2 as u32, v___x_2056_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 3 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 4 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 5 as u32, v___x_2056_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 6 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 7 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 8 as u32, v___x_2056_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 9 as u32, v___x_2054_);
                        crate::leanh::lean_ctor_set_uint8(v___x_2057_, 10 as u32, v___x_2054_);
                        v___x_2058_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
                            v___x_2052_,
                            v___x_2057_,
                            v___x_2054_,
                            v_a_2039_,
                            v_a_2045_,
                            v_a_2046_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2058_) == 0 {
                            v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                            crate::leanh::lean_inc(v_a_2059_);
                            crate::leanh::lean_dec_ref_known(v___x_2058_, 1);
                            v___f_2060_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_2060_, 0, v_a_2059_);
                            v___x_2061_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                v___f_2060_,
                                v_a_2039_,
                                v_a_2040_,
                                v_a_2041_,
                                v_a_2042_,
                                v_a_2043_,
                                v_a_2044_,
                                v_a_2045_,
                                v_a_2046_,
                            );
                            return v___x_2061_;
                        } else {
                            v_a_2062_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                            v_isSharedCheck_2069_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2058_)) as u8;
                            if v_isSharedCheck_2069_ == 0 {
                                v___x_2064_ = v___x_2058_;
                                v_isShared_2065_ = v_isSharedCheck_2069_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2062_);
                                crate::leanh::lean_dec(v___x_2058_);
                                v___x_2064_ = crate::leanh::lean_box(0);
                                v_isShared_2065_ = v_isSharedCheck_2069_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2065_ == 0 {
                    v___x_2067_ = v___x_2064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
                    v___x_2067_ = v_reuseFailAlloc_2068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(
    mut v_x_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(
        v_x_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_,
        v_a_2078_,
    );
    crate::leanh::lean_dec(v_a_2078_);
    crate::leanh::lean_dec_ref(v_a_2077_);
    crate::leanh::lean_dec(v_a_2076_);
    crate::leanh::lean_dec_ref(v_a_2075_);
    crate::leanh::lean_dec(v_a_2074_);
    crate::leanh::lean_dec_ref(v_a_2073_);
    crate::leanh::lean_dec(v_a_2072_);
    crate::leanh::lean_dec_ref(v_a_2071_);
    return v_res_2080_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2090_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
    v___x_2091_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1;
    v___x_2092_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2093_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2089_,
        v___x_2090_,
        v___x_2091_,
        v___x_2092_,
    );
    return v___x_2093_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(
    mut v_a_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2095_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    return v_res_2095_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_a_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_a_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_2100_,
                    v___y_2103_,
                    v___y_2104_,
                    v___y_2105_,
                    v___y_2106_,
                );
                if crate::leanh::lean_obj_tag(v___x_2108_) == 0 {
                    v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2108_, 0);
                    crate::leanh::lean_inc_n(v_a_2109_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2108_, 1);
                    v___x_2110_ = l_Lean_Meta_letToHave(
                        v_a_2109_,
                        v___y_2103_,
                        v___y_2104_,
                        v___y_2105_,
                        v___y_2106_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2110_) == 0 {
                        v_a_2111_ = crate::leanh::lean_ctor_get(v___x_2110_, 0);
                        crate::leanh::lean_inc(v_a_2111_);
                        crate::leanh::lean_dec_ref_known(v___x_2110_, 1);
                        v___x_2112_ = lean_expr_eqv(v_a_2109_, v_a_2111_);
                        crate::leanh::lean_dec(v_a_2109_);
                        if v___x_2112_ == 0 {
                            v___x_2113_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_2111_,
                                v___y_2099_,
                                v___y_2100_,
                                v___y_2101_,
                                v___y_2102_,
                                v___y_2103_,
                                v___y_2104_,
                                v___y_2105_,
                                v___y_2106_,
                            );
                            return v___x_2113_;
                        } else {
                            v___x_2114_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_2100_,
                                v___y_2103_,
                                v___y_2104_,
                                v___y_2105_,
                                v___y_2106_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2114_) == 0 {
                                v_a_2115_ = crate::leanh::lean_ctor_get(v___x_2114_, 0);
                                crate::leanh::lean_inc(v_a_2115_);
                                crate::leanh::lean_dec_ref_known(v___x_2114_, 1);
                                v___x_2116_ =
                                    l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1;
                                v___x_2117_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_2118_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_2116_,
                                    v_a_2115_,
                                    v___x_2117_,
                                    v___y_2103_,
                                    v___y_2104_,
                                    v___y_2105_,
                                    v___y_2106_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2118_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2118_, 1);
                                    v___x_2119_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_2111_,
                                        v___y_2099_,
                                        v___y_2100_,
                                        v___y_2101_,
                                        v___y_2102_,
                                        v___y_2103_,
                                        v___y_2104_,
                                        v___y_2105_,
                                        v___y_2106_,
                                    );
                                    return v___x_2119_;
                                } else {
                                    crate::leanh::lean_dec(v_a_2111_);
                                    return v___x_2118_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2111_);
                                v_a_2120_ = crate::leanh::lean_ctor_get(v___x_2114_, 0);
                                v_isSharedCheck_2127_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2114_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2122_ = v___x_2114_;
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2120_);
                                    crate::leanh::lean_dec(v___x_2114_);
                                    v___x_2122_ = crate::leanh::lean_box(0);
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2109_);
                        v_a_2128_ = crate::leanh::lean_ctor_get(v___x_2110_, 0);
                        v_isSharedCheck_2135_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2110_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v___x_2130_ = v___x_2110_;
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2128_);
                            crate::leanh::lean_dec(v___x_2110_);
                            v___x_2130_ = crate::leanh::lean_box(0);
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2136_ = crate::leanh::lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2143_ = (!crate::leanh::lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2143_ == 0 {
                        v___x_2138_ = v___x_2108_;
                        v_isShared_2139_ = v_isSharedCheck_2143_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2136_);
                        crate::leanh::lean_dec(v___x_2108_);
                        v___x_2138_ = crate::leanh::lean_box(0);
                        v_isShared_2139_ = v_isSharedCheck_2143_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2123_ == 0 {
                    v___x_2125_ = v___x_2122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2125_;
            }
            3 => {
                if v_isShared_2131_ == 0 {
                    v___x_2133_ = v___x_2130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
                    v___x_2133_ = v_reuseFailAlloc_2134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2133_;
            }
            5 => {
                if v_isShared_2139_ == 0 {
                    v___x_2141_ = v___x_2138_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
                    v___x_2141_ = v_reuseFailAlloc_2142_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(
        v___y_2144_,
        v___y_2145_,
        v___y_2146_,
        v___y_2147_,
        v___y_2148_,
        v___y_2149_,
        v___y_2150_,
        v___y_2151_,
    );
    crate::leanh::lean_dec(v___y_2151_);
    crate::leanh::lean_dec_ref(v___y_2150_);
    crate::leanh::lean_dec(v___y_2149_);
    crate::leanh::lean_dec_ref(v___y_2148_);
    crate::leanh::lean_dec(v___y_2147_);
    crate::leanh::lean_dec_ref(v___y_2146_);
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave(
    mut v_x_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    v___x_2172_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2173_ = l_Lean_Syntax_isOfKind(v_x_2162_, v___x_2172_);
    if v___x_2173_ == 0 {
        let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
        return v___x_2174_;
    } else {
        let mut v___f_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_2175_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2;
        v___x_2176_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_2175_,
            v_a_2163_,
            v_a_2164_,
            v_a_2165_,
            v_a_2166_,
            v_a_2167_,
            v_a_2168_,
            v_a_2169_,
            v_a_2170_,
        );
        return v___x_2176_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(
    mut v_x_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
    mut v_a_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(
        v_x_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_,
        v_a_2185_,
    );
    crate::leanh::lean_dec(v_a_2185_);
    crate::leanh::lean_dec_ref(v_a_2184_);
    crate::leanh::lean_dec(v_a_2183_);
    crate::leanh::lean_dec_ref(v_a_2182_);
    crate::leanh::lean_dec(v_a_2181_);
    crate::leanh::lean_dec_ref(v_a_2180_);
    crate::leanh::lean_dec(v_a_2179_);
    crate::leanh::lean_dec_ref(v_a_2178_);
    return v_res_2187_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2197_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2198_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1;
    v___x_2199_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2196_,
        v___x_2197_,
        v___x_2198_,
        v___x_2199_,
    );
    return v___x_2200_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(
    mut v_a_2201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2202_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    return v_res_2202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Lets(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Lets(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Lets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
}
