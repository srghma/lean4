// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Lets
// Imports: Lean.Elab.Tactic.Lets Lean.Elab.Tactic.Conv.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uset, lean_expr_eqv, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        4644032510077903208 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value:
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
    m_data: [67, 111, 110, 118, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut leanh::LeanObject,
        2622230176999461939 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
            as *mut leanh::LeanObject,
        3123354491248406356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut leanh::LeanObject,4698081872094885029 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        7326091052943921366 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut leanh::LeanObject,
        2622230176999461939 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value)
                as *mut leanh::LeanObject,
            15211363250062378073 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 76, 105, 102, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut leanh::LeanObject,5567011710448919931 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        6130153969274943757 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
            as *mut leanh::LeanObject,
        2622230176999461939 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value)
            as *mut leanh::LeanObject,
        1576434579341158445 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 76, 101, 116, 84, 111, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut leanh::LeanObject,7421465252802819374 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = leanh::lean_box(0);
    v___x_1103_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1104_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    leanh::lean_ctor_set(v___x_1104_, 1, v___x_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
    v___x_1107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(
    mut v___y_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v_res_1109_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(
    mut v_00_u03b1_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
    mut v___y_1114_: *mut leanh::LeanObject,
    mut v___y_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v___x_1120_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(
    mut v_00_u03b1_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
    mut v___y_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1129_);
    leanh::lean_dec_ref(v___y_1128_);
    leanh::lean_dec(v___y_1127_);
    leanh::lean_dec_ref(v___y_1126_);
    leanh::lean_dec(v___y_1125_);
    leanh::lean_dec_ref(v___y_1124_);
    leanh::lean_dec(v___y_1123_);
    leanh::lean_dec_ref(v___y_1122_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
    mut v_mvarId_1132_: *mut leanh::LeanObject,
    mut v_x_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1132_,
                    v_x_1133_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                );
                if leanh::lean_obj_tag(v___x_1139_) == 0 {
                    v_a_1140_ = leanh::lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1142_ = v___x_1139_;
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1140_);
                        leanh::lean_dec(v___x_1139_);
                        v___x_1142_ = leanh::lean_box(0);
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1148_ = leanh::lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1155_ = (!leanh::lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1155_ == 0 {
                        v___x_1150_ = v___x_1139_;
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1148_);
                        leanh::lean_dec(v___x_1139_);
                        v___x_1150_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
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
                    v_reuseFailAlloc_1154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
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
    mut v_mvarId_1156_: *mut leanh::LeanObject,
    mut v_x_1157_: *mut leanh::LeanObject,
    mut v___y_1158_: *mut leanh::LeanObject,
    mut v___y_1159_: *mut leanh::LeanObject,
    mut v___y_1160_: *mut leanh::LeanObject,
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
            v_mvarId_1156_,
            v_x_1157_,
            v___y_1158_,
            v___y_1159_,
            v___y_1160_,
            v___y_1161_,
        );
    leanh::lean_dec(v___y_1161_);
    leanh::lean_dec_ref(v___y_1160_);
    leanh::lean_dec(v___y_1159_);
    leanh::lean_dec_ref(v___y_1158_);
    return v_res_1163_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
    mut v_00_u03b1_1164_: *mut leanh::LeanObject,
    mut v_mvarId_1165_: *mut leanh::LeanObject,
    mut v_x_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1173_: *mut leanh::LeanObject,
    mut v_mvarId_1174_: *mut leanh::LeanObject,
    mut v_x_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
        v_00_u03b1_1173_,
        v_mvarId_1174_,
        v_x_1175_,
        v___y_1176_,
        v___y_1177_,
        v___y_1178_,
        v___y_1179_,
    );
    leanh::lean_dec(v___y_1179_);
    leanh::lean_dec_ref(v___y_1178_);
    leanh::lean_dec(v___y_1177_);
    leanh::lean_dec_ref(v___y_1176_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(
    mut v_k_1182_: *mut leanh::LeanObject,
    mut v_b_1183_: *mut leanh::LeanObject,
    mut v_c_1184_: *mut leanh::LeanObject,
    mut v_d_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
    mut v___y_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1189_);
    leanh::lean_inc_ref(v___y_1188_);
    leanh::lean_inc(v___y_1187_);
    leanh::lean_inc_ref(v___y_1186_);
    v___x_1191_ = leanh::lean_apply_8(
        v_k_1182_,
        v_b_1183_,
        v_c_1184_,
        v_d_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        leanh::lean_box(0),
    );
    return v___x_1191_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(
    mut v_k_1192_: *mut leanh::LeanObject,
    mut v_b_1193_: *mut leanh::LeanObject,
    mut v_c_1194_: *mut leanh::LeanObject,
    mut v_d_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
    mut v___y_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_1192_, v_b_1193_, v_c_1194_, v_d_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
    leanh::lean_dec(v___y_1199_);
    leanh::lean_dec_ref(v___y_1198_);
    leanh::lean_dec(v___y_1197_);
    leanh::lean_dec_ref(v___y_1196_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
    mut v_es_1202_: *mut leanh::LeanObject,
    mut v_givenNames_1203_: *mut leanh::LeanObject,
    mut v_k_1204_: *mut leanh::LeanObject,
    mut v_config_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1216_: u8 = 0;
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut v_a_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1211_ = leanh::lean_alloc_closure(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                leanh::lean_closure_set(v___f_1211_, 0, v_k_1204_);
                v___x_1212_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(
                    leanh::lean_box(0),
                    v_es_1202_,
                    v_givenNames_1203_,
                    v___f_1211_,
                    v_config_1205_,
                    v___y_1206_,
                    v___y_1207_,
                    v___y_1208_,
                    v___y_1209_,
                );
                if leanh::lean_obj_tag(v___x_1212_) == 0 {
                    v_a_1213_ = leanh::lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1220_ = (!leanh::lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1220_ == 0 {
                        v___x_1215_ = v___x_1212_;
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1213_);
                        leanh::lean_dec(v___x_1212_);
                        v___x_1215_ = leanh::lean_box(0);
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1221_ = leanh::lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1228_ = (!leanh::lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1228_ == 0 {
                        v___x_1223_ = v___x_1212_;
                        v_isShared_1224_ = v_isSharedCheck_1228_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1221_);
                        leanh::lean_dec(v___x_1212_);
                        v___x_1223_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
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
                    v_reuseFailAlloc_1227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
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
    mut v_es_1229_: *mut leanh::LeanObject,
    mut v_givenNames_1230_: *mut leanh::LeanObject,
    mut v_k_1231_: *mut leanh::LeanObject,
    mut v_config_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1236_);
    leanh::lean_dec_ref(v___y_1235_);
    leanh::lean_dec(v___y_1234_);
    leanh::lean_dec_ref(v___y_1233_);
    leanh::lean_dec_ref(v_config_1232_);
    return v_res_1238_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(
    mut v_00_u03b1_1239_: *mut leanh::LeanObject,
    mut v_es_1240_: *mut leanh::LeanObject,
    mut v_givenNames_1241_: *mut leanh::LeanObject,
    mut v_k_1242_: *mut leanh::LeanObject,
    mut v_config_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1250_: *mut leanh::LeanObject,
    mut v_es_1251_: *mut leanh::LeanObject,
    mut v_givenNames_1252_: *mut leanh::LeanObject,
    mut v_k_1253_: *mut leanh::LeanObject,
    mut v_config_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1258_);
    leanh::lean_dec_ref(v___y_1257_);
    leanh::lean_dec(v___y_1256_);
    leanh::lean_dec_ref(v___y_1255_);
    leanh::lean_dec_ref(v_config_1254_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(
    mut v_x_1261_: *mut leanh::LeanObject,
    mut v_x_1262_: *mut leanh::LeanObject,
    mut v_x_1263_: *mut leanh::LeanObject,
    mut v_x_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1265_ = leanh::lean_ctor_get(v_x_1261_, 0);
                v_vs_1266_ = leanh::lean_ctor_get(v_x_1261_, 1);
                v_isSharedCheck_1290_ = (!leanh::lean_is_exclusive(v_x_1261_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1268_ = v_x_1261_;
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1266_);
                    leanh::lean_inc(v_ks_1265_);
                    leanh::lean_dec(v_x_1261_);
                    v___x_1268_ = leanh::lean_box(0);
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1270_ = lean_array_get_size(v_ks_1265_);
                v___x_1271_ = lean_nat_dec_lt(v_x_1262_, v___x_1270_);
                if v___x_1271_ == 0 {
                    leanh::lean_dec(v_x_1262_);
                    v___x_1272_ = lean_array_push(v_ks_1265_, v_x_1263_);
                    v___x_1273_ = lean_array_push(v_vs_1266_, v_x_1264_);
                    if v_isShared_1269_ == 0 {
                        leanh::lean_ctor_set(v___x_1268_, 1, v___x_1273_);
                        leanh::lean_ctor_set(v___x_1268_, 0, v___x_1272_);
                        v___x_1275_ = v___x_1268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1276_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ks_1265_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_vs_1266_);
                            v___x_1280_ = v_reuseFailAlloc_1284_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1285_ = lean_array_fset(v_ks_1265_, v_x_1262_, v_x_1263_);
                        v___x_1286_ = lean_array_fset(v_vs_1266_, v_x_1262_, v_x_1264_);
                        leanh::lean_dec(v_x_1262_);
                        if v_isShared_1269_ == 0 {
                            leanh::lean_ctor_set(v___x_1268_, 1, v___x_1286_);
                            leanh::lean_ctor_set(v___x_1268_, 0, v___x_1285_);
                            v___x_1288_ = v___x_1268_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1289_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1285_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
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
                v___x_1281_ = leanh::lean_unsigned_to_nat(1);
                v___x_1282_ = lean_nat_add(v_x_1262_, v___x_1281_);
                leanh::lean_dec(v_x_1262_);
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
    mut v_n_1291_: *mut leanh::LeanObject,
    mut v_k_1292_: *mut leanh::LeanObject,
    mut v_v_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_1300_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
    v___x_1301_ = lean_usize_sub(v___x_1300_, v___x_1299_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: usize,
    mut v_x_1305_: usize,
    mut v_x_1306_: *mut leanh::LeanObject,
    mut v_x_1307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: usize = 0;
    let mut v___x_1312_: usize = 0;
    let mut v_j_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v_v_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut v_node_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_unused_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1363_: u8 = 0;
    let mut v_ks_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v_reuseFailAlloc_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1303_) == 0 {
                    v_es_1308_ = leanh::lean_ctor_get(v_x_1303_, 0);
                    v___x_1309_ = 5usize;
                    v___x_1310_ = 1usize;
                    v___x_1311_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1);
                    v___x_1312_ = lean_usize_land(v_x_1304_, v___x_1311_);
                    v_j_1313_ = lean_usize_to_nat(v___x_1312_);
                    v___x_1314_ = lean_array_get_size(v_es_1308_);
                    v___x_1315_ = lean_nat_dec_lt(v_j_1313_, v___x_1314_);
                    if v___x_1315_ == 0 {
                        leanh::lean_dec(v_j_1313_);
                        leanh::lean_dec(v_x_1307_);
                        leanh::lean_dec(v_x_1306_);
                        return v_x_1303_;
                    } else {
                        leanh::lean_inc_ref(v_es_1308_);
                        v_isSharedCheck_1352_ = (!leanh::lean_is_exclusive(v_x_1303_)) as u8;
                        if v_isSharedCheck_1352_ == 0 {
                            v_unused_1353_ = leanh::lean_ctor_get(v_x_1303_, 0);
                            leanh::lean_dec(v_unused_1353_);
                            v___x_1317_ = v_x_1303_;
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1303_);
                            v___x_1317_ = leanh::lean_box(0);
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1354_ = leanh::lean_ctor_get(v_x_1303_, 0);
                    v_vs_1355_ = leanh::lean_ctor_get(v_x_1303_, 1);
                    v_isSharedCheck_1375_ = (!leanh::lean_is_exclusive(v_x_1303_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1357_ = v_x_1303_;
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1355_);
                        leanh::lean_inc(v_ks_1354_);
                        leanh::lean_dec(v_x_1303_);
                        v___x_1357_ = leanh::lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1319_ = lean_array_fget(v_es_1308_, v_j_1313_);
                v___x_1320_ = leanh::lean_box(0);
                v_xs_x27_1321_ = lean_array_fset(v_es_1308_, v_j_1313_, v___x_1320_);
                match leanh::lean_obj_tag(v_v_1319_) {
                    0 => {
                        v_key_1328_ = leanh::lean_ctor_get(v_v_1319_, 0);
                        v_val_1329_ = leanh::lean_ctor_get(v_v_1319_, 1);
                        v_isSharedCheck_1339_ = (!leanh::lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1339_ == 0 {
                            v___x_1331_ = v_v_1319_;
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1329_);
                            leanh::lean_inc(v_key_1328_);
                            leanh::lean_dec(v_v_1319_);
                            v___x_1331_ = leanh::lean_box(0);
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1340_ = leanh::lean_ctor_get(v_v_1319_, 0);
                        v_isSharedCheck_1350_ = (!leanh::lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1350_ == 0 {
                            v___x_1342_ = v_v_1319_;
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1340_);
                            leanh::lean_dec(v_v_1319_);
                            v___x_1342_ = leanh::lean_box(0);
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1351_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1351_, 0, v_x_1306_);
                        leanh::lean_ctor_set(v___x_1351_, 1, v_x_1307_);
                        v___y_1323_ = v___x_1351_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1324_ = lean_array_fset(v_xs_x27_1321_, v_j_1313_, v___y_1323_);
                leanh::lean_dec(v_j_1313_);
                if v_isShared_1318_ == 0 {
                    leanh::lean_ctor_set(v___x_1317_, 0, v___x_1324_);
                    v___x_1326_ = v___x_1317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
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
                    leanh::lean_del_object(v___x_1331_);
                    v___x_1334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1328_,
                        v_val_1329_,
                        v_x_1306_,
                        v_x_1307_,
                    );
                    v___x_1335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
                    v___y_1323_ = v___x_1335_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1329_);
                    leanh::lean_dec(v_key_1328_);
                    if v_isShared_1332_ == 0 {
                        leanh::lean_ctor_set(v___x_1331_, 1, v_x_1307_);
                        leanh::lean_ctor_set(v___x_1331_, 0, v_x_1306_);
                        v___x_1337_ = v___x_1331_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_x_1306_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_x_1307_);
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
                    leanh::lean_ctor_set(v___x_1342_, 0, v___x_1346_);
                    v___x_1348_ = v___x_1342_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
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
                    v_reuseFailAlloc_1374_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1355_);
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
                    v___x_1372_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1373_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
                    leanh::lean_dec(v___x_1371_);
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
                    v_ks_1364_ = leanh::lean_ctor_get(v_newNode_1361_, 0);
                    leanh::lean_inc_ref(v_ks_1364_);
                    v_vs_1365_ = leanh::lean_ctor_get(v_newNode_1361_, 1);
                    leanh::lean_inc_ref(v_vs_1365_);
                    leanh::lean_dec_ref(v_newNode_1361_);
                    v___x_1366_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1367_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2);
                    v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_1305_, v_ks_1364_, v_vs_1365_, v___x_1366_, v___x_1367_);
                    leanh::lean_dec_ref(v_vs_1365_);
                    leanh::lean_dec_ref(v_ks_1364_);
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
    mut v_keys_1377_: *mut leanh::LeanObject,
    mut v_vals_1378_: *mut leanh::LeanObject,
    mut v_i_1379_: *mut leanh::LeanObject,
    mut v_entries_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v_k_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u64 = 0;
    let mut v_h_1386_: usize = 0;
    let mut v___x_1387_: usize = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v_h_1392_: usize = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1381_ = lean_array_get_size(v_keys_1377_);
                v___x_1382_ = lean_nat_dec_lt(v_i_1379_, v___x_1381_);
                if v___x_1382_ == 0 {
                    leanh::lean_dec(v_i_1379_);
                    return v_entries_1380_;
                } else {
                    v_k_1383_ = lean_array_fget_borrowed(v_keys_1377_, v_i_1379_);
                    v_v_1384_ = lean_array_fget_borrowed(v_vals_1378_, v_i_1379_);
                    v___x_1385_ = l_Lean_instHashableMVarId_hash(v_k_1383_);
                    v_h_1386_ = lean_uint64_to_usize(v___x_1385_);
                    v___x_1387_ = 5usize;
                    v___x_1388_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1389_ = 1usize;
                    v___x_1390_ = lean_usize_sub(v_depth_1376_, v___x_1389_);
                    v___x_1391_ = lean_usize_mul(v___x_1387_, v___x_1390_);
                    v_h_1392_ = lean_usize_shift_right(v_h_1386_, v___x_1391_);
                    v___x_1393_ = lean_nat_add(v_i_1379_, v___x_1388_);
                    leanh::lean_dec(v_i_1379_);
                    leanh::lean_inc(v_v_1384_);
                    leanh::lean_inc(v_k_1383_);
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
    mut v_depth_1396_: *mut leanh::LeanObject,
    mut v_keys_1397_: *mut leanh::LeanObject,
    mut v_vals_1398_: *mut leanh::LeanObject,
    mut v_i_1399_: *mut leanh::LeanObject,
    mut v_entries_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1401_: usize = 0;
    let mut v_res_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1401_ = leanh::lean_unbox_usize(v_depth_1396_);
    leanh::lean_dec(v_depth_1396_);
    v_res_1402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_1401_, v_keys_1397_, v_vals_1398_, v_i_1399_, v_entries_1400_);
    leanh::lean_dec_ref(v_vals_1398_);
    leanh::lean_dec_ref(v_keys_1397_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(
    mut v_x_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
    mut v_x_1405_: *mut leanh::LeanObject,
    mut v_x_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6152__boxed_1408_: usize = 0;
    let mut v_x_6153__boxed_1409_: usize = 0;
    let mut v_res_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6152__boxed_1408_ = leanh::lean_unbox_usize(v_x_1404_);
    leanh::lean_dec(v_x_1404_);
    v_x_6153__boxed_1409_ = leanh::lean_unbox_usize(v_x_1405_);
    leanh::lean_dec(v_x_1405_);
    v_res_1410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1403_, v_x_6152__boxed_1408_, v_x_6153__boxed_1409_, v_x_1406_, v_x_1407_);
    return v_res_1410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(
    mut v_x_1411_: *mut leanh::LeanObject,
    mut v_x_1412_: *mut leanh::LeanObject,
    mut v_x_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1414_: u64 = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Lean_instHashableMVarId_hash(v_x_1412_);
    v___x_1415_ = lean_uint64_to_usize(v___x_1414_);
    v___x_1416_ = 1usize;
    v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1411_, v___x_1415_, v___x_1416_, v_x_1412_, v_x_1413_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
    mut v_mvarId_1418_: *mut leanh::LeanObject,
    mut v_val_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_depth_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1422_ = lean_st_ref_take(v___y_1420_);
                v_mctx_1423_ = leanh::lean_ctor_get(v___x_1422_, 0);
                v_cache_1424_ = leanh::lean_ctor_get(v___x_1422_, 1);
                v_zetaDeltaFVarIds_1425_ = leanh::lean_ctor_get(v___x_1422_, 2);
                v_postponed_1426_ = leanh::lean_ctor_get(v___x_1422_, 3);
                v_diag_1427_ = leanh::lean_ctor_get(v___x_1422_, 4);
                v_isSharedCheck_1455_ = (!leanh::lean_is_exclusive(v___x_1422_)) as u8;
                if v_isSharedCheck_1455_ == 0 {
                    v___x_1429_ = v___x_1422_;
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1427_);
                    leanh::lean_inc(v_postponed_1426_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1425_);
                    leanh::lean_inc(v_cache_1424_);
                    leanh::lean_inc(v_mctx_1423_);
                    leanh::lean_dec(v___x_1422_);
                    v___x_1429_ = leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1431_ = leanh::lean_ctor_get(v_mctx_1423_, 0);
                v_levelAssignDepth_1432_ = leanh::lean_ctor_get(v_mctx_1423_, 1);
                v_lmvarCounter_1433_ = leanh::lean_ctor_get(v_mctx_1423_, 2);
                v_mvarCounter_1434_ = leanh::lean_ctor_get(v_mctx_1423_, 3);
                v_lDecls_1435_ = leanh::lean_ctor_get(v_mctx_1423_, 4);
                v_decls_1436_ = leanh::lean_ctor_get(v_mctx_1423_, 5);
                v_userNames_1437_ = leanh::lean_ctor_get(v_mctx_1423_, 6);
                v_lAssignment_1438_ = leanh::lean_ctor_get(v_mctx_1423_, 7);
                v_eAssignment_1439_ = leanh::lean_ctor_get(v_mctx_1423_, 8);
                v_dAssignment_1440_ = leanh::lean_ctor_get(v_mctx_1423_, 9);
                v_isSharedCheck_1454_ = (!leanh::lean_is_exclusive(v_mctx_1423_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v___x_1442_ = v_mctx_1423_;
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1440_);
                    leanh::lean_inc(v_eAssignment_1439_);
                    leanh::lean_inc(v_lAssignment_1438_);
                    leanh::lean_inc(v_userNames_1437_);
                    leanh::lean_inc(v_decls_1436_);
                    leanh::lean_inc(v_lDecls_1435_);
                    leanh::lean_inc(v_mvarCounter_1434_);
                    leanh::lean_inc(v_lmvarCounter_1433_);
                    leanh::lean_inc(v_levelAssignDepth_1432_);
                    leanh::lean_inc(v_depth_1431_);
                    leanh::lean_dec(v_mctx_1423_);
                    v___x_1442_ = leanh::lean_box(0);
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_1439_, v_mvarId_1418_, v_val_1419_);
                if v_isShared_1443_ == 0 {
                    leanh::lean_ctor_set(v___x_1442_, 8, v___x_1444_);
                    v___x_1446_ = v___x_1442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_depth_1431_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1453_,
                        1,
                        v_levelAssignDepth_1432_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_lmvarCounter_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_mvarCounter_1434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_lDecls_1435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 5, v_decls_1436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 6, v_userNames_1437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 7, v_lAssignment_1438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 8, v___x_1444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 9, v_dAssignment_1440_);
                    v___x_1446_ = v_reuseFailAlloc_1453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1446_);
                    v___x_1448_ = v___x_1429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_cache_1424_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1452_,
                        2,
                        v_zetaDeltaFVarIds_1425_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_postponed_1426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_diag_1427_);
                    v___x_1448_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1449_ = lean_st_ref_set(v___y_1420_, v___x_1448_);
                v___x_1450_ = leanh::lean_box(0);
                v___x_1451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(
    mut v_mvarId_1456_: *mut leanh::LeanObject,
    mut v_val_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1456_,
            v_val_1457_,
            v___y_1458_,
        );
    leanh::lean_dec(v___y_1458_);
    return v_res_1460_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0;
    v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1,
    );
    v___x_1465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1465_, 0, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(
    mut v___x_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v___x_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_mvar_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_1467_);
                v___x_1476_ = l_Lean_Meta_isExprDefEq(
                    v___x_1466_,
                    v_a_1467_,
                    v___y_1471_,
                    v___y_1472_,
                    v___y_1473_,
                    v___y_1474_,
                );
                if leanh::lean_obj_tag(v___x_1476_) == 0 {
                    v_a_1477_ = leanh::lean_ctor_get(v___x_1476_, 0);
                    leanh::lean_inc(v_a_1477_);
                    leanh::lean_dec_ref_known(v___x_1476_, 1);
                    v___x_1478_ = (leanh::lean_unbox(v_a_1477_) as u8);
                    leanh::lean_dec(v_a_1477_);
                    if v___x_1478_ == 0 {
                        v___x_1479_ = leanh::lean_obj_once(
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
                        if leanh::lean_obj_tag(v___x_1480_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1480_, 1);
                            v___x_1481_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                            return v___x_1481_;
                        } else {
                            leanh::lean_dec(v_mvar_1470_);
                            leanh::lean_dec_ref(v_a_1467_);
                            return v___x_1480_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1469_);
                        leanh::lean_dec(v___x_1468_);
                        v___x_1482_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                        return v___x_1482_;
                    }
                } else {
                    leanh::lean_dec(v_mvar_1470_);
                    leanh::lean_dec(v_a_1469_);
                    leanh::lean_dec(v___x_1468_);
                    leanh::lean_dec_ref(v_a_1467_);
                    v_a_1483_ = leanh::lean_ctor_get(v___x_1476_, 0);
                    v_isSharedCheck_1490_ = (!leanh::lean_is_exclusive(v___x_1476_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1485_ = v___x_1476_;
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1483_);
                        leanh::lean_dec(v___x_1476_);
                        v___x_1485_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
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
    mut v___x_1491_: *mut leanh::LeanObject,
    mut v_a_1492_: *mut leanh::LeanObject,
    mut v___x_1493_: *mut leanh::LeanObject,
    mut v_a_1494_: *mut leanh::LeanObject,
    mut v_mvar_1495_: *mut leanh::LeanObject,
    mut v___y_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1499_);
    leanh::lean_dec_ref(v___y_1498_);
    leanh::lean_dec(v___y_1497_);
    leanh::lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
    mut v___x_1502_: *mut leanh::LeanObject,
    mut v___x_1503_: u8,
    mut v___x_1504_: u8,
    mut v___x_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
    mut v_mvar_1507_: *mut leanh::LeanObject,
    mut v_e_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
    mut v___y_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1515_) == 0 {
                    v_a_1516_ = leanh::lean_ctor_get(v___x_1515_, 0);
                    leanh::lean_inc(v_a_1516_);
                    leanh::lean_dec_ref_known(v___x_1515_, 1);
                    leanh::lean_inc_n(v_mvar_1507_, 2);
                    v___x_1517_ = l_Lean_Expr_mvar___override(v_mvar_1507_);
                    v___f_1518_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    leanh::lean_closure_set(v___f_1518_, 0, v___x_1517_);
                    leanh::lean_closure_set(v___f_1518_, 1, v_a_1516_);
                    leanh::lean_closure_set(v___f_1518_, 2, v___x_1505_);
                    leanh::lean_closure_set(v___f_1518_, 3, v_a_1506_);
                    leanh::lean_closure_set(v___f_1518_, 4, v_mvar_1507_);
                    v___x_1519_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_1507_, v___f_1518_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
                    return v___x_1519_;
                } else {
                    leanh::lean_dec(v_mvar_1507_);
                    leanh::lean_dec(v_a_1506_);
                    leanh::lean_dec(v___x_1505_);
                    v_a_1520_ = leanh::lean_ctor_get(v___x_1515_, 0);
                    v_isSharedCheck_1527_ = (!leanh::lean_is_exclusive(v___x_1515_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1522_ = v___x_1515_;
                        v_isShared_1523_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1520_);
                        leanh::lean_dec(v___x_1515_);
                        v___x_1522_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1526_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
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
    mut v___x_1528_: *mut leanh::LeanObject,
    mut v___x_1529_: *mut leanh::LeanObject,
    mut v___x_1530_: *mut leanh::LeanObject,
    mut v___x_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_mvar_1533_: *mut leanh::LeanObject,
    mut v_e_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6446__boxed_1540_: u8 = 0;
    let mut v___x_6447__boxed_1541_: u8 = 0;
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6446__boxed_1540_ = (leanh::lean_unbox(v___x_1529_) as u8);
    v___x_6447__boxed_1541_ = (leanh::lean_unbox(v___x_1530_) as u8);
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
    leanh::lean_dec(v___y_1538_);
    leanh::lean_dec_ref(v___y_1537_);
    leanh::lean_dec(v___y_1536_);
    leanh::lean_dec_ref(v___y_1535_);
    leanh::lean_dec_ref(v___x_1528_);
    return v_res_1542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(
    mut v_sz_1543_: usize,
    mut v_i_1544_: usize,
    mut v_bs_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: u8 = 0;
    let mut v_v_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
                if v___x_1546_ == 0 {
                    return v_bs_1545_;
                } else {
                    v_v_1547_ = lean_array_uget(v_bs_1545_, v_i_1544_);
                    v___x_1548_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1555_: *mut leanh::LeanObject,
    mut v_i_1556_: *mut leanh::LeanObject,
    mut v_bs_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1558_: usize = 0;
    let mut v_i_boxed_1559_: usize = 0;
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1558_ = leanh::lean_unbox_usize(v_sz_1555_);
    leanh::lean_dec(v_sz_1555_);
    v_i_boxed_1559_ = leanh::lean_unbox_usize(v_i_1556_);
    leanh::lean_dec(v_i_1556_);
    v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_1558_, v_i_boxed_1559_, v_bs_1557_);
    return v_res_1560_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0;
    v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1,
    );
    v___x_1565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(
    mut v___x_1566_: *mut leanh::LeanObject,
    mut v_a_1567_: *mut leanh::LeanObject,
    mut v___x_1568_: usize,
    mut v___x_1569_: u8,
    mut v___x_1570_: u8,
    mut v___x_1571_: *mut leanh::LeanObject,
    mut v_snd_1572_: *mut leanh::LeanObject,
    mut v_fst_1573_: *mut leanh::LeanObject,
    mut v_fvarIds_1574_: *mut leanh::LeanObject,
    mut v_es_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
    mut v___y_1578_: *mut leanh::LeanObject,
    mut v___y_1579_: *mut leanh::LeanObject,
    mut v___y_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v_sz_1594_: usize = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1611_: u8 = 0;
    let mut v_unused_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v_a_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                        v___x_1649_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2,
                        );
                        leanh::lean_inc(v_a_1567_);
                        leanh::lean_inc(v___x_1571_);
                        v___x_1650_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_1571_,
                            v_a_1567_,
                            v___x_1649_,
                            v___y_1577_,
                            v___y_1578_,
                            v___y_1579_,
                            v___y_1580_,
                        );
                        if leanh::lean_obj_tag(v___x_1650_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1650_, 1);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_fvarIds_1574_);
                            leanh::lean_dec_ref(v_snd_1572_);
                            leanh::lean_dec(v___x_1571_);
                            leanh::lean_dec(v_a_1567_);
                            v_a_1651_ = leanh::lean_ctor_get(v___x_1650_, 0);
                            v_isSharedCheck_1658_ =
                                (!leanh::lean_is_exclusive(v___x_1650_)) as u8;
                            if v_isSharedCheck_1658_ == 0 {
                                v___x_1653_ = v___x_1650_;
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1651_);
                                leanh::lean_dec(v___x_1650_);
                                v___x_1653_ = leanh::lean_box(0);
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1567_);
                v___x_1585_ = l_Lean_MVarId_getTag(
                    v_a_1567_,
                    v___y_1577_,
                    v___y_1578_,
                    v___y_1579_,
                    v___y_1580_,
                );
                if leanh::lean_obj_tag(v___x_1585_) == 0 {
                    v_a_1586_ = leanh::lean_ctor_get(v___x_1585_, 0);
                    leanh::lean_inc(v_a_1586_);
                    leanh::lean_dec_ref_known(v___x_1585_, 1);
                    leanh::lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                        v___x_1583_,
                        v_a_1586_,
                        v___y_1577_,
                        v___y_1578_,
                        v___y_1579_,
                        v___y_1580_,
                    );
                    if leanh::lean_obj_tag(v___x_1587_) == 0 {
                        v_a_1588_ = leanh::lean_ctor_get(v___x_1587_, 0);
                        leanh::lean_inc(v_a_1588_);
                        leanh::lean_dec_ref_known(v___x_1587_, 1);
                        v_fst_1589_ = leanh::lean_ctor_get(v_a_1588_, 0);
                        v_snd_1590_ = leanh::lean_ctor_get(v_a_1588_, 1);
                        v_isSharedCheck_1629_ = (!leanh::lean_is_exclusive(v_a_1588_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1592_ = v_a_1588_;
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1590_);
                            leanh::lean_inc(v_fst_1589_);
                            leanh::lean_dec(v_a_1588_);
                            v___x_1592_ = leanh::lean_box(0);
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_fvarIds_1574_);
                        leanh::lean_dec_ref(v_snd_1572_);
                        leanh::lean_dec(v___x_1571_);
                        leanh::lean_dec(v_a_1567_);
                        v_a_1630_ = leanh::lean_ctor_get(v___x_1587_, 0);
                        v_isSharedCheck_1637_ =
                            (!leanh::lean_is_exclusive(v___x_1587_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1587_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1630_);
                            leanh::lean_dec(v___x_1587_);
                            v___x_1632_ = leanh::lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fvarIds_1574_);
                    leanh::lean_dec_ref(v_snd_1572_);
                    leanh::lean_dec(v___x_1571_);
                    leanh::lean_dec(v_a_1567_);
                    v_a_1638_ = leanh::lean_ctor_get(v___x_1585_, 0);
                    v_isSharedCheck_1645_ = (!leanh::lean_is_exclusive(v___x_1585_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1640_ = v___x_1585_;
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1638_);
                        leanh::lean_dec(v___x_1585_);
                        v___x_1640_ = leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_sz_1594_ = lean_array_size(v_fvarIds_1574_);
                leanh::lean_inc_ref(v_fvarIds_1574_);
                v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_1594_, v___x_1568_, v_fvarIds_1574_);
                v___x_1596_ = l_Lean_Expr_mvarId_x21(v_fst_1589_);
                leanh::lean_dec(v_fst_1589_);
                leanh::lean_inc(v_a_1567_);
                leanh::lean_inc(v___x_1571_);
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
                if leanh::lean_obj_tag(v___x_1597_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1597_, 1);
                    leanh::lean_inc(v_snd_1590_);
                    leanh::lean_inc(v_a_1567_);
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
                    leanh::lean_dec_ref(v___x_1595_);
                    if leanh::lean_obj_tag(v___x_1598_) == 0 {
                        v_isSharedCheck_1611_ =
                            (!leanh::lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1611_ == 0 {
                            v_unused_1612_ = leanh::lean_ctor_get(v___x_1598_, 0);
                            leanh::lean_dec(v_unused_1612_);
                            v___x_1600_ = v___x_1598_;
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1598_);
                            v___x_1600_ = leanh::lean_box(0);
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1592_);
                        leanh::lean_dec(v_snd_1590_);
                        leanh::lean_dec_ref(v_fvarIds_1574_);
                        v_a_1613_ = leanh::lean_ctor_get(v___x_1598_, 0);
                        v_isSharedCheck_1620_ =
                            (!leanh::lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1620_ == 0 {
                            v___x_1615_ = v___x_1598_;
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1613_);
                            leanh::lean_dec(v___x_1598_);
                            v___x_1615_ = leanh::lean_box(0);
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1595_);
                    leanh::lean_del_object(v___x_1592_);
                    leanh::lean_dec(v_snd_1590_);
                    leanh::lean_dec_ref(v_fvarIds_1574_);
                    leanh::lean_dec(v___x_1571_);
                    leanh::lean_dec(v_a_1567_);
                    v_a_1621_ = leanh::lean_ctor_get(v___x_1597_, 0);
                    v_isSharedCheck_1628_ = (!leanh::lean_is_exclusive(v___x_1597_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1597_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1621_);
                        leanh::lean_dec(v___x_1597_);
                        v___x_1623_ = leanh::lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1602_ = l_Lean_Expr_mvarId_x21(v_snd_1590_);
                leanh::lean_dec(v_snd_1590_);
                v___x_1603_ = leanh::lean_box(0);
                v___x_1604_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                leanh::lean_ctor_set(v___x_1604_, 1, v___x_1603_);
                if v_isShared_1593_ == 0 {
                    leanh::lean_ctor_set(v___x_1592_, 1, v___x_1604_);
                    leanh::lean_ctor_set(v___x_1592_, 0, v_fvarIds_1574_);
                    v___x_1606_ = v___x_1592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fvarIds_1574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1604_);
                    v___x_1606_ = v_reuseFailAlloc_1610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1601_ == 0 {
                    leanh::lean_ctor_set(v___x_1600_, 0, v___x_1606_);
                    v___x_1608_ = v___x_1600_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
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
                    v_reuseFailAlloc_1619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
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
                    v_reuseFailAlloc_1627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
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
                    v_reuseFailAlloc_1636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
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
                    v_reuseFailAlloc_1644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
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
                    v_reuseFailAlloc_1657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
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
    mut v___x_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v___x_1661_: *mut leanh::LeanObject,
    mut v___x_1662_: *mut leanh::LeanObject,
    mut v___x_1663_: *mut leanh::LeanObject,
    mut v___x_1664_: *mut leanh::LeanObject,
    mut v_snd_1665_: *mut leanh::LeanObject,
    mut v_fst_1666_: *mut leanh::LeanObject,
    mut v_fvarIds_1667_: *mut leanh::LeanObject,
    mut v_es_1668_: *mut leanh::LeanObject,
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6529__boxed_1675_: usize = 0;
    let mut v___x_6530__boxed_1676_: u8 = 0;
    let mut v___x_6531__boxed_1677_: u8 = 0;
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6529__boxed_1675_ = leanh::lean_unbox_usize(v___x_1661_);
    leanh::lean_dec(v___x_1661_);
    v___x_6530__boxed_1676_ = (leanh::lean_unbox(v___x_1662_) as u8);
    v___x_6531__boxed_1677_ = (leanh::lean_unbox(v___x_1663_) as u8);
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
    leanh::lean_dec(v___y_1673_);
    leanh::lean_dec_ref(v___y_1672_);
    leanh::lean_dec(v___y_1671_);
    leanh::lean_dec_ref(v___y_1670_);
    leanh::lean_dec(v_x_1669_);
    leanh::lean_dec_ref(v_es_1668_);
    leanh::lean_dec_ref(v_fst_1666_);
    leanh::lean_dec(v___x_1659_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(
    mut v___x_1682_: *mut leanh::LeanObject,
    mut v___x_1683_: usize,
    mut v___x_1684_: u8,
    mut v___x_1685_: u8,
    mut v_snd_1686_: *mut leanh::LeanObject,
    mut v_fst_1687_: *mut leanh::LeanObject,
    mut v___x_1688_: *mut leanh::LeanObject,
    mut v___x_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_unused_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut v_a_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_a_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1700_) == 0 {
                    v_a_1701_ = leanh::lean_ctor_get(v___x_1700_, 0);
                    leanh::lean_inc_n(v_a_1701_, 2);
                    leanh::lean_dec_ref_known(v___x_1700_, 1);
                    v___x_1702_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1;
                    v___x_1703_ = l_Lean_MVarId_checkNotAssigned(
                        v_a_1701_,
                        v___x_1702_,
                        v___y_1695_,
                        v___y_1696_,
                        v___y_1697_,
                        v___y_1698_,
                    );
                    if leanh::lean_obj_tag(v___x_1703_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1703_, 1);
                        v___x_1704_ = leanh::lean_box_usize(v___x_1683_);
                        v___x_1705_ = leanh::lean_box((v___x_1684_) as usize);
                        v___x_1706_ = leanh::lean_box((v___x_1685_) as usize);
                        leanh::lean_inc_ref(v_fst_1687_);
                        v___f_1707_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            8,
                        );
                        leanh::lean_closure_set(v___f_1707_, 0, v___x_1682_);
                        leanh::lean_closure_set(v___f_1707_, 1, v_a_1701_);
                        leanh::lean_closure_set(v___f_1707_, 2, v___x_1704_);
                        leanh::lean_closure_set(v___f_1707_, 3, v___x_1705_);
                        leanh::lean_closure_set(v___f_1707_, 4, v___x_1706_);
                        leanh::lean_closure_set(v___f_1707_, 5, v___x_1702_);
                        leanh::lean_closure_set(v___f_1707_, 6, v_snd_1686_);
                        leanh::lean_closure_set(v___f_1707_, 7, v_fst_1687_);
                        v___x_1708_ = lean_mk_empty_array_with_capacity(v___x_1688_);
                        v___x_1709_ = lean_array_push(v___x_1708_, v_fst_1687_);
                        v___x_1710_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_1709_, v___x_1689_, v___f_1707_, v_a_1690_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
                        if leanh::lean_obj_tag(v___x_1710_) == 0 {
                            v_a_1711_ = leanh::lean_ctor_get(v___x_1710_, 0);
                            leanh::lean_inc(v_a_1711_);
                            leanh::lean_dec_ref_known(v___x_1710_, 1);
                            v_fst_1712_ = leanh::lean_ctor_get(v_a_1711_, 0);
                            leanh::lean_inc(v_fst_1712_);
                            v_snd_1713_ = leanh::lean_ctor_get(v_a_1711_, 1);
                            leanh::lean_inc(v_snd_1713_);
                            leanh::lean_dec(v_a_1711_);
                            v___x_1714_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v_snd_1713_,
                                v___y_1692_,
                                v___y_1695_,
                                v___y_1696_,
                                v___y_1697_,
                                v___y_1698_,
                            );
                            if leanh::lean_obj_tag(v___x_1714_) == 0 {
                                v_isSharedCheck_1721_ =
                                    (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1721_ == 0 {
                                    v_unused_1722_ = leanh::lean_ctor_get(v___x_1714_, 0);
                                    leanh::lean_dec(v_unused_1722_);
                                    v___x_1716_ = v___x_1714_;
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1714_);
                                    v___x_1716_ = leanh::lean_box(0);
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_fst_1712_);
                                v_a_1723_ = leanh::lean_ctor_get(v___x_1714_, 0);
                                v_isSharedCheck_1730_ =
                                    (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1730_ == 0 {
                                    v___x_1725_ = v___x_1714_;
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1723_);
                                    leanh::lean_dec(v___x_1714_);
                                    v___x_1725_ = leanh::lean_box(0);
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1731_ = leanh::lean_ctor_get(v___x_1710_, 0);
                            v_isSharedCheck_1738_ =
                                (!leanh::lean_is_exclusive(v___x_1710_)) as u8;
                            if v_isSharedCheck_1738_ == 0 {
                                v___x_1733_ = v___x_1710_;
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1731_);
                                leanh::lean_dec(v___x_1710_);
                                v___x_1733_ = leanh::lean_box(0);
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1701_);
                        leanh::lean_dec(v___x_1689_);
                        leanh::lean_dec_ref(v_fst_1687_);
                        leanh::lean_dec_ref(v_snd_1686_);
                        leanh::lean_dec(v___x_1682_);
                        v_a_1739_ = leanh::lean_ctor_get(v___x_1703_, 0);
                        v_isSharedCheck_1746_ =
                            (!leanh::lean_is_exclusive(v___x_1703_)) as u8;
                        if v_isSharedCheck_1746_ == 0 {
                            v___x_1741_ = v___x_1703_;
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1739_);
                            leanh::lean_dec(v___x_1703_);
                            v___x_1741_ = leanh::lean_box(0);
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1689_);
                    leanh::lean_dec_ref(v_fst_1687_);
                    leanh::lean_dec_ref(v_snd_1686_);
                    leanh::lean_dec(v___x_1682_);
                    v_a_1747_ = leanh::lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1754_ = (!leanh::lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v___x_1749_ = v___x_1700_;
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1747_);
                        leanh::lean_dec(v___x_1700_);
                        v___x_1749_ = leanh::lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1717_ == 0 {
                    leanh::lean_ctor_set(v___x_1716_, 0, v_fst_1712_);
                    v___x_1719_ = v___x_1716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1712_);
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
                    v_reuseFailAlloc_1729_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
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
                    v_reuseFailAlloc_1737_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
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
                    v_reuseFailAlloc_1745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
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
                    v_reuseFailAlloc_1753_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_1756_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_1757_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_1758_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_snd_1759_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_fst_1760_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_1761_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_1762_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_1763_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_1764_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_1765_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_1766_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_1767_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_1768_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_1769_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_1770_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_1771_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_1772_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_6736__boxed_1773_: usize = 0;
    let mut v___x_6737__boxed_1774_: u8 = 0;
    let mut v___x_6738__boxed_1775_: u8 = 0;
    let mut v_res_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6736__boxed_1773_ = leanh::lean_unbox_usize(v___x_1756_);
    leanh::lean_dec(v___x_1756_);
    v___x_6737__boxed_1774_ = (leanh::lean_unbox(v___x_1757_) as u8);
    v___x_6738__boxed_1775_ = (leanh::lean_unbox(v___x_1758_) as u8);
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
    leanh::lean_dec(v___y_1771_);
    leanh::lean_dec_ref(v___y_1770_);
    leanh::lean_dec(v___y_1769_);
    leanh::lean_dec_ref(v___y_1768_);
    leanh::lean_dec(v___y_1767_);
    leanh::lean_dec_ref(v___y_1766_);
    leanh::lean_dec(v___y_1765_);
    leanh::lean_dec_ref(v___y_1764_);
    leanh::lean_dec_ref(v_a_1763_);
    leanh::lean_dec(v___x_1761_);
    return v_res_1776_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(
    mut v_sz_1777_: usize,
    mut v_i_1778_: usize,
    mut v_bs_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1780_: u8 = 0;
    let mut v_v_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1780_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
                if v___x_1780_ == 0 {
                    return v_bs_1779_;
                } else {
                    v_v_1781_ = lean_array_uget(v_bs_1779_, v_i_1778_);
                    v___x_1782_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1783_ = lean_array_uset(v_bs_1779_, v_i_1778_, v___x_1782_);
                    v___x_1784_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_1781_);
                    leanh::lean_dec(v_v_1781_);
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
    mut v_sz_1789_: *mut leanh::LeanObject,
    mut v_i_1790_: *mut leanh::LeanObject,
    mut v_bs_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1792_: usize = 0;
    let mut v_i_boxed_1793_: usize = 0;
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1792_ = leanh::lean_unbox_usize(v_sz_1789_);
    leanh::lean_dec(v_sz_1789_);
    v_i_boxed_1793_ = leanh::lean_unbox_usize(v_i_1790_);
    leanh::lean_dec(v_i_1790_);
    v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_1792_, v_i_boxed_1793_, v_bs_1791_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets(
    mut v_x_1814_: *mut leanh::LeanObject,
    mut v_a_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
    mut v_a_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1843_: usize = 0;
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: usize = 0;
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
                leanh::lean_inc(v_x_1814_);
                v___x_1825_ = l_Lean_Syntax_isOfKind(v_x_1814_, v___x_1824_);
                if v___x_1825_ == 0 {
                    leanh::lean_dec(v_x_1814_);
                    v___x_1826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_1826_;
                } else {
                    v___x_1827_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1828_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1827_);
                    v___x_1829_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    leanh::lean_inc(v___x_1828_);
                    v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1828_, v___x_1829_);
                    if v___x_1830_ == 0 {
                        leanh::lean_dec(v___x_1828_);
                        leanh::lean_dec(v_x_1814_);
                        v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_1831_;
                    } else {
                        v___x_1832_ = 0;
                        v___x_1833_ = leanh::lean_alloc_ctor(0, 0, (11) as u32);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 0 as u32, v___x_1832_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 1 as u32, v___x_1830_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 2 as u32, v___x_1832_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 3 as u32, v___x_1830_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 4 as u32, v___x_1830_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 5 as u32, v___x_1832_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 6 as u32, v___x_1830_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 7 as u32, v___x_1830_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 8 as u32, v___x_1832_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 9 as u32, v___x_1832_);
                        leanh::lean_ctor_set_uint8(v___x_1833_, 10 as u32, v___x_1832_);
                        v___x_1834_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
                            v___x_1828_,
                            v___x_1833_,
                            v___x_1830_,
                            v_a_1815_,
                            v_a_1821_,
                            v_a_1822_,
                        );
                        if leanh::lean_obj_tag(v___x_1834_) == 0 {
                            v_a_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                            leanh::lean_inc(v_a_1835_);
                            leanh::lean_dec_ref_known(v___x_1834_, 1);
                            v___x_1836_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
                                v_a_1816_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_,
                            );
                            if leanh::lean_obj_tag(v___x_1836_) == 0 {
                                v_a_1837_ = leanh::lean_ctor_get(v___x_1836_, 0);
                                leanh::lean_inc(v_a_1837_);
                                leanh::lean_dec_ref_known(v___x_1836_, 1);
                                v_fst_1838_ = leanh::lean_ctor_get(v_a_1837_, 0);
                                leanh::lean_inc(v_fst_1838_);
                                v_snd_1839_ = leanh::lean_ctor_get(v_a_1837_, 1);
                                leanh::lean_inc(v_snd_1839_);
                                leanh::lean_dec(v_a_1837_);
                                v___x_1840_ = leanh::lean_unsigned_to_nat(2);
                                v___x_1841_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1840_);
                                leanh::lean_dec(v_x_1814_);
                                v_ids_1842_ = l_Lean_Syntax_getArgs(v___x_1841_);
                                leanh::lean_dec(v___x_1841_);
                                v_sz_1843_ = lean_array_size(v_ids_1842_);
                                v___x_1844_ = leanh::lean_unsigned_to_nat(0);
                                v___x_1845_ = 0usize;
                                leanh::lean_inc_ref(v_ids_1842_);
                                v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_1843_, v___x_1845_, v_ids_1842_);
                                v___x_1847_ = lean_array_to_list(v___x_1846_);
                                v___x_1848_ =
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1;
                                v___x_1849_ = leanh::lean_box((v___x_1832_) as usize);
                                v___x_1850_ = leanh::lean_box((v___x_1830_) as usize);
                                v___f_1851_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed
                                        as *mut core::ffi::c_void,
                                    18,
                                    9,
                                );
                                leanh::lean_closure_set(v___f_1851_, 0, v___x_1844_);
                                leanh::lean_closure_set(v___f_1851_, 1, v___x_1848_);
                                leanh::lean_closure_set(v___f_1851_, 2, v___x_1849_);
                                leanh::lean_closure_set(v___f_1851_, 3, v___x_1850_);
                                leanh::lean_closure_set(v___f_1851_, 4, v_snd_1839_);
                                leanh::lean_closure_set(v___f_1851_, 5, v_fst_1838_);
                                leanh::lean_closure_set(v___f_1851_, 6, v___x_1827_);
                                leanh::lean_closure_set(v___f_1851_, 7, v___x_1847_);
                                leanh::lean_closure_set(v___f_1851_, 8, v_a_1835_);
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
                                if leanh::lean_obj_tag(v___x_1852_) == 0 {
                                    v_a_1853_ = leanh::lean_ctor_get(v___x_1852_, 0);
                                    leanh::lean_inc(v_a_1853_);
                                    leanh::lean_dec_ref_known(v___x_1852_, 1);
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
                                    leanh::lean_dec_ref(v_ids_1842_);
                                    v_a_1855_ = leanh::lean_ctor_get(v___x_1852_, 0);
                                    v_isSharedCheck_1862_ =
                                        (!leanh::lean_is_exclusive(v___x_1852_)) as u8;
                                    if v_isSharedCheck_1862_ == 0 {
                                        v___x_1857_ = v___x_1852_;
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1855_);
                                        leanh::lean_dec(v___x_1852_);
                                        v___x_1857_ = leanh::lean_box(0);
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_1835_);
                                leanh::lean_dec(v_x_1814_);
                                v_a_1863_ = leanh::lean_ctor_get(v___x_1836_, 0);
                                v_isSharedCheck_1870_ =
                                    (!leanh::lean_is_exclusive(v___x_1836_)) as u8;
                                if v_isSharedCheck_1870_ == 0 {
                                    v___x_1865_ = v___x_1836_;
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1863_);
                                    leanh::lean_dec(v___x_1836_);
                                    v___x_1865_ = leanh::lean_box(0);
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_x_1814_);
                            v_a_1871_ = leanh::lean_ctor_get(v___x_1834_, 0);
                            v_isSharedCheck_1878_ =
                                (!leanh::lean_is_exclusive(v___x_1834_)) as u8;
                            if v_isSharedCheck_1878_ == 0 {
                                v___x_1873_ = v___x_1834_;
                                v_isShared_1874_ = v_isSharedCheck_1878_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1871_);
                                leanh::lean_dec(v___x_1834_);
                                v___x_1873_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
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
                    v_reuseFailAlloc_1869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
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
                    v_reuseFailAlloc_1877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
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
    mut v_x_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
    mut v_a_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
    mut v_a_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(
        v_x_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_,
        v_a_1887_,
    );
    leanh::lean_dec(v_a_1887_);
    leanh::lean_dec_ref(v_a_1886_);
    leanh::lean_dec(v_a_1885_);
    leanh::lean_dec_ref(v_a_1884_);
    leanh::lean_dec(v_a_1883_);
    leanh::lean_dec_ref(v_a_1882_);
    leanh::lean_dec(v_a_1881_);
    leanh::lean_dec_ref(v_a_1880_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
    mut v_mvarId_1890_: *mut leanh::LeanObject,
    mut v_val_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1890_,
            v_val_1891_,
            v___y_1893_,
        );
    return v___x_1897_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(
    mut v_mvarId_1898_: *mut leanh::LeanObject,
    mut v_val_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
        v_mvarId_1898_,
        v_val_1899_,
        v___y_1900_,
        v___y_1901_,
        v___y_1902_,
        v___y_1903_,
    );
    leanh::lean_dec(v___y_1903_);
    leanh::lean_dec_ref(v___y_1902_);
    leanh::lean_dec(v___y_1901_);
    leanh::lean_dec_ref(v___y_1900_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(
    mut v_00_u03b2_1906_: *mut leanh::LeanObject,
    mut v_x_1907_: *mut leanh::LeanObject,
    mut v_x_1908_: *mut leanh::LeanObject,
    mut v_x_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_1907_, v_x_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(
    mut v_00_u03b2_1911_: *mut leanh::LeanObject,
    mut v_x_1912_: *mut leanh::LeanObject,
    mut v_x_1913_: usize,
    mut v_x_1914_: usize,
    mut v_x_1915_: *mut leanh::LeanObject,
    mut v_x_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1912_, v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(
    mut v_00_u03b2_1918_: *mut leanh::LeanObject,
    mut v_x_1919_: *mut leanh::LeanObject,
    mut v_x_1920_: *mut leanh::LeanObject,
    mut v_x_1921_: *mut leanh::LeanObject,
    mut v_x_1922_: *mut leanh::LeanObject,
    mut v_x_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7111__boxed_1924_: usize = 0;
    let mut v_x_7112__boxed_1925_: usize = 0;
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7111__boxed_1924_ = leanh::lean_unbox_usize(v_x_1920_);
    leanh::lean_dec(v_x_1920_);
    v_x_7112__boxed_1925_ = leanh::lean_unbox_usize(v_x_1921_);
    leanh::lean_dec(v_x_1921_);
    v_res_1926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_1918_, v_x_1919_, v_x_7111__boxed_1924_, v_x_7112__boxed_1925_, v_x_1922_, v_x_1923_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(
    mut v_00_u03b2_1927_: *mut leanh::LeanObject,
    mut v_n_1928_: *mut leanh::LeanObject,
    mut v_k_1929_: *mut leanh::LeanObject,
    mut v_v_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_1928_, v_k_1929_, v_v_1930_);
    return v___x_1931_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(
    mut v_00_u03b2_1932_: *mut leanh::LeanObject,
    mut v_depth_1933_: usize,
    mut v_keys_1934_: *mut leanh::LeanObject,
    mut v_vals_1935_: *mut leanh::LeanObject,
    mut v_heq_1936_: *mut leanh::LeanObject,
    mut v_i_1937_: *mut leanh::LeanObject,
    mut v_entries_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_1933_, v_keys_1934_, v_vals_1935_, v_i_1937_, v_entries_1938_);
    return v___x_1939_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_1940_: *mut leanh::LeanObject,
    mut v_depth_1941_: *mut leanh::LeanObject,
    mut v_keys_1942_: *mut leanh::LeanObject,
    mut v_vals_1943_: *mut leanh::LeanObject,
    mut v_heq_1944_: *mut leanh::LeanObject,
    mut v_i_1945_: *mut leanh::LeanObject,
    mut v_entries_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1947_ = leanh::lean_unbox_usize(v_depth_1941_);
    leanh::lean_dec(v_depth_1941_);
    v_res_1948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_1940_, v_depth_boxed_1947_, v_keys_1942_, v_vals_1943_, v_heq_1944_, v_i_1945_, v_entries_1946_);
    leanh::lean_dec_ref(v_vals_1943_);
    leanh::lean_dec_ref(v_keys_1942_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(
    mut v_00_u03b2_1949_: *mut leanh::LeanObject,
    mut v_x_1950_: *mut leanh::LeanObject,
    mut v_x_1951_: *mut leanh::LeanObject,
    mut v_x_1952_: *mut leanh::LeanObject,
    mut v_x_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1954_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
    return v___x_1954_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1()
-> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1965_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
    v___x_1966_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2;
    v___x_1967_ = leanh::lean_alloc_closure(
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
    mut v_a_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    return v_res_1970_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_a_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1984_) == 0 {
                    v_a_1985_ = leanh::lean_ctor_get(v___x_1984_, 0);
                    leanh::lean_inc_n(v_a_1985_, 2);
                    leanh::lean_dec_ref_known(v___x_1984_, 1);
                    v___x_1986_ = l_Lean_Meta_liftLets(
                        v_a_1985_,
                        v_a_1974_,
                        v___y_1979_,
                        v___y_1980_,
                        v___y_1981_,
                        v___y_1982_,
                    );
                    if leanh::lean_obj_tag(v___x_1986_) == 0 {
                        v_a_1987_ = leanh::lean_ctor_get(v___x_1986_, 0);
                        leanh::lean_inc(v_a_1987_);
                        leanh::lean_dec_ref_known(v___x_1986_, 1);
                        v___x_1988_ = lean_expr_eqv(v_a_1985_, v_a_1987_);
                        leanh::lean_dec(v_a_1985_);
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
                            if leanh::lean_obj_tag(v___x_1990_) == 0 {
                                v_a_1991_ = leanh::lean_ctor_get(v___x_1990_, 0);
                                leanh::lean_inc(v_a_1991_);
                                leanh::lean_dec_ref_known(v___x_1990_, 1);
                                v___x_1992_ =
                                    l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1;
                                v___x_1993_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_1994_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_1992_,
                                    v_a_1991_,
                                    v___x_1993_,
                                    v___y_1979_,
                                    v___y_1980_,
                                    v___y_1981_,
                                    v___y_1982_,
                                );
                                if leanh::lean_obj_tag(v___x_1994_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1994_, 1);
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
                                    leanh::lean_dec(v_a_1987_);
                                    return v___x_1994_;
                                }
                            } else {
                                leanh::lean_dec(v_a_1987_);
                                v_a_1996_ = leanh::lean_ctor_get(v___x_1990_, 0);
                                v_isSharedCheck_2003_ =
                                    (!leanh::lean_is_exclusive(v___x_1990_)) as u8;
                                if v_isSharedCheck_2003_ == 0 {
                                    v___x_1998_ = v___x_1990_;
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1996_);
                                    leanh::lean_dec(v___x_1990_);
                                    v___x_1998_ = leanh::lean_box(0);
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1985_);
                        v_a_2004_ = leanh::lean_ctor_get(v___x_1986_, 0);
                        v_isSharedCheck_2011_ =
                            (!leanh::lean_is_exclusive(v___x_1986_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2006_ = v___x_1986_;
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2004_);
                            leanh::lean_dec(v___x_1986_);
                            v___x_2006_ = leanh::lean_box(0);
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1974_);
                    v_a_2012_ = leanh::lean_ctor_get(v___x_1984_, 0);
                    v_isSharedCheck_2019_ = (!leanh::lean_is_exclusive(v___x_1984_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_1984_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2012_);
                        leanh::lean_dec(v___x_1984_);
                        v___x_2014_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
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
                    v_reuseFailAlloc_2010_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
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
                    v_reuseFailAlloc_2018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
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
    mut v_a_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2028_);
    leanh::lean_dec_ref(v___y_2027_);
    leanh::lean_dec(v___y_2026_);
    leanh::lean_dec_ref(v___y_2025_);
    leanh::lean_dec(v___y_2024_);
    leanh::lean_dec_ref(v___y_2023_);
    leanh::lean_dec(v___y_2022_);
    leanh::lean_dec_ref(v___y_2021_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets(
    mut v_x_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
    mut v_a_2040_: *mut leanh::LeanObject,
    mut v_a_2041_: *mut leanh::LeanObject,
    mut v_a_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2048_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
                leanh::lean_inc(v_x_2038_);
                v___x_2049_ = l_Lean_Syntax_isOfKind(v_x_2038_, v___x_2048_);
                if v___x_2049_ == 0 {
                    leanh::lean_dec(v_x_2038_);
                    v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_2050_;
                } else {
                    v___x_2051_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2052_ = l_Lean_Syntax_getArg(v_x_2038_, v___x_2051_);
                    leanh::lean_dec(v_x_2038_);
                    v___x_2053_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    leanh::lean_inc(v___x_2052_);
                    v___x_2054_ = l_Lean_Syntax_isOfKind(v___x_2052_, v___x_2053_);
                    if v___x_2054_ == 0 {
                        leanh::lean_dec(v___x_2052_);
                        v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_2055_;
                    } else {
                        v___x_2056_ = 0;
                        v___x_2057_ = leanh::lean_alloc_ctor(0, 0, (11) as u32);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 0 as u32, v___x_2056_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 1 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 2 as u32, v___x_2056_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 3 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 4 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 5 as u32, v___x_2056_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 6 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 7 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 8 as u32, v___x_2056_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 9 as u32, v___x_2054_);
                        leanh::lean_ctor_set_uint8(v___x_2057_, 10 as u32, v___x_2054_);
                        v___x_2058_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
                            v___x_2052_,
                            v___x_2057_,
                            v___x_2054_,
                            v_a_2039_,
                            v_a_2045_,
                            v_a_2046_,
                        );
                        if leanh::lean_obj_tag(v___x_2058_) == 0 {
                            v_a_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                            leanh::lean_inc(v_a_2059_);
                            leanh::lean_dec_ref_known(v___x_2058_, 1);
                            v___f_2060_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            leanh::lean_closure_set(v___f_2060_, 0, v_a_2059_);
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
                            v_a_2062_ = leanh::lean_ctor_get(v___x_2058_, 0);
                            v_isSharedCheck_2069_ =
                                (!leanh::lean_is_exclusive(v___x_2058_)) as u8;
                            if v_isSharedCheck_2069_ == 0 {
                                v___x_2064_ = v___x_2058_;
                                v_isShared_2065_ = v_isSharedCheck_2069_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2062_);
                                leanh::lean_dec(v___x_2058_);
                                v___x_2064_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2068_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
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
    mut v_x_2070_: *mut leanh::LeanObject,
    mut v_a_2071_: *mut leanh::LeanObject,
    mut v_a_2072_: *mut leanh::LeanObject,
    mut v_a_2073_: *mut leanh::LeanObject,
    mut v_a_2074_: *mut leanh::LeanObject,
    mut v_a_2075_: *mut leanh::LeanObject,
    mut v_a_2076_: *mut leanh::LeanObject,
    mut v_a_2077_: *mut leanh::LeanObject,
    mut v_a_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(
        v_x_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_,
        v_a_2078_,
    );
    leanh::lean_dec(v_a_2078_);
    leanh::lean_dec_ref(v_a_2077_);
    leanh::lean_dec(v_a_2076_);
    leanh::lean_dec_ref(v_a_2075_);
    leanh::lean_dec(v_a_2074_);
    leanh::lean_dec_ref(v_a_2073_);
    leanh::lean_dec(v_a_2072_);
    leanh::lean_dec_ref(v_a_2071_);
    return v_res_2080_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1()
-> *mut leanh::LeanObject {
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2090_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
    v___x_2091_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1;
    v___x_2092_ = leanh::lean_alloc_closure(
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
    mut v_a_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2095_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    return v_res_2095_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_a_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_a_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2108_) == 0 {
                    v_a_2109_ = leanh::lean_ctor_get(v___x_2108_, 0);
                    leanh::lean_inc_n(v_a_2109_, 2);
                    leanh::lean_dec_ref_known(v___x_2108_, 1);
                    v___x_2110_ = l_Lean_Meta_letToHave(
                        v_a_2109_,
                        v___y_2103_,
                        v___y_2104_,
                        v___y_2105_,
                        v___y_2106_,
                    );
                    if leanh::lean_obj_tag(v___x_2110_) == 0 {
                        v_a_2111_ = leanh::lean_ctor_get(v___x_2110_, 0);
                        leanh::lean_inc(v_a_2111_);
                        leanh::lean_dec_ref_known(v___x_2110_, 1);
                        v___x_2112_ = lean_expr_eqv(v_a_2109_, v_a_2111_);
                        leanh::lean_dec(v_a_2109_);
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
                            if leanh::lean_obj_tag(v___x_2114_) == 0 {
                                v_a_2115_ = leanh::lean_ctor_get(v___x_2114_, 0);
                                leanh::lean_inc(v_a_2115_);
                                leanh::lean_dec_ref_known(v___x_2114_, 1);
                                v___x_2116_ =
                                    l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1;
                                v___x_2117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_2118_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_2116_,
                                    v_a_2115_,
                                    v___x_2117_,
                                    v___y_2103_,
                                    v___y_2104_,
                                    v___y_2105_,
                                    v___y_2106_,
                                );
                                if leanh::lean_obj_tag(v___x_2118_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2118_, 1);
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
                                    leanh::lean_dec(v_a_2111_);
                                    return v___x_2118_;
                                }
                            } else {
                                leanh::lean_dec(v_a_2111_);
                                v_a_2120_ = leanh::lean_ctor_get(v___x_2114_, 0);
                                v_isSharedCheck_2127_ =
                                    (!leanh::lean_is_exclusive(v___x_2114_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2122_ = v___x_2114_;
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2120_);
                                    leanh::lean_dec(v___x_2114_);
                                    v___x_2122_ = leanh::lean_box(0);
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2109_);
                        v_a_2128_ = leanh::lean_ctor_get(v___x_2110_, 0);
                        v_isSharedCheck_2135_ =
                            (!leanh::lean_is_exclusive(v___x_2110_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v___x_2130_ = v___x_2110_;
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2128_);
                            leanh::lean_dec(v___x_2110_);
                            v___x_2130_ = leanh::lean_box(0);
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2136_ = leanh::lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2143_ = (!leanh::lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2143_ == 0 {
                        v___x_2138_ = v___x_2108_;
                        v_isShared_2139_ = v_isSharedCheck_2143_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2136_);
                        leanh::lean_dec(v___x_2108_);
                        v___x_2138_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
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
                    v_reuseFailAlloc_2134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
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
                    v_reuseFailAlloc_2142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
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
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2151_);
    leanh::lean_dec_ref(v___y_2150_);
    leanh::lean_dec(v___y_2149_);
    leanh::lean_dec_ref(v___y_2148_);
    leanh::lean_dec(v___y_2147_);
    leanh::lean_dec_ref(v___y_2146_);
    leanh::lean_dec(v___y_2145_);
    leanh::lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave(
    mut v_x_2162_: *mut leanh::LeanObject,
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
    mut v_a_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    v___x_2172_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2173_ = l_Lean_Syntax_isOfKind(v_x_2162_, v___x_2172_);
    if v___x_2173_ == 0 {
        let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
        return v___x_2174_;
    } else {
        let mut v___f_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2177_: *mut leanh::LeanObject,
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_a_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(
        v_x_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_,
        v_a_2185_,
    );
    leanh::lean_dec(v_a_2185_);
    leanh::lean_dec_ref(v_a_2184_);
    leanh::lean_dec(v_a_2183_);
    leanh::lean_dec_ref(v_a_2182_);
    leanh::lean_dec(v_a_2181_);
    leanh::lean_dec_ref(v_a_2180_);
    leanh::lean_dec(v_a_2179_);
    leanh::lean_dec_ref(v_a_2178_);
    return v_res_2187_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1()
-> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2197_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2198_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1;
    v___x_2199_ = leanh::lean_alloc_closure(
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
    mut v_a_2201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2202_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    return v_res_2202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Lets(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Lets(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Lets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
}