// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Have
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr6, l_Lean_Name_num___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getId,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21,
    l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo, l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabTerm,
    l_Lean_Elab_Tactic_elabTermEnsuringType, runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_consumeMData, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp7, l_Lean_mkApp8,
    l_Lean_mkApp10, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value:
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
    m_data: [72, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 117, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value:
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
    m_data: [72, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value:
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
    m_data: [109, 100, 117, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8619307128568967249 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 77, 68, 117, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value) as *mut crate::leanh::LeanObject,16089473174266965463 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value:
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
    m_data: [104, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 104, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4297332248507658187 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value) as *mut crate::leanh::LeanObject,16508224334496205735 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 112, 108, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 114, 101, 112, 108, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6001227252242998451 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 77, 82, 101, 112, 108, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value) as *mut crate::leanh::LeanObject,4360817995873788650 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = crate::leanh::lean_box(0);
    v___x_1233_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1234_, 0, v___x_1233_);
    crate::leanh::lean_ctor_set(v___x_1234_, 1, v___x_1232_);
    return v___x_1234_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0);
    v___x_1237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___boxed(
    mut v___y_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
    return v_res_1239_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(
    mut v_00_u03b1_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
    return v___x_1250_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___boxed(
    mut v_00_u03b1_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(
            v_00_u03b1_1251_,
            v___y_1252_,
            v___y_1253_,
            v___y_1254_,
            v___y_1255_,
            v___y_1256_,
            v___y_1257_,
            v___y_1258_,
            v___y_1259_,
        );
    crate::leanh::lean_dec(v___y_1259_);
    crate::leanh::lean_dec_ref(v___y_1258_);
    crate::leanh::lean_dec(v___y_1257_);
    crate::leanh::lean_dec_ref(v___y_1256_);
    crate::leanh::lean_dec(v___y_1255_);
    crate::leanh::lean_dec_ref(v___y_1254_);
    crate::leanh::lean_dec(v___y_1253_);
    crate::leanh::lean_dec_ref(v___y_1252_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
    mut v___y_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v_r_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_unused_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = lean_st_ref_get(v___y_1262_);
                v_ngen_1265_ = crate::leanh::lean_ctor_get(v___x_1264_, 2);
                crate::leanh::lean_inc_ref(v_ngen_1265_);
                crate::leanh::lean_dec(v___x_1264_);
                v_namePrefix_1266_ = crate::leanh::lean_ctor_get(v_ngen_1265_, 0);
                v_idx_1267_ = crate::leanh::lean_ctor_get(v_ngen_1265_, 1);
                v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v_ngen_1265_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v___x_1269_ = v_ngen_1265_;
                    v_isShared_1270_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1267_);
                    crate::leanh::lean_inc(v_namePrefix_1266_);
                    crate::leanh::lean_dec(v_ngen_1265_);
                    v___x_1269_ = crate::leanh::lean_box(0);
                    v_isShared_1270_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1271_ = lean_st_ref_take(v___y_1262_);
                v_env_1272_ = crate::leanh::lean_ctor_get(v___x_1271_, 0);
                v_nextMacroScope_1273_ = crate::leanh::lean_ctor_get(v___x_1271_, 1);
                v_auxDeclNGen_1274_ = crate::leanh::lean_ctor_get(v___x_1271_, 3);
                v_traceState_1275_ = crate::leanh::lean_ctor_get(v___x_1271_, 4);
                v_cache_1276_ = crate::leanh::lean_ctor_get(v___x_1271_, 5);
                v_messages_1277_ = crate::leanh::lean_ctor_get(v___x_1271_, 6);
                v_infoState_1278_ = crate::leanh::lean_ctor_get(v___x_1271_, 7);
                v_snapshotTasks_1279_ = crate::leanh::lean_ctor_get(v___x_1271_, 8);
                v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v___x_1271_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v_unused_1295_ = crate::leanh::lean_ctor_get(v___x_1271_, 2);
                    crate::leanh::lean_dec(v_unused_1295_);
                    v___x_1281_ = v___x_1271_;
                    v_isShared_1282_ = v_isSharedCheck_1294_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1279_);
                    crate::leanh::lean_inc(v_infoState_1278_);
                    crate::leanh::lean_inc(v_messages_1277_);
                    crate::leanh::lean_inc(v_cache_1276_);
                    crate::leanh::lean_inc(v_traceState_1275_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1274_);
                    crate::leanh::lean_inc(v_nextMacroScope_1273_);
                    crate::leanh::lean_inc(v_env_1272_);
                    crate::leanh::lean_dec(v___x_1271_);
                    v___x_1281_ = crate::leanh::lean_box(0);
                    v_isShared_1282_ = v_isSharedCheck_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_1267_);
                crate::leanh::lean_inc(v_namePrefix_1266_);
                v_r_1283_ = l_Lean_Name_num___override(v_namePrefix_1266_, v_idx_1267_);
                v___x_1284_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1285_ = lean_nat_add(v_idx_1267_, v___x_1284_);
                crate::leanh::lean_dec(v_idx_1267_);
                if v_isShared_1270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1269_, 1, v___x_1285_);
                    v___x_1287_ = v___x_1269_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_namePrefix_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1285_);
                    v___x_1287_ = v_reuseFailAlloc_1293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1281_, 2, v___x_1287_);
                    v___x_1289_ = v___x_1281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_env_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_nextMacroScope_1273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 2, v___x_1287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_auxDeclNGen_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_traceState_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_cache_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 6, v_messages_1277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 7, v_infoState_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1292_, 8, v_snapshotTasks_1279_);
                    v___x_1289_ = v_reuseFailAlloc_1292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1290_ = lean_st_ref_set(v___y_1262_, v___x_1289_);
                v___x_1291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1291_, 0, v_r_1283_);
                return v___x_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
        v___y_1297_,
    );
    crate::leanh::lean_dec(v___y_1297_);
    return v_res_1299_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1309_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
        v___y_1307_,
    );
    return v___x_1309_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
    );
    crate::leanh::lean_dec(v___y_1317_);
    crate::leanh::lean_dec_ref(v___y_1316_);
    crate::leanh::lean_dec(v___y_1315_);
    crate::leanh::lean_dec_ref(v___y_1314_);
    crate::leanh::lean_dec(v___y_1313_);
    crate::leanh::lean_dec_ref(v___y_1312_);
    crate::leanh::lean_dec(v___y_1311_);
    crate::leanh::lean_dec_ref(v___y_1310_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(
    mut v_x_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1324_);
    crate::leanh::lean_inc_ref(v___y_1323_);
    crate::leanh::lean_inc(v___y_1322_);
    crate::leanh::lean_inc_ref(v___y_1321_);
    v___x_1330_ = crate::leanh::lean_apply_9(
        v_x_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
        crate::leanh::lean_box(0),
    );
    return v___x_1330_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(
    mut v_x_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1341_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
    crate::leanh::lean_dec(v___y_1335_);
    crate::leanh::lean_dec_ref(v___y_1334_);
    crate::leanh::lean_dec(v___y_1333_);
    crate::leanh::lean_dec_ref(v___y_1332_);
    return v_res_1341_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
    mut v_mvarId_1342_: *mut crate::leanh::LeanObject,
    mut v_x_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1347_);
                crate::leanh::lean_inc_ref(v___y_1346_);
                crate::leanh::lean_inc(v___y_1345_);
                crate::leanh::lean_inc_ref(v___y_1344_);
                v___f_1353_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1353_, 0, v_x_1343_);
                crate::leanh::lean_closure_set(v___f_1353_, 1, v___y_1344_);
                crate::leanh::lean_closure_set(v___f_1353_, 2, v___y_1345_);
                crate::leanh::lean_closure_set(v___f_1353_, 3, v___y_1346_);
                crate::leanh::lean_closure_set(v___f_1353_, 4, v___y_1347_);
                v___x_1354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1342_,
                    v___f_1353_,
                    v___y_1348_,
                    v___y_1349_,
                    v___y_1350_,
                    v___y_1351_,
                );
                if crate::leanh::lean_obj_tag(v___x_1354_) == 0 {
                    return v___x_1354_;
                } else {
                    v_a_1355_ = crate::leanh::lean_ctor_get(v___x_1354_, 0);
                    v_isSharedCheck_1362_ = (!crate::leanh::lean_is_exclusive(v___x_1354_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1357_ = v___x_1354_;
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1355_);
                        crate::leanh::lean_dec(v___x_1354_);
                        v___x_1357_ = crate::leanh::lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(
    mut v_mvarId_1363_: *mut crate::leanh::LeanObject,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1374_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
            v_mvarId_1363_,
            v_x_1364_,
            v___y_1365_,
            v___y_1366_,
            v___y_1367_,
            v___y_1368_,
            v___y_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
        );
    crate::leanh::lean_dec(v___y_1372_);
    crate::leanh::lean_dec_ref(v___y_1371_);
    crate::leanh::lean_dec(v___y_1370_);
    crate::leanh::lean_dec_ref(v___y_1369_);
    crate::leanh::lean_dec(v___y_1368_);
    crate::leanh::lean_dec_ref(v___y_1367_);
    crate::leanh::lean_dec(v___y_1366_);
    crate::leanh::lean_dec_ref(v___y_1365_);
    return v_res_1374_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(
    mut v_00_u03b1_1375_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1376_: *mut crate::leanh::LeanObject,
    mut v_x_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
            v_mvarId_1376_,
            v_x_1377_,
            v___y_1378_,
            v___y_1379_,
            v___y_1380_,
            v___y_1381_,
            v___y_1382_,
            v___y_1383_,
            v___y_1384_,
            v___y_1385_,
        );
    return v___x_1387_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(
    mut v_00_u03b1_1388_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1389_: *mut crate::leanh::LeanObject,
    mut v_x_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
    mut v___y_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(
        v_00_u03b1_1388_,
        v_mvarId_1389_,
        v_x_1390_,
        v___y_1391_,
        v___y_1392_,
        v___y_1393_,
        v___y_1394_,
        v___y_1395_,
        v___y_1396_,
        v___y_1397_,
        v___y_1398_,
    );
    crate::leanh::lean_dec(v___y_1398_);
    crate::leanh::lean_dec_ref(v___y_1397_);
    crate::leanh::lean_dec(v___y_1396_);
    crate::leanh::lean_dec_ref(v___y_1395_);
    crate::leanh::lean_dec(v___y_1394_);
    crate::leanh::lean_dec_ref(v___y_1393_);
    crate::leanh::lean_dec(v___y_1392_);
    crate::leanh::lean_dec_ref(v___y_1391_);
    return v_res_1400_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(
    mut v_x_1401_: *mut crate::leanh::LeanObject,
    mut v_x_1402_: *mut crate::leanh::LeanObject,
    mut v_x_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1405_ = crate::leanh::lean_ctor_get(v_x_1401_, 0);
                v_vs_1406_ = crate::leanh::lean_ctor_get(v_x_1401_, 1);
                v_isSharedCheck_1430_ = (!crate::leanh::lean_is_exclusive(v_x_1401_)) as u8;
                if v_isSharedCheck_1430_ == 0 {
                    v___x_1408_ = v_x_1401_;
                    v_isShared_1409_ = v_isSharedCheck_1430_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1406_);
                    crate::leanh::lean_inc(v_ks_1405_);
                    crate::leanh::lean_dec(v_x_1401_);
                    v___x_1408_ = crate::leanh::lean_box(0);
                    v_isShared_1409_ = v_isSharedCheck_1430_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1410_ = lean_array_get_size(v_ks_1405_);
                v___x_1411_ = lean_nat_dec_lt(v_x_1402_, v___x_1410_);
                if v___x_1411_ == 0 {
                    crate::leanh::lean_dec(v_x_1402_);
                    v___x_1412_ = lean_array_push(v_ks_1405_, v_x_1403_);
                    v___x_1413_ = lean_array_push(v_vs_1406_, v_x_1404_);
                    if v_isShared_1409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1408_, 1, v___x_1413_);
                        crate::leanh::lean_ctor_set(v___x_1408_, 0, v___x_1412_);
                        v___x_1415_ = v___x_1408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1412_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
                        v___x_1415_ = v_reuseFailAlloc_1416_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1417_ = lean_array_fget_borrowed(v_ks_1405_, v_x_1402_);
                    v___x_1418_ = l_Lean_instBEqMVarId_beq(v_x_1403_, v_k_x27_1417_);
                    if v___x_1418_ == 0 {
                        if v_isShared_1409_ == 0 {
                            v___x_1420_ = v___x_1408_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1424_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_ks_1405_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_vs_1406_);
                            v___x_1420_ = v_reuseFailAlloc_1424_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1425_ = lean_array_fset(v_ks_1405_, v_x_1402_, v_x_1403_);
                        v___x_1426_ = lean_array_fset(v_vs_1406_, v_x_1402_, v_x_1404_);
                        crate::leanh::lean_dec(v_x_1402_);
                        if v_isShared_1409_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1408_, 1, v___x_1426_);
                            crate::leanh::lean_ctor_set(v___x_1408_, 0, v___x_1425_);
                            v___x_1428_ = v___x_1408_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1429_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
                            v___x_1428_ = v_reuseFailAlloc_1429_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1415_;
            }
            3 => {
                v___x_1421_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1422_ = lean_nat_add(v_x_1402_, v___x_1421_);
                crate::leanh::lean_dec(v_x_1402_);
                v_x_1401_ = v___x_1420_;
                v_x_1402_ = v___x_1422_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_n_1431_: *mut crate::leanh::LeanObject,
    mut v_k_1432_: *mut crate::leanh::LeanObject,
    mut v_v_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1435_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_1431_, v___x_1434_, v_k_1432_, v_v_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1436_: usize = 0;
    let mut v___x_1437_: usize = 0;
    let mut v___x_1438_: usize = 0;
    v___x_1436_ = 5usize;
    v___x_1437_ = 1usize;
    v___x_1438_ = lean_usize_shift_left(v___x_1437_, v___x_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: usize = 0;
    v___x_1439_ = 1usize;
    v___x_1440_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_1441_ = lean_usize_sub(v___x_1440_, v___x_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(
    mut v_x_1443_: *mut crate::leanh::LeanObject,
    mut v_x_1444_: usize,
    mut v_x_1445_: usize,
    mut v_x_1446_: *mut crate::leanh::LeanObject,
    mut v_x_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: usize = 0;
    let mut v___x_1452_: usize = 0;
    let mut v_j_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_v_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_node_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: usize = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: u8 = 0;
    let mut v_ks_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1443_) == 0 {
                    v_es_1448_ = crate::leanh::lean_ctor_get(v_x_1443_, 0);
                    v___x_1449_ = 5usize;
                    v___x_1450_ = 1usize;
                    v___x_1451_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_1452_ = lean_usize_land(v_x_1444_, v___x_1451_);
                    v_j_1453_ = lean_usize_to_nat(v___x_1452_);
                    v___x_1454_ = lean_array_get_size(v_es_1448_);
                    v___x_1455_ = lean_nat_dec_lt(v_j_1453_, v___x_1454_);
                    if v___x_1455_ == 0 {
                        crate::leanh::lean_dec(v_j_1453_);
                        crate::leanh::lean_dec(v_x_1447_);
                        crate::leanh::lean_dec(v_x_1446_);
                        return v_x_1443_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1448_);
                        v_isSharedCheck_1492_ = (!crate::leanh::lean_is_exclusive(v_x_1443_)) as u8;
                        if v_isSharedCheck_1492_ == 0 {
                            v_unused_1493_ = crate::leanh::lean_ctor_get(v_x_1443_, 0);
                            crate::leanh::lean_dec(v_unused_1493_);
                            v___x_1457_ = v_x_1443_;
                            v_isShared_1458_ = v_isSharedCheck_1492_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1443_);
                            v___x_1457_ = crate::leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1492_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1494_ = crate::leanh::lean_ctor_get(v_x_1443_, 0);
                    v_vs_1495_ = crate::leanh::lean_ctor_get(v_x_1443_, 1);
                    v_isSharedCheck_1515_ = (!crate::leanh::lean_is_exclusive(v_x_1443_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1497_ = v_x_1443_;
                        v_isShared_1498_ = v_isSharedCheck_1515_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1495_);
                        crate::leanh::lean_inc(v_ks_1494_);
                        crate::leanh::lean_dec(v_x_1443_);
                        v___x_1497_ = crate::leanh::lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1515_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1459_ = lean_array_fget(v_es_1448_, v_j_1453_);
                v___x_1460_ = crate::leanh::lean_box(0);
                v_xs_x27_1461_ = lean_array_fset(v_es_1448_, v_j_1453_, v___x_1460_);
                match crate::leanh::lean_obj_tag(v_v_1459_) {
                    0 => {
                        v_key_1468_ = crate::leanh::lean_ctor_get(v_v_1459_, 0);
                        v_val_1469_ = crate::leanh::lean_ctor_get(v_v_1459_, 1);
                        v_isSharedCheck_1479_ = (!crate::leanh::lean_is_exclusive(v_v_1459_)) as u8;
                        if v_isSharedCheck_1479_ == 0 {
                            v___x_1471_ = v_v_1459_;
                            v_isShared_1472_ = v_isSharedCheck_1479_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1469_);
                            crate::leanh::lean_inc(v_key_1468_);
                            crate::leanh::lean_dec(v_v_1459_);
                            v___x_1471_ = crate::leanh::lean_box(0);
                            v_isShared_1472_ = v_isSharedCheck_1479_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1480_ = crate::leanh::lean_ctor_get(v_v_1459_, 0);
                        v_isSharedCheck_1490_ = (!crate::leanh::lean_is_exclusive(v_v_1459_)) as u8;
                        if v_isSharedCheck_1490_ == 0 {
                            v___x_1482_ = v_v_1459_;
                            v_isShared_1483_ = v_isSharedCheck_1490_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1480_);
                            crate::leanh::lean_dec(v_v_1459_);
                            v___x_1482_ = crate::leanh::lean_box(0);
                            v_isShared_1483_ = v_isSharedCheck_1490_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1491_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1491_, 0, v_x_1446_);
                        crate::leanh::lean_ctor_set(v___x_1491_, 1, v_x_1447_);
                        v___y_1463_ = v___x_1491_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1464_ = lean_array_fset(v_xs_x27_1461_, v_j_1453_, v___y_1463_);
                crate::leanh::lean_dec(v_j_1453_);
                if v_isShared_1458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1464_);
                    v___x_1466_ = v___x_1457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1466_;
            }
            4 => {
                v___x_1473_ = l_Lean_instBEqMVarId_beq(v_x_1446_, v_key_1468_);
                if v___x_1473_ == 0 {
                    crate::leanh::lean_del_object(v___x_1471_);
                    v___x_1474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1468_,
                        v_val_1469_,
                        v_x_1446_,
                        v_x_1447_,
                    );
                    v___x_1475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                    v___y_1463_ = v___x_1475_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1469_);
                    crate::leanh::lean_dec(v_key_1468_);
                    if v_isShared_1472_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1471_, 1, v_x_1447_);
                        crate::leanh::lean_ctor_set(v___x_1471_, 0, v_x_1446_);
                        v___x_1477_ = v___x_1471_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_x_1446_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_x_1447_);
                        v___x_1477_ = v_reuseFailAlloc_1478_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1463_ = v___x_1477_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1484_ = lean_usize_shift_right(v_x_1444_, v___x_1449_);
                v___x_1485_ = lean_usize_add(v_x_1445_, v___x_1450_);
                v___x_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_1480_, v___x_1484_, v___x_1485_, v_x_1446_, v_x_1447_);
                if v_isShared_1483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1482_, 0, v___x_1486_);
                    v___x_1488_ = v___x_1482_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1463_ = v___x_1488_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1498_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_ks_1494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_vs_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1514_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1501_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_1500_, v_x_1446_, v_x_1447_);
                v___x_1509_ = 7usize;
                v___x_1510_ = lean_usize_dec_le(v___x_1509_, v_x_1445_);
                if v___x_1510_ == 0 {
                    v___x_1511_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1501_);
                    v___x_1512_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
                    crate::leanh::lean_dec(v___x_1511_);
                    v___y_1503_ = v___x_1513_;
                    state = 10;
                    continue;
                } else {
                    v___y_1503_ = v___x_1510_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1503_ == 0 {
                    v_ks_1504_ = crate::leanh::lean_ctor_get(v_newNode_1501_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1504_);
                    v_vs_1505_ = crate::leanh::lean_ctor_get(v_newNode_1501_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1505_);
                    crate::leanh::lean_dec_ref(v_newNode_1501_);
                    v___x_1506_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_1508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_1445_, v_ks_1504_, v_vs_1505_, v___x_1506_, v___x_1507_);
                    crate::leanh::lean_dec_ref(v_vs_1505_);
                    crate::leanh::lean_dec_ref(v_ks_1504_);
                    return v___x_1508_;
                } else {
                    return v_newNode_1501_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(
    mut v_depth_1516_: usize,
    mut v_keys_1517_: *mut crate::leanh::LeanObject,
    mut v_vals_1518_: *mut crate::leanh::LeanObject,
    mut v_i_1519_: *mut crate::leanh::LeanObject,
    mut v_entries_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v_k_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u64 = 0;
    let mut v_h_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: usize = 0;
    let mut v_h_1532_: usize = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = lean_array_get_size(v_keys_1517_);
                v___x_1522_ = lean_nat_dec_lt(v_i_1519_, v___x_1521_);
                if v___x_1522_ == 0 {
                    crate::leanh::lean_dec(v_i_1519_);
                    return v_entries_1520_;
                } else {
                    v_k_1523_ = lean_array_fget_borrowed(v_keys_1517_, v_i_1519_);
                    v_v_1524_ = lean_array_fget_borrowed(v_vals_1518_, v_i_1519_);
                    v___x_1525_ = l_Lean_instHashableMVarId_hash(v_k_1523_);
                    v_h_1526_ = lean_uint64_to_usize(v___x_1525_);
                    v___x_1527_ = 5usize;
                    v___x_1528_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1529_ = 1usize;
                    v___x_1530_ = lean_usize_sub(v_depth_1516_, v___x_1529_);
                    v___x_1531_ = lean_usize_mul(v___x_1527_, v___x_1530_);
                    v_h_1532_ = lean_usize_shift_right(v_h_1526_, v___x_1531_);
                    v___x_1533_ = lean_nat_add(v_i_1519_, v___x_1528_);
                    crate::leanh::lean_dec(v_i_1519_);
                    crate::leanh::lean_inc(v_v_1524_);
                    crate::leanh::lean_inc(v_k_1523_);
                    v___x_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_1520_, v_h_1532_, v_depth_1516_, v_k_1523_, v_v_1524_);
                    v_i_1519_ = v___x_1533_;
                    v_entries_1520_ = v___x_1534_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_1536_: *mut crate::leanh::LeanObject,
    mut v_keys_1537_: *mut crate::leanh::LeanObject,
    mut v_vals_1538_: *mut crate::leanh::LeanObject,
    mut v_i_1539_: *mut crate::leanh::LeanObject,
    mut v_entries_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1541_: usize = 0;
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1541_ = crate::leanh::lean_unbox_usize(v_depth_1536_);
    crate::leanh::lean_dec(v_depth_1536_);
    v_res_1542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_1541_, v_keys_1537_, v_vals_1538_, v_i_1539_, v_entries_1540_);
    crate::leanh::lean_dec_ref(v_vals_1538_);
    crate::leanh::lean_dec_ref(v_keys_1537_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1543_: *mut crate::leanh::LeanObject,
    mut v_x_1544_: *mut crate::leanh::LeanObject,
    mut v_x_1545_: *mut crate::leanh::LeanObject,
    mut v_x_1546_: *mut crate::leanh::LeanObject,
    mut v_x_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7757__boxed_1548_: usize = 0;
    let mut v_x_7758__boxed_1549_: usize = 0;
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7757__boxed_1548_ = crate::leanh::lean_unbox_usize(v_x_1544_);
    crate::leanh::lean_dec(v_x_1544_);
    v_x_7758__boxed_1549_ = crate::leanh::lean_unbox_usize(v_x_1545_);
    crate::leanh::lean_dec(v_x_1545_);
    v_res_1550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1543_, v_x_7757__boxed_1548_, v_x_7758__boxed_1549_, v_x_1546_, v_x_1547_);
    return v_res_1550_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(
    mut v_x_1551_: *mut crate::leanh::LeanObject,
    mut v_x_1552_: *mut crate::leanh::LeanObject,
    mut v_x_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: u64 = 0;
    let mut v___x_1555_: usize = 0;
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_instHashableMVarId_hash(v_x_1552_);
    v___x_1555_ = lean_uint64_to_usize(v___x_1554_);
    v___x_1556_ = 1usize;
    v___x_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1551_, v___x_1555_, v___x_1556_, v_x_1552_, v_x_1553_);
    return v___x_1557_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
    mut v_mvarId_1558_: *mut crate::leanh::LeanObject,
    mut v_val_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_depth_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1562_ = lean_st_ref_take(v___y_1560_);
                v_mctx_1563_ = crate::leanh::lean_ctor_get(v___x_1562_, 0);
                v_cache_1564_ = crate::leanh::lean_ctor_get(v___x_1562_, 1);
                v_zetaDeltaFVarIds_1565_ = crate::leanh::lean_ctor_get(v___x_1562_, 2);
                v_postponed_1566_ = crate::leanh::lean_ctor_get(v___x_1562_, 3);
                v_diag_1567_ = crate::leanh::lean_ctor_get(v___x_1562_, 4);
                v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v___x_1562_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1569_ = v___x_1562_;
                    v_isShared_1570_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1567_);
                    crate::leanh::lean_inc(v_postponed_1566_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1565_);
                    crate::leanh::lean_inc(v_cache_1564_);
                    crate::leanh::lean_inc(v_mctx_1563_);
                    crate::leanh::lean_dec(v___x_1562_);
                    v___x_1569_ = crate::leanh::lean_box(0);
                    v_isShared_1570_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1571_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 0);
                v_levelAssignDepth_1572_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 1);
                v_lmvarCounter_1573_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 2);
                v_mvarCounter_1574_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 3);
                v_lDecls_1575_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 4);
                v_decls_1576_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 5);
                v_userNames_1577_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 6);
                v_lAssignment_1578_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 7);
                v_eAssignment_1579_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 8);
                v_dAssignment_1580_ = crate::leanh::lean_ctor_get(v_mctx_1563_, 9);
                v_isSharedCheck_1594_ = (!crate::leanh::lean_is_exclusive(v_mctx_1563_)) as u8;
                if v_isSharedCheck_1594_ == 0 {
                    v___x_1582_ = v_mctx_1563_;
                    v_isShared_1583_ = v_isSharedCheck_1594_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1580_);
                    crate::leanh::lean_inc(v_eAssignment_1579_);
                    crate::leanh::lean_inc(v_lAssignment_1578_);
                    crate::leanh::lean_inc(v_userNames_1577_);
                    crate::leanh::lean_inc(v_decls_1576_);
                    crate::leanh::lean_inc(v_lDecls_1575_);
                    crate::leanh::lean_inc(v_mvarCounter_1574_);
                    crate::leanh::lean_inc(v_lmvarCounter_1573_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1572_);
                    crate::leanh::lean_inc(v_depth_1571_);
                    crate::leanh::lean_dec(v_mctx_1563_);
                    v___x_1582_ = crate::leanh::lean_box(0);
                    v_isShared_1583_ = v_isSharedCheck_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1584_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_1579_, v_mvarId_1558_, v_val_1559_);
                if v_isShared_1583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1582_, 8, v___x_1584_);
                    v___x_1586_ = v___x_1582_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_depth_1571_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1593_,
                        1,
                        v_levelAssignDepth_1572_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_lmvarCounter_1573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_mvarCounter_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_lDecls_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_decls_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_userNames_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_lAssignment_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 8, v___x_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_dAssignment_1580_);
                    v___x_1586_ = v_reuseFailAlloc_1593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_cache_1564_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1592_,
                        2,
                        v_zetaDeltaFVarIds_1565_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_postponed_1566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_diag_1567_);
                    v___x_1588_ = v_reuseFailAlloc_1592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1589_ = lean_st_ref_set(v___y_1560_, v___x_1588_);
                v___x_1590_ = crate::leanh::lean_box(0);
                v___x_1591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1590_);
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(
    mut v_mvarId_1596_: *mut crate::leanh::LeanObject,
    mut v_val_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
            v_mvarId_1596_,
            v_val_1597_,
            v___y_1598_,
        );
    crate::leanh::lean_dec(v___y_1598_);
    return v_res_1600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(
    mut v_msgData_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = lean_st_ref_get(v___y_1605_);
    v_env_1608_ = crate::leanh::lean_ctor_get(v___x_1607_, 0);
    crate::leanh::lean_inc_ref(v_env_1608_);
    crate::leanh::lean_dec(v___x_1607_);
    v___x_1609_ = lean_st_ref_get(v___y_1603_);
    v_mctx_1610_ = crate::leanh::lean_ctor_get(v___x_1609_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1610_);
    crate::leanh::lean_dec(v___x_1609_);
    v_lctx_1611_ = crate::leanh::lean_ctor_get(v___y_1602_, 2);
    v_options_1612_ = crate::leanh::lean_ctor_get(v___y_1604_, 2);
    crate::leanh::lean_inc_ref(v_options_1612_);
    crate::leanh::lean_inc_ref(v_lctx_1611_);
    v___x_1613_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1613_, 0, v_env_1608_);
    crate::leanh::lean_ctor_set(v___x_1613_, 1, v_mctx_1610_);
    crate::leanh::lean_ctor_set(v___x_1613_, 2, v_lctx_1611_);
    crate::leanh::lean_ctor_set(v___x_1613_, 3, v_options_1612_);
    v___x_1614_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1614_, 0, v___x_1613_);
    crate::leanh::lean_ctor_set(v___x_1614_, 1, v_msgData_1601_);
    v___x_1615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1615_, 0, v___x_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(
    mut v_msgData_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
    crate::leanh::lean_dec(v___y_1620_);
    crate::leanh::lean_dec_ref(v___y_1619_);
    crate::leanh::lean_dec(v___y_1618_);
    crate::leanh::lean_dec_ref(v___y_1617_);
    return v_res_1622_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
    mut v_msg_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1629_ = crate::leanh::lean_ctor_get(v___y_1626_, 5);
                v___x_1630_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
                v_a_1631_ = crate::leanh::lean_ctor_get(v___x_1630_, 0);
                v_isSharedCheck_1639_ = (!crate::leanh::lean_is_exclusive(v___x_1630_)) as u8;
                if v_isSharedCheck_1639_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    v_isShared_1634_ = v_isSharedCheck_1639_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1631_);
                    crate::leanh::lean_dec(v___x_1630_);
                    v___x_1633_ = crate::leanh::lean_box(0);
                    v_isShared_1634_ = v_isSharedCheck_1639_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1629_);
                v___x_1635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1635_, 0, v_ref_1629_);
                crate::leanh::lean_ctor_set(v___x_1635_, 1, v_a_1631_);
                if v_isShared_1634_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1633_, 1);
                    crate::leanh::lean_ctor_set(v___x_1633_, 0, v___x_1635_);
                    v___x_1637_ = v___x_1633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(
    mut v_msg_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
            v_msg_1640_,
            v___y_1641_,
            v___y_1642_,
            v___y_1643_,
            v___y_1644_,
        );
    crate::leanh::lean_dec(v___y_1644_);
    crate::leanh::lean_dec_ref(v___y_1643_);
    crate::leanh::lean_dec(v___y_1642_);
    crate::leanh::lean_dec_ref(v___y_1641_);
    return v_res_1646_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5;
    v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7;
    v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
    return v___x_1657_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(
    mut v___x_1658_: *mut crate::leanh::LeanObject,
    mut v_snd_1659_: *mut crate::leanh::LeanObject,
    mut v___x_1660_: *mut crate::leanh::LeanObject,
    mut v___x_1661_: *mut crate::leanh::LeanObject,
    mut v___x_1662_: u8,
    mut v___x_1663_: *mut crate::leanh::LeanObject,
    mut v_fst_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v_u_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v_reuseFailAlloc_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_isSharedCheck_1728_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___x_1658_) == 1 {
                    v_val_1674_ = crate::leanh::lean_ctor_get(v___x_1658_, 0);
                    crate::leanh::lean_inc(v_val_1674_);
                    crate::leanh::lean_dec_ref_known(v___x_1658_, 1);
                    v___x_1675_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1672_);
                    v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                    crate::leanh::lean_inc(v_a_1676_);
                    crate::leanh::lean_dec_ref(v___x_1675_);
                    v_focusHyp_1677_ = crate::leanh::lean_ctor_get(v_val_1674_, 0);
                    v_restHyps_1678_ = crate::leanh::lean_ctor_get(v_val_1674_, 1);
                    v_proof_1679_ = crate::leanh::lean_ctor_get(v_val_1674_, 2);
                    v_isSharedCheck_1728_ = (!crate::leanh::lean_is_exclusive(v_val_1674_)) as u8;
                    if v_isSharedCheck_1728_ == 0 {
                        v___x_1681_ = v_val_1674_;
                        v_isShared_1682_ = v_isSharedCheck_1728_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_proof_1679_);
                        crate::leanh::lean_inc(v_restHyps_1678_);
                        crate::leanh::lean_inc(v_focusHyp_1677_);
                        crate::leanh::lean_dec(v_val_1674_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1728_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1664_);
                    crate::leanh::lean_dec_ref(v___x_1663_);
                    crate::leanh::lean_dec_ref(v_snd_1659_);
                    crate::leanh::lean_dec(v___x_1658_);
                    v___x_1729_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6,
                    );
                    v___x_1730_ = l_Lean_MessageData_ofSyntax(v___x_1661_);
                    v___x_1731_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                    crate::leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                    v___x_1732_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8,
                    );
                    v___x_1733_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1731_);
                    crate::leanh::lean_ctor_set(v___x_1733_, 1, v___x_1732_);
                    v___x_1734_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1733_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
                    return v___x_1734_;
                }
            }
            1 => {
                v_u_1683_ = crate::leanh::lean_ctor_get(v_snd_1659_, 0);
                v_00_u03c3s_1684_ = crate::leanh::lean_ctor_get(v_snd_1659_, 1);
                v_hyps_1685_ = crate::leanh::lean_ctor_get(v_snd_1659_, 2);
                v_target_1686_ = crate::leanh::lean_ctor_get(v_snd_1659_, 3);
                v_isSharedCheck_1727_ = (!crate::leanh::lean_is_exclusive(v_snd_1659_)) as u8;
                if v_isSharedCheck_1727_ == 0 {
                    v___x_1688_ = v_snd_1659_;
                    v_isShared_1689_ = v_isSharedCheck_1727_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_1686_);
                    crate::leanh::lean_inc(v_hyps_1685_);
                    crate::leanh::lean_inc(v_00_u03c3s_1684_);
                    crate::leanh::lean_inc(v_u_1683_);
                    crate::leanh::lean_dec(v_snd_1659_);
                    v___x_1688_ = crate::leanh::lean_box(0);
                    v_isShared_1689_ = v_isSharedCheck_1727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1690_ = l_Lean_Syntax_getId(v___x_1660_);
                v___x_1691_ = l_Lean_Expr_consumeMData(v_focusHyp_1677_);
                if v_isShared_1682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1681_, 2, v___x_1691_);
                    crate::leanh::lean_ctor_set(v___x_1681_, 1, v_a_1676_);
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1690_);
                    v___x_1693_ = v___x_1681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_a_1676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 2, v___x_1691_);
                    v___x_1693_ = v_reuseFailAlloc_1726_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_1693_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_1684_);
                v___x_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_1661_,
                    v_00_u03c3s_1684_,
                    v___x_1693_,
                    v___x_1662_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                );
                if crate::leanh::lean_obj_tag(v___x_1694_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1694_, 1);
                    v___x_1695_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1693_);
                    crate::leanh::lean_inc_ref(v_hyps_1685_);
                    crate::leanh::lean_inc_ref_n(v_00_u03c3s_1684_, 2);
                    crate::leanh::lean_inc_n(v_u_1683_, 2);
                    v___x_1696_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                        v_u_1683_,
                        v_00_u03c3s_1684_,
                        v_hyps_1685_,
                        v___x_1695_,
                    );
                    crate::leanh::lean_inc_ref(v_target_1686_);
                    if v_isShared_1689_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1688_, 2, v___x_1696_);
                        v___x_1698_ = v___x_1688_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1725_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_u_1683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_00_u03c3s_1684_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 2, v___x_1696_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_target_1686_);
                        v___x_1698_ = v_reuseFailAlloc_1725_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1693_);
                    crate::leanh::lean_del_object(v___x_1688_);
                    crate::leanh::lean_dec_ref(v_target_1686_);
                    crate::leanh::lean_dec_ref(v_hyps_1685_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1684_);
                    crate::leanh::lean_dec(v_u_1683_);
                    crate::leanh::lean_dec_ref(v_proof_1679_);
                    crate::leanh::lean_dec_ref(v_restHyps_1678_);
                    crate::leanh::lean_dec_ref(v_focusHyp_1677_);
                    crate::leanh::lean_dec(v_fst_1664_);
                    crate::leanh::lean_dec_ref(v___x_1663_);
                    return v___x_1694_;
                }
            }
            4 => {
                v___x_1699_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1698_);
                v___x_1700_ = crate::leanh::lean_box(0);
                v___x_1701_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1699_,
                    v___x_1700_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                );
                if crate::leanh::lean_obj_tag(v___x_1701_) == 0 {
                    v_a_1702_ = crate::leanh::lean_ctor_get(v___x_1701_, 0);
                    crate::leanh::lean_inc_n(v_a_1702_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1701_, 1);
                    v___x_1703_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                    v___x_1704_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                    v___x_1705_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                    v___x_1706_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                    v___x_1707_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4;
                    v___x_1708_ = l_Lean_Name_mkStr6(
                        v___x_1703_,
                        v___x_1704_,
                        v___x_1705_,
                        v___x_1663_,
                        v___x_1706_,
                        v___x_1707_,
                    );
                    v___x_1709_ = crate::leanh::lean_box(0);
                    v___x_1710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1710_, 0, v_u_1683_);
                    crate::leanh::lean_ctor_set(v___x_1710_, 1, v___x_1709_);
                    v___x_1711_ = l_Lean_mkConst(v___x_1708_, v___x_1710_);
                    v___x_1712_ = l_Lean_mkApp7(
                        v___x_1711_,
                        v_00_u03c3s_1684_,
                        v_hyps_1685_,
                        v_restHyps_1678_,
                        v_focusHyp_1677_,
                        v_target_1686_,
                        v_proof_1679_,
                        v_a_1702_,
                    );
                    v___x_1713_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_1664_, v___x_1712_, v___y_1670_);
                    crate::leanh::lean_dec_ref(v___x_1713_);
                    v___x_1714_ = l_Lean_Expr_mvarId_x21(v_a_1702_);
                    crate::leanh::lean_dec(v_a_1702_);
                    v___x_1715_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                    crate::leanh::lean_ctor_set(v___x_1715_, 1, v___x_1709_);
                    v___x_1716_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1715_,
                        v___y_1666_,
                        v___y_1669_,
                        v___y_1670_,
                        v___y_1671_,
                        v___y_1672_,
                    );
                    return v___x_1716_;
                } else {
                    crate::leanh::lean_dec_ref(v_target_1686_);
                    crate::leanh::lean_dec_ref(v_hyps_1685_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1684_);
                    crate::leanh::lean_dec(v_u_1683_);
                    crate::leanh::lean_dec_ref(v_proof_1679_);
                    crate::leanh::lean_dec_ref(v_restHyps_1678_);
                    crate::leanh::lean_dec_ref(v_focusHyp_1677_);
                    crate::leanh::lean_dec(v_fst_1664_);
                    crate::leanh::lean_dec_ref(v___x_1663_);
                    v_a_1717_ = crate::leanh::lean_ctor_get(v___x_1701_, 0);
                    v_isSharedCheck_1724_ = (!crate::leanh::lean_is_exclusive(v___x_1701_)) as u8;
                    if v_isSharedCheck_1724_ == 0 {
                        v___x_1719_ = v___x_1701_;
                        v_isShared_1720_ = v_isSharedCheck_1724_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1717_);
                        crate::leanh::lean_dec(v___x_1701_);
                        v___x_1719_ = crate::leanh::lean_box(0);
                        v_isShared_1720_ = v_isSharedCheck_1724_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1720_ == 0 {
                    v___x_1722_ = v___x_1719_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
                    v___x_1722_ = v_reuseFailAlloc_1723_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(
    mut v___x_1735_: *mut crate::leanh::LeanObject,
    mut v_snd_1736_: *mut crate::leanh::LeanObject,
    mut v___x_1737_: *mut crate::leanh::LeanObject,
    mut v___x_1738_: *mut crate::leanh::LeanObject,
    mut v___x_1739_: *mut crate::leanh::LeanObject,
    mut v___x_1740_: *mut crate::leanh::LeanObject,
    mut v_fst_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8063__boxed_1751_: u8 = 0;
    let mut v_res_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8063__boxed_1751_ = (crate::leanh::lean_unbox(v___x_1739_) as u8);
    v_res_1752_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(
        v___x_1735_,
        v_snd_1736_,
        v___x_1737_,
        v___x_1738_,
        v___x_8063__boxed_1751_,
        v___x_1740_,
        v_fst_1741_,
        v___y_1742_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
        v___y_1746_,
        v___y_1747_,
        v___y_1748_,
        v___y_1749_,
    );
    crate::leanh::lean_dec(v___y_1749_);
    crate::leanh::lean_dec_ref(v___y_1748_);
    crate::leanh::lean_dec(v___y_1747_);
    crate::leanh::lean_dec_ref(v___y_1746_);
    crate::leanh::lean_dec(v___y_1745_);
    crate::leanh::lean_dec_ref(v___y_1744_);
    crate::leanh::lean_dec(v___y_1743_);
    crate::leanh::lean_dec_ref(v___y_1742_);
    crate::leanh::lean_dec(v___x_1737_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(
    mut v_x_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_1776_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4;
                crate::leanh::lean_inc(v_x_1765_);
                v___x_1777_ = l_Lean_Syntax_isOfKind(v_x_1765_, v___x_1776_);
                if v___x_1777_ == 0 {
                    crate::leanh::lean_dec(v_x_1765_);
                    v___x_1778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_1778_;
                } else {
                    v___x_1779_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1780_ = l_Lean_Syntax_getArg(v_x_1765_, v___x_1779_);
                    v___x_1781_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6;
                    crate::leanh::lean_inc(v___x_1780_);
                    v___x_1782_ = l_Lean_Syntax_isOfKind(v___x_1780_, v___x_1781_);
                    if v___x_1782_ == 0 {
                        crate::leanh::lean_dec(v___x_1780_);
                        crate::leanh::lean_dec(v_x_1765_);
                        v___x_1783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                        return v___x_1783_;
                    } else {
                        v___x_1784_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1785_ = l_Lean_Syntax_getArg(v_x_1765_, v___x_1784_);
                        crate::leanh::lean_dec(v_x_1765_);
                        crate::leanh::lean_inc(v___x_1785_);
                        v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1785_, v___x_1781_);
                        if v___x_1786_ == 0 {
                            crate::leanh::lean_dec(v___x_1785_);
                            crate::leanh::lean_dec(v___x_1780_);
                            v___x_1787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_1787_;
                        } else {
                            v___x_1788_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                                v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_,
                                v_a_1772_, v_a_1773_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1788_) == 0 {
                                v_a_1789_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                                crate::leanh::lean_inc(v_a_1789_);
                                crate::leanh::lean_dec_ref_known(v___x_1788_, 1);
                                v_fst_1790_ = crate::leanh::lean_ctor_get(v_a_1789_, 0);
                                crate::leanh::lean_inc_n(v_fst_1790_, 2);
                                v_snd_1791_ = crate::leanh::lean_ctor_get(v_a_1789_, 1);
                                crate::leanh::lean_inc_n(v_snd_1791_, 2);
                                crate::leanh::lean_dec(v_a_1789_);
                                v___x_1792_ = l_Lean_Syntax_getId(v___x_1780_);
                                v___x_1793_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(
                                    v_snd_1791_,
                                    v___x_1792_,
                                );
                                crate::leanh::lean_dec(v___x_1792_);
                                v___x_1794_ = crate::leanh::lean_box((v___x_1786_) as usize);
                                v___y_1795_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    16,
                                    7,
                                );
                                crate::leanh::lean_closure_set(v___y_1795_, 0, v___x_1793_);
                                crate::leanh::lean_closure_set(v___y_1795_, 1, v_snd_1791_);
                                crate::leanh::lean_closure_set(v___y_1795_, 2, v___x_1785_);
                                crate::leanh::lean_closure_set(v___y_1795_, 3, v___x_1780_);
                                crate::leanh::lean_closure_set(v___y_1795_, 4, v___x_1794_);
                                crate::leanh::lean_closure_set(v___y_1795_, 5, v___x_1775_);
                                crate::leanh::lean_closure_set(v___y_1795_, 6, v_fst_1790_);
                                v___x_1796_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1790_, v___y_1795_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
                                return v___x_1796_;
                            } else {
                                crate::leanh::lean_dec(v___x_1785_);
                                crate::leanh::lean_dec(v___x_1780_);
                                v_a_1797_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                                v_isSharedCheck_1804_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1788_)) as u8;
                                if v_isSharedCheck_1804_ == 0 {
                                    v___x_1799_ = v___x_1788_;
                                    v_isShared_1800_ = v_isSharedCheck_1804_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1797_);
                                    crate::leanh::lean_dec(v___x_1788_);
                                    v___x_1799_ = crate::leanh::lean_box(0);
                                    v_isShared_1800_ = v_isSharedCheck_1804_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1800_ == 0 {
                    v___x_1802_ = v___x_1799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(
    mut v_x_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
    mut v_a_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_a_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1815_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(
        v_x_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_,
        v_a_1813_,
    );
    crate::leanh::lean_dec(v_a_1813_);
    crate::leanh::lean_dec_ref(v_a_1812_);
    crate::leanh::lean_dec(v_a_1811_);
    crate::leanh::lean_dec_ref(v_a_1810_);
    crate::leanh::lean_dec(v_a_1809_);
    crate::leanh::lean_dec_ref(v_a_1808_);
    crate::leanh::lean_dec(v_a_1807_);
    crate::leanh::lean_dec_ref(v_a_1806_);
    return v_res_1815_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(
    mut v_mvarId_1816_: *mut crate::leanh::LeanObject,
    mut v_val_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
            v_mvarId_1816_,
            v_val_1817_,
            v___y_1823_,
        );
    return v___x_1827_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(
    mut v_mvarId_1828_: *mut crate::leanh::LeanObject,
    mut v_val_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
    mut v___y_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(
        v_mvarId_1828_,
        v_val_1829_,
        v___y_1830_,
        v___y_1831_,
        v___y_1832_,
        v___y_1833_,
        v___y_1834_,
        v___y_1835_,
        v___y_1836_,
        v___y_1837_,
    );
    crate::leanh::lean_dec(v___y_1837_);
    crate::leanh::lean_dec_ref(v___y_1836_);
    crate::leanh::lean_dec(v___y_1835_);
    crate::leanh::lean_dec_ref(v___y_1834_);
    crate::leanh::lean_dec(v___y_1833_);
    crate::leanh::lean_dec_ref(v___y_1832_);
    crate::leanh::lean_dec(v___y_1831_);
    crate::leanh::lean_dec_ref(v___y_1830_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(
    mut v_00_u03b1_1840_: *mut crate::leanh::LeanObject,
    mut v_msg_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
            v_msg_1841_,
            v___y_1846_,
            v___y_1847_,
            v___y_1848_,
            v___y_1849_,
        );
    return v___x_1851_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(
    mut v_00_u03b1_1852_: *mut crate::leanh::LeanObject,
    mut v_msg_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(
        v_00_u03b1_1852_,
        v_msg_1853_,
        v___y_1854_,
        v___y_1855_,
        v___y_1856_,
        v___y_1857_,
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
        v___y_1861_,
    );
    crate::leanh::lean_dec(v___y_1861_);
    crate::leanh::lean_dec_ref(v___y_1860_);
    crate::leanh::lean_dec(v___y_1859_);
    crate::leanh::lean_dec_ref(v___y_1858_);
    crate::leanh::lean_dec(v___y_1857_);
    crate::leanh::lean_dec_ref(v___y_1856_);
    crate::leanh::lean_dec(v___y_1855_);
    crate::leanh::lean_dec_ref(v___y_1854_);
    return v_res_1863_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(
    mut v_00_u03b2_1864_: *mut crate::leanh::LeanObject,
    mut v_x_1865_: *mut crate::leanh::LeanObject,
    mut v_x_1866_: *mut crate::leanh::LeanObject,
    mut v_x_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_1865_, v_x_1866_, v_x_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1869_: *mut crate::leanh::LeanObject,
    mut v_x_1870_: *mut crate::leanh::LeanObject,
    mut v_x_1871_: usize,
    mut v_x_1872_: usize,
    mut v_x_1873_: *mut crate::leanh::LeanObject,
    mut v_x_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
    mut v_x_1878_: *mut crate::leanh::LeanObject,
    mut v_x_1879_: *mut crate::leanh::LeanObject,
    mut v_x_1880_: *mut crate::leanh::LeanObject,
    mut v_x_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8400__boxed_1882_: usize = 0;
    let mut v_x_8401__boxed_1883_: usize = 0;
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8400__boxed_1882_ = crate::leanh::lean_unbox_usize(v_x_1878_);
    crate::leanh::lean_dec(v_x_1878_);
    v_x_8401__boxed_1883_ = crate::leanh::lean_unbox_usize(v_x_1879_);
    crate::leanh::lean_dec(v_x_1879_);
    v_res_1884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_1876_, v_x_1877_, v_x_8400__boxed_1882_, v_x_8401__boxed_1883_, v_x_1880_, v_x_1881_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1885_: *mut crate::leanh::LeanObject,
    mut v_n_1886_: *mut crate::leanh::LeanObject,
    mut v_k_1887_: *mut crate::leanh::LeanObject,
    mut v_v_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_1886_, v_k_1887_, v_v_1888_);
    return v___x_1889_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1890_: *mut crate::leanh::LeanObject,
    mut v_depth_1891_: usize,
    mut v_keys_1892_: *mut crate::leanh::LeanObject,
    mut v_vals_1893_: *mut crate::leanh::LeanObject,
    mut v_heq_1894_: *mut crate::leanh::LeanObject,
    mut v_i_1895_: *mut crate::leanh::LeanObject,
    mut v_entries_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_1891_, v_keys_1892_, v_vals_1893_, v_i_1895_, v_entries_1896_);
    return v___x_1897_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_1898_: *mut crate::leanh::LeanObject,
    mut v_depth_1899_: *mut crate::leanh::LeanObject,
    mut v_keys_1900_: *mut crate::leanh::LeanObject,
    mut v_vals_1901_: *mut crate::leanh::LeanObject,
    mut v_heq_1902_: *mut crate::leanh::LeanObject,
    mut v_i_1903_: *mut crate::leanh::LeanObject,
    mut v_entries_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1905_: usize = 0;
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1905_ = crate::leanh::lean_unbox_usize(v_depth_1899_);
    crate::leanh::lean_dec(v_depth_1899_);
    v_res_1906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_1898_, v_depth_boxed_1905_, v_keys_1900_, v_vals_1901_, v_heq_1902_, v_i_1903_, v_entries_1904_);
    crate::leanh::lean_dec_ref(v_vals_1901_);
    crate::leanh::lean_dec_ref(v_keys_1900_);
    return v_res_1906_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(
    mut v_00_u03b2_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
    mut v_x_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_1908_, v_x_1909_, v_x_1910_, v_x_1911_);
    return v___x_1912_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1925_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4;
    v___x_1926_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3;
    v___x_1927_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1928_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1924_,
        v___x_1925_,
        v___x_1926_,
        v___x_1927_,
    );
    return v___x_1928_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(
    mut v_a_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
    return v_res_1930_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(
    mut v___x_1932_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_1933_: *mut crate::leanh::LeanObject,
    mut v___x_1934_: u8,
    mut v_u_1935_: *mut crate::leanh::LeanObject,
    mut v_hyps_1936_: *mut crate::leanh::LeanObject,
    mut v___x_1937_: *mut crate::leanh::LeanObject,
    mut v_target_1938_: *mut crate::leanh::LeanObject,
    mut v___x_1939_: *mut crate::leanh::LeanObject,
    mut v___x_1940_: *mut crate::leanh::LeanObject,
    mut v___x_1941_: *mut crate::leanh::LeanObject,
    mut v___x_1942_: *mut crate::leanh::LeanObject,
    mut v___x_1943_: *mut crate::leanh::LeanObject,
    mut v_fst_1944_: *mut crate::leanh::LeanObject,
    mut v_H_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_unused_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1955_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1953_);
                v_a_1956_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                crate::leanh::lean_inc(v_a_1956_);
                crate::leanh::lean_dec_ref(v___x_1955_);
                v___x_1957_ = l_Lean_Syntax_getId(v___x_1932_);
                crate::leanh::lean_inc_ref(v_H_1945_);
                v___x_1958_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1957_);
                crate::leanh::lean_ctor_set(v___x_1958_, 1, v_a_1956_);
                crate::leanh::lean_ctor_set(v___x_1958_, 2, v_H_1945_);
                crate::leanh::lean_inc_ref(v___x_1958_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_1933_);
                v___x_1959_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_1932_,
                    v_00_u03c3s_1933_,
                    v___x_1958_,
                    v___x_1934_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                if crate::leanh::lean_obj_tag(v___x_1959_) == 0 {
                    v_isSharedCheck_2012_ = (!crate::leanh::lean_is_exclusive(v___x_1959_)) as u8;
                    if v_isSharedCheck_2012_ == 0 {
                        v_unused_2013_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
                        crate::leanh::lean_dec(v_unused_2013_);
                        v___x_1961_ = v___x_1959_;
                        v_isShared_1962_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1959_);
                        v___x_1961_ = crate::leanh::lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1958_, 3);
                    crate::leanh::lean_dec_ref(v_H_1945_);
                    crate::leanh::lean_dec(v_fst_1944_);
                    crate::leanh::lean_dec(v___x_1943_);
                    crate::leanh::lean_dec_ref(v___x_1942_);
                    crate::leanh::lean_dec_ref(v___x_1941_);
                    crate::leanh::lean_dec_ref(v___x_1940_);
                    crate::leanh::lean_dec_ref(v___x_1939_);
                    crate::leanh::lean_dec_ref(v_target_1938_);
                    crate::leanh::lean_dec(v___x_1937_);
                    crate::leanh::lean_dec_ref(v_hyps_1936_);
                    crate::leanh::lean_dec(v_u_1935_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1933_);
                    return v___x_1959_;
                }
            }
            1 => {
                v___x_1963_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1958_);
                crate::leanh::lean_inc_ref(v___x_1963_);
                crate::leanh::lean_inc_ref(v_hyps_1936_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_1933_);
                crate::leanh::lean_inc(v_u_1935_);
                v___x_1964_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_1935_,
                    v_00_u03c3s_1933_,
                    v_hyps_1936_,
                    v___x_1963_,
                );
                v_fst_1965_ = crate::leanh::lean_ctor_get(v___x_1964_, 0);
                v_snd_1966_ = crate::leanh::lean_ctor_get(v___x_1964_, 1);
                v_isSharedCheck_2011_ = (!crate::leanh::lean_is_exclusive(v___x_1964_)) as u8;
                if v_isSharedCheck_2011_ == 0 {
                    v___x_1968_ = v___x_1964_;
                    v_isShared_1969_ = v_isSharedCheck_2011_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1966_);
                    crate::leanh::lean_inc(v_fst_1965_);
                    crate::leanh::lean_dec(v___x_1964_);
                    v___x_1968_ = crate::leanh::lean_box(0);
                    v_isShared_1969_ = v_isSharedCheck_2011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_hyps_1936_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_1933_);
                crate::leanh::lean_inc(v_u_1935_);
                v___x_1970_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1970_, 0, v_u_1935_);
                crate::leanh::lean_ctor_set(v___x_1970_, 1, v_00_u03c3s_1933_);
                crate::leanh::lean_ctor_set(v___x_1970_, 2, v_hyps_1936_);
                crate::leanh::lean_ctor_set(v___x_1970_, 3, v_H_1945_);
                v___x_1971_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1970_);
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1961_, 1);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1971_);
                    v___x_1973_ = v_reuseFailAlloc_2010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1974_ = 0;
                v___x_1975_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
                    v___x_1937_,
                    v___x_1973_,
                    v___x_1974_,
                    v___y_1946_,
                    v___y_1947_,
                    v___y_1948_,
                    v___y_1949_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                    crate::leanh::lean_inc(v_a_1976_);
                    crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                    crate::leanh::lean_inc_ref(v_target_1938_);
                    crate::leanh::lean_inc(v_fst_1965_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_1933_);
                    v___x_1977_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1977_, 0, v_u_1935_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 1, v_00_u03c3s_1933_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 2, v_fst_1965_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 3, v_target_1938_);
                    v___x_1978_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1977_);
                    v___x_1979_ = crate::leanh::lean_box(0);
                    v___x_1980_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1978_,
                        v___x_1979_,
                        v___y_1950_,
                        v___y_1951_,
                        v___y_1952_,
                        v___y_1953_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1980_) == 0 {
                        v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                        crate::leanh::lean_inc_n(v_a_1981_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1980_, 1);
                        v___x_1982_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                        v___x_1983_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0;
                        v___x_1984_ = l_Lean_Name_mkStr6(
                            v___x_1939_,
                            v___x_1940_,
                            v___x_1941_,
                            v___x_1942_,
                            v___x_1982_,
                            v___x_1983_,
                        );
                        v___x_1985_ = l_Lean_mkConst(v___x_1984_, v___x_1943_);
                        v___x_1986_ = l_Lean_mkApp8(
                            v___x_1985_,
                            v_00_u03c3s_1933_,
                            v_hyps_1936_,
                            v___x_1963_,
                            v_fst_1965_,
                            v_target_1938_,
                            v_snd_1966_,
                            v_a_1976_,
                            v_a_1981_,
                        );
                        v___x_1987_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_1944_, v___x_1986_, v___y_1951_);
                        crate::leanh::lean_dec_ref(v___x_1987_);
                        v___x_1988_ = l_Lean_Expr_mvarId_x21(v_a_1981_);
                        crate::leanh::lean_dec(v_a_1981_);
                        v___x_1989_ = crate::leanh::lean_box(0);
                        if v_isShared_1969_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1968_, 1);
                            crate::leanh::lean_ctor_set(v___x_1968_, 1, v___x_1989_);
                            crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1988_);
                            v___x_1991_ = v___x_1968_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1993_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1988_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1989_);
                            v___x_1991_ = v_reuseFailAlloc_1993_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1976_);
                        crate::leanh::lean_del_object(v___x_1968_);
                        crate::leanh::lean_dec(v_snd_1966_);
                        crate::leanh::lean_dec(v_fst_1965_);
                        crate::leanh::lean_dec_ref(v___x_1963_);
                        crate::leanh::lean_dec(v_fst_1944_);
                        crate::leanh::lean_dec(v___x_1943_);
                        crate::leanh::lean_dec_ref(v___x_1942_);
                        crate::leanh::lean_dec_ref(v___x_1941_);
                        crate::leanh::lean_dec_ref(v___x_1940_);
                        crate::leanh::lean_dec_ref(v___x_1939_);
                        crate::leanh::lean_dec_ref(v_target_1938_);
                        crate::leanh::lean_dec_ref(v_hyps_1936_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_1933_);
                        v_a_1994_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                        v_isSharedCheck_2001_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1980_)) as u8;
                        if v_isSharedCheck_2001_ == 0 {
                            v___x_1996_ = v___x_1980_;
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1994_);
                            crate::leanh::lean_dec(v___x_1980_);
                            v___x_1996_ = crate::leanh::lean_box(0);
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1968_);
                    crate::leanh::lean_dec(v_snd_1966_);
                    crate::leanh::lean_dec(v_fst_1965_);
                    crate::leanh::lean_dec_ref(v___x_1963_);
                    crate::leanh::lean_dec(v_fst_1944_);
                    crate::leanh::lean_dec(v___x_1943_);
                    crate::leanh::lean_dec_ref(v___x_1942_);
                    crate::leanh::lean_dec_ref(v___x_1941_);
                    crate::leanh::lean_dec_ref(v___x_1940_);
                    crate::leanh::lean_dec_ref(v___x_1939_);
                    crate::leanh::lean_dec_ref(v_target_1938_);
                    crate::leanh::lean_dec_ref(v_hyps_1936_);
                    crate::leanh::lean_dec(v_u_1935_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1933_);
                    v_a_2002_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2009_ = (!crate::leanh::lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1975_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2002_);
                        crate::leanh::lean_dec(v___x_1975_);
                        v___x_2004_ = crate::leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1992_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_1991_,
                    v___y_1947_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                return v___x_1992_;
            }
            5 => {
                if v_isShared_1997_ == 0 {
                    v___x_1999_ = v___x_1996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1999_;
            }
            7 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3s_2015_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2016_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_u_2017_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_hyps_2018_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2019_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_target_2020_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2021_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2022_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2023_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2024_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2025_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_fst_2026_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_H_2027_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2028_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2029_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2030_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2031_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2032_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2033_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2034_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_2035_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_2036_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___x_2878__boxed_2037_: u8 = 0;
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878__boxed_2037_ = (crate::leanh::lean_unbox(v___x_2016_) as u8);
    v_res_2038_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(
        v___x_2014_,
        v_00_u03c3s_2015_,
        v___x_2878__boxed_2037_,
        v_u_2017_,
        v_hyps_2018_,
        v___x_2019_,
        v_target_2020_,
        v___x_2021_,
        v___x_2022_,
        v___x_2023_,
        v___x_2024_,
        v___x_2025_,
        v_fst_2026_,
        v_H_2027_,
        v___y_2028_,
        v___y_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
        v___y_2033_,
        v___y_2034_,
        v___y_2035_,
    );
    crate::leanh::lean_dec(v___y_2035_);
    crate::leanh::lean_dec_ref(v___y_2034_);
    crate::leanh::lean_dec(v___y_2033_);
    crate::leanh::lean_dec_ref(v___y_2032_);
    crate::leanh::lean_dec(v___y_2031_);
    crate::leanh::lean_dec_ref(v___y_2030_);
    crate::leanh::lean_dec(v___y_2029_);
    crate::leanh::lean_dec_ref(v___y_2028_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(
    mut v_ty_x3f_2039_: *mut crate::leanh::LeanObject,
    mut v___x_2040_: *mut crate::leanh::LeanObject,
    mut v___f_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_ty_x3f_2039_) == 1 {
                    v_val_2051_ = crate::leanh::lean_ctor_get(v_ty_x3f_2039_, 0);
                    v_isSharedCheck_2070_ =
                        (!crate::leanh::lean_is_exclusive(v_ty_x3f_2039_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v___x_2053_ = v_ty_x3f_2039_;
                        v_isShared_2054_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2051_);
                        crate::leanh::lean_dec(v_ty_x3f_2039_);
                        v___x_2053_ = crate::leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_x3f_2039_);
                    v___x_2071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2071_, 0, v___x_2040_);
                    v___x_2072_ = 0;
                    v___x_2073_ = crate::leanh::lean_box(0);
                    v___x_2074_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_2071_,
                        v___x_2072_,
                        v___x_2073_,
                        v___y_2046_,
                        v___y_2047_,
                        v___y_2048_,
                        v___y_2049_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2074_) == 0 {
                        v_a_2075_ = crate::leanh::lean_ctor_get(v___x_2074_, 0);
                        crate::leanh::lean_inc(v_a_2075_);
                        crate::leanh::lean_dec_ref_known(v___x_2074_, 1);
                        crate::leanh::lean_inc(v___y_2049_);
                        crate::leanh::lean_inc_ref(v___y_2048_);
                        crate::leanh::lean_inc(v___y_2047_);
                        crate::leanh::lean_inc_ref(v___y_2046_);
                        crate::leanh::lean_inc(v___y_2045_);
                        crate::leanh::lean_inc_ref(v___y_2044_);
                        crate::leanh::lean_inc(v___y_2043_);
                        crate::leanh::lean_inc_ref(v___y_2042_);
                        v___x_2076_ = crate::leanh::lean_apply_10(
                            v___f_2041_,
                            v_a_2075_,
                            v___y_2042_,
                            v___y_2043_,
                            v___y_2044_,
                            v___y_2045_,
                            v___y_2046_,
                            v___y_2047_,
                            v___y_2048_,
                            v___y_2049_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_2076_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_2041_);
                        v_a_2077_ = crate::leanh::lean_ctor_get(v___x_2074_, 0);
                        v_isSharedCheck_2084_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2074_)) as u8;
                        if v_isSharedCheck_2084_ == 0 {
                            v___x_2079_ = v___x_2074_;
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2077_);
                            crate::leanh::lean_dec(v___x_2074_);
                            v___x_2079_ = crate::leanh::lean_box(0);
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2053_, 0, v___x_2040_);
                    v___x_2056_ = v___x_2053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2040_);
                    v___x_2056_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2057_ = 0;
                v___x_2058_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_2051_,
                    v___x_2056_,
                    v___x_2057_,
                    v___y_2042_,
                    v___y_2043_,
                    v___y_2044_,
                    v___y_2045_,
                    v___y_2046_,
                    v___y_2047_,
                    v___y_2048_,
                    v___y_2049_,
                );
                if crate::leanh::lean_obj_tag(v___x_2058_) == 0 {
                    v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                    crate::leanh::lean_inc(v_a_2059_);
                    crate::leanh::lean_dec_ref_known(v___x_2058_, 1);
                    crate::leanh::lean_inc(v___y_2049_);
                    crate::leanh::lean_inc_ref(v___y_2048_);
                    crate::leanh::lean_inc(v___y_2047_);
                    crate::leanh::lean_inc_ref(v___y_2046_);
                    crate::leanh::lean_inc(v___y_2045_);
                    crate::leanh::lean_inc_ref(v___y_2044_);
                    crate::leanh::lean_inc(v___y_2043_);
                    crate::leanh::lean_inc_ref(v___y_2042_);
                    v___x_2060_ = crate::leanh::lean_apply_10(
                        v___f_2041_,
                        v_a_2059_,
                        v___y_2042_,
                        v___y_2043_,
                        v___y_2044_,
                        v___y_2045_,
                        v___y_2046_,
                        v___y_2047_,
                        v___y_2048_,
                        v___y_2049_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2060_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_2041_);
                    v_a_2061_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                    v_isSharedCheck_2068_ = (!crate::leanh::lean_is_exclusive(v___x_2058_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2063_ = v___x_2058_;
                        v_isShared_2064_ = v_isSharedCheck_2068_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2061_);
                        crate::leanh::lean_dec(v___x_2058_);
                        v___x_2063_ = crate::leanh::lean_box(0);
                        v_isShared_2064_ = v_isSharedCheck_2068_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2064_ == 0 {
                    v___x_2066_ = v___x_2063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
                    v___x_2066_ = v_reuseFailAlloc_2067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2066_;
            }
            5 => {
                if v_isShared_2080_ == 0 {
                    v___x_2082_ = v___x_2079_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(
    mut v_ty_x3f_2085_: *mut crate::leanh::LeanObject,
    mut v___x_2086_: *mut crate::leanh::LeanObject,
    mut v___f_2087_: *mut crate::leanh::LeanObject,
    mut v___y_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
    mut v___y_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(
        v_ty_x3f_2085_,
        v___x_2086_,
        v___f_2087_,
        v___y_2088_,
        v___y_2089_,
        v___y_2090_,
        v___y_2091_,
        v___y_2092_,
        v___y_2093_,
        v___y_2094_,
        v___y_2095_,
    );
    crate::leanh::lean_dec(v___y_2095_);
    crate::leanh::lean_dec_ref(v___y_2094_);
    crate::leanh::lean_dec(v___y_2093_);
    crate::leanh::lean_dec_ref(v___y_2092_);
    crate::leanh::lean_dec(v___y_2091_);
    crate::leanh::lean_dec_ref(v___y_2090_);
    crate::leanh::lean_dec(v___y_2089_);
    crate::leanh::lean_dec_ref(v___y_2088_);
    return v_res_2097_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(
    mut v_x_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
    mut v_a_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_u_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2118_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_2119_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1;
                crate::leanh::lean_inc(v_x_2108_);
                v___x_2120_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2119_);
                if v___x_2120_ == 0 {
                    crate::leanh::lean_dec(v_x_2108_);
                    v___x_2121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_2121_;
                } else {
                    v___x_2122_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2123_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2122_);
                    v___x_2170_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2171_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2170_);
                    v___x_2172_ = l_Lean_Syntax_isNone(v___x_2171_);
                    if v___x_2172_ == 0 {
                        crate::leanh::lean_inc(v___x_2171_);
                        v___x_2173_ = l_Lean_Syntax_matchesNull(v___x_2171_, v___x_2170_);
                        if v___x_2173_ == 0 {
                            crate::leanh::lean_dec(v___x_2171_);
                            crate::leanh::lean_dec(v___x_2123_);
                            crate::leanh::lean_dec(v_x_2108_);
                            v___x_2174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_2174_;
                        } else {
                            v_ty_x3f_2175_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2122_);
                            crate::leanh::lean_dec(v___x_2171_);
                            v___x_2176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2176_, 0, v_ty_x3f_2175_);
                            v_ty_x3f_2125_ = v___x_2176_;
                            v___y_2126_ = v_a_2109_;
                            v___y_2127_ = v_a_2110_;
                            v___y_2128_ = v_a_2111_;
                            v___y_2129_ = v_a_2112_;
                            v___y_2130_ = v_a_2113_;
                            v___y_2131_ = v_a_2114_;
                            v___y_2132_ = v_a_2115_;
                            v___y_2133_ = v_a_2116_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2171_);
                        v___x_2177_ = crate::leanh::lean_box(0);
                        v_ty_x3f_2125_ = v___x_2177_;
                        v___y_2126_ = v_a_2109_;
                        v___y_2127_ = v_a_2110_;
                        v___y_2128_ = v_a_2111_;
                        v___y_2129_ = v_a_2112_;
                        v___y_2130_ = v_a_2113_;
                        v___y_2131_ = v_a_2114_;
                        v___y_2132_ = v_a_2115_;
                        v___y_2133_ = v_a_2116_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2134_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                    v___y_2126_,
                    v___y_2127_,
                    v___y_2128_,
                    v___y_2129_,
                    v___y_2130_,
                    v___y_2131_,
                    v___y_2132_,
                    v___y_2133_,
                );
                if crate::leanh::lean_obj_tag(v___x_2134_) == 0 {
                    v_a_2135_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                    crate::leanh::lean_inc(v_a_2135_);
                    crate::leanh::lean_dec_ref_known(v___x_2134_, 1);
                    v_snd_2136_ = crate::leanh::lean_ctor_get(v_a_2135_, 1);
                    v_fst_2137_ = crate::leanh::lean_ctor_get(v_a_2135_, 0);
                    v_isSharedCheck_2161_ = (!crate::leanh::lean_is_exclusive(v_a_2135_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2139_ = v_a_2135_;
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2136_);
                        crate::leanh::lean_inc(v_fst_2137_);
                        crate::leanh::lean_dec(v_a_2135_);
                        v___x_2139_ = crate::leanh::lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_x3f_2125_);
                    crate::leanh::lean_dec(v___x_2123_);
                    crate::leanh::lean_dec(v_x_2108_);
                    v_a_2162_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                    v_isSharedCheck_2169_ = (!crate::leanh::lean_is_exclusive(v___x_2134_)) as u8;
                    if v_isSharedCheck_2169_ == 0 {
                        v___x_2164_ = v___x_2134_;
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2162_);
                        crate::leanh::lean_dec(v___x_2134_);
                        v___x_2164_ = crate::leanh::lean_box(0);
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_u_2141_ = crate::leanh::lean_ctor_get(v_snd_2136_, 0);
                crate::leanh::lean_inc_n(v_u_2141_, 2);
                v_00_u03c3s_2142_ = crate::leanh::lean_ctor_get(v_snd_2136_, 1);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2142_);
                v_hyps_2143_ = crate::leanh::lean_ctor_get(v_snd_2136_, 2);
                crate::leanh::lean_inc_ref(v_hyps_2143_);
                v_target_2144_ = crate::leanh::lean_ctor_get(v_snd_2136_, 3);
                crate::leanh::lean_inc_ref(v_target_2144_);
                crate::leanh::lean_dec(v_snd_2136_);
                v___x_2145_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2146_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2145_);
                crate::leanh::lean_dec(v_x_2108_);
                v___x_2147_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                v___x_2148_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                v___x_2149_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                v___x_2150_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2;
                v___x_2151_ = crate::leanh::lean_box(0);
                if v_isShared_2140_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2139_, 1);
                    crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2139_, 0, v_u_2141_);
                    v___x_2153_ = v___x_2139_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_u_2141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2151_);
                    v___x_2153_ = v_reuseFailAlloc_2160_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2154_ = crate::leanh::lean_box((v___x_2120_) as usize);
                crate::leanh::lean_inc(v_fst_2137_);
                crate::leanh::lean_inc_ref(v___x_2153_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2142_);
                v___f_2155_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed
                        as *mut core::ffi::c_void,
                    23,
                    13,
                );
                crate::leanh::lean_closure_set(v___f_2155_, 0, v___x_2123_);
                crate::leanh::lean_closure_set(v___f_2155_, 1, v_00_u03c3s_2142_);
                crate::leanh::lean_closure_set(v___f_2155_, 2, v___x_2154_);
                crate::leanh::lean_closure_set(v___f_2155_, 3, v_u_2141_);
                crate::leanh::lean_closure_set(v___f_2155_, 4, v_hyps_2143_);
                crate::leanh::lean_closure_set(v___f_2155_, 5, v___x_2146_);
                crate::leanh::lean_closure_set(v___f_2155_, 6, v_target_2144_);
                crate::leanh::lean_closure_set(v___f_2155_, 7, v___x_2147_);
                crate::leanh::lean_closure_set(v___f_2155_, 8, v___x_2148_);
                crate::leanh::lean_closure_set(v___f_2155_, 9, v___x_2149_);
                crate::leanh::lean_closure_set(v___f_2155_, 10, v___x_2118_);
                crate::leanh::lean_closure_set(v___f_2155_, 11, v___x_2153_);
                crate::leanh::lean_closure_set(v___f_2155_, 12, v_fst_2137_);
                v___x_2156_ = l_Lean_mkConst(v___x_2150_, v___x_2153_);
                v___x_2157_ = l_Lean_Expr_app___override(v___x_2156_, v_00_u03c3s_2142_);
                v___y_2158_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                crate::leanh::lean_closure_set(v___y_2158_, 0, v_ty_x3f_2125_);
                crate::leanh::lean_closure_set(v___y_2158_, 1, v___x_2157_);
                crate::leanh::lean_closure_set(v___y_2158_, 2, v___f_2155_);
                v___x_2159_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_2137_, v___y_2158_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
                return v___x_2159_;
            }
            4 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(
    mut v_x_2178_: *mut crate::leanh::LeanObject,
    mut v_a_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(
        v_x_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_,
        v_a_2186_,
    );
    crate::leanh::lean_dec(v_a_2186_);
    crate::leanh::lean_dec_ref(v_a_2185_);
    crate::leanh::lean_dec(v_a_2184_);
    crate::leanh::lean_dec_ref(v_a_2183_);
    crate::leanh::lean_dec(v_a_2182_);
    crate::leanh::lean_dec_ref(v_a_2181_);
    crate::leanh::lean_dec(v_a_2180_);
    crate::leanh::lean_dec_ref(v_a_2179_);
    return v_res_2188_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2199_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1;
    v___x_2200_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1;
    v___x_2201_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2198_,
        v___x_2199_,
        v___x_2200_,
        v___x_2201_,
    );
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(
    mut v_a_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
    return v_res_2204_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(
    mut v___x_2206_: *mut crate::leanh::LeanObject,
    mut v_u_2207_: *mut crate::leanh::LeanObject,
    mut v___x_2208_: *mut crate::leanh::LeanObject,
    mut v___x_2209_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2210_: *mut crate::leanh::LeanObject,
    mut v___x_2211_: u8,
    mut v_hyps_2212_: *mut crate::leanh::LeanObject,
    mut v___x_2213_: *mut crate::leanh::LeanObject,
    mut v_target_2214_: *mut crate::leanh::LeanObject,
    mut v___x_2215_: *mut crate::leanh::LeanObject,
    mut v_fst_2216_: *mut crate::leanh::LeanObject,
    mut v_ty_x3f_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v_focusHyp_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_H_x27_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_a_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v_reuseFailAlloc_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___x_2206_) == 1 {
                    v_val_2227_ = crate::leanh::lean_ctor_get(v___x_2206_, 0);
                    v_isSharedCheck_2343_ = (!crate::leanh::lean_is_exclusive(v___x_2206_)) as u8;
                    if v_isSharedCheck_2343_ == 0 {
                        v___x_2229_ = v___x_2206_;
                        v_isShared_2230_ = v_isSharedCheck_2343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2227_);
                        crate::leanh::lean_dec(v___x_2206_);
                        v___x_2229_ = crate::leanh::lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2343_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_x3f_2217_);
                    crate::leanh::lean_dec(v_fst_2216_);
                    crate::leanh::lean_dec_ref(v___x_2215_);
                    crate::leanh::lean_dec_ref(v_target_2214_);
                    crate::leanh::lean_dec(v___x_2213_);
                    crate::leanh::lean_dec_ref(v_hyps_2212_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_dec(v___x_2208_);
                    crate::leanh::lean_dec(v_u_2207_);
                    crate::leanh::lean_dec(v___x_2206_);
                    v___x_2344_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6,
                    );
                    v___x_2345_ = l_Lean_MessageData_ofSyntax(v___x_2209_);
                    v___x_2346_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2346_, 0, v___x_2344_);
                    crate::leanh::lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                    v___x_2347_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8,
                    );
                    v___x_2348_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2346_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 1, v___x_2347_);
                    v___x_2349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_2348_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
                    return v___x_2349_;
                }
            }
            1 => {
                v_focusHyp_2231_ = crate::leanh::lean_ctor_get(v_val_2227_, 0);
                v_restHyps_2232_ = crate::leanh::lean_ctor_get(v_val_2227_, 1);
                v_proof_2233_ = crate::leanh::lean_ctor_get(v_val_2227_, 2);
                v_isSharedCheck_2342_ = (!crate::leanh::lean_is_exclusive(v_val_2227_)) as u8;
                if v_isSharedCheck_2342_ == 0 {
                    v___x_2235_ = v_val_2227_;
                    v_isShared_2236_ = v_isSharedCheck_2342_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_2233_);
                    crate::leanh::lean_inc(v_restHyps_2232_);
                    crate::leanh::lean_inc(v_focusHyp_2231_);
                    crate::leanh::lean_dec(v_val_2227_);
                    v___x_2235_ = crate::leanh::lean_box(0);
                    v_isShared_2236_ = v_isSharedCheck_2342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2237_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                v___x_2238_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                v___x_2239_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                v___x_2240_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2;
                v___x_2241_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_2207_);
                v___x_2242_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2242_, 0, v_u_2207_);
                crate::leanh::lean_ctor_set(v___x_2242_, 1, v___x_2241_);
                crate::leanh::lean_inc_ref(v___x_2242_);
                v___x_2308_ = l_Lean_mkConst(v___x_2240_, v___x_2242_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2309_ = l_Lean_Expr_app___override(v___x_2308_, v_00_u03c3s_2210_);
                if crate::leanh::lean_obj_tag(v_ty_x3f_2217_) == 1 {
                    v_val_2310_ = crate::leanh::lean_ctor_get(v_ty_x3f_2217_, 0);
                    v_isSharedCheck_2328_ =
                        (!crate::leanh::lean_is_exclusive(v_ty_x3f_2217_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2312_ = v_ty_x3f_2217_;
                        v_isShared_2313_ = v_isSharedCheck_2328_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2310_);
                        crate::leanh::lean_dec(v_ty_x3f_2217_);
                        v___x_2312_ = crate::leanh::lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2328_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_x3f_2217_);
                    v___x_2329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2309_);
                    v___x_2330_ = 0;
                    v___x_2331_ = crate::leanh::lean_box(0);
                    v___x_2332_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_2329_,
                        v___x_2330_,
                        v___x_2331_,
                        v___y_2222_,
                        v___y_2223_,
                        v___y_2224_,
                        v___y_2225_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2332_) == 0 {
                        v_a_2333_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                        crate::leanh::lean_inc(v_a_2333_);
                        crate::leanh::lean_dec_ref_known(v___x_2332_, 1);
                        v_H_x27_2244_ = v_a_2333_;
                        v___y_2245_ = v___y_2218_;
                        v___y_2246_ = v___y_2219_;
                        v___y_2247_ = v___y_2220_;
                        v___y_2248_ = v___y_2221_;
                        v___y_2249_ = v___y_2222_;
                        v___y_2250_ = v___y_2223_;
                        v___y_2251_ = v___y_2224_;
                        v___y_2252_ = v___y_2225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2242_, 2);
                        crate::leanh::lean_del_object(v___x_2235_);
                        crate::leanh::lean_dec_ref(v_proof_2233_);
                        crate::leanh::lean_dec_ref(v_restHyps_2232_);
                        crate::leanh::lean_dec_ref(v_focusHyp_2231_);
                        crate::leanh::lean_del_object(v___x_2229_);
                        crate::leanh::lean_dec(v_fst_2216_);
                        crate::leanh::lean_dec_ref(v___x_2215_);
                        crate::leanh::lean_dec_ref(v_target_2214_);
                        crate::leanh::lean_dec(v___x_2213_);
                        crate::leanh::lean_dec_ref(v_hyps_2212_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                        crate::leanh::lean_dec(v___x_2209_);
                        crate::leanh::lean_dec(v___x_2208_);
                        crate::leanh::lean_dec(v_u_2207_);
                        v_a_2334_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                        v_isSharedCheck_2341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2332_)) as u8;
                        if v_isSharedCheck_2341_ == 0 {
                            v___x_2336_ = v___x_2332_;
                            v_isShared_2337_ = v_isSharedCheck_2341_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2334_);
                            crate::leanh::lean_dec(v___x_2332_);
                            v___x_2336_ = crate::leanh::lean_box(0);
                            v_isShared_2337_ = v_isSharedCheck_2341_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2253_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_2252_);
                v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                crate::leanh::lean_inc(v_a_2254_);
                crate::leanh::lean_dec_ref(v___x_2253_);
                crate::leanh::lean_inc_ref(v_H_x27_2244_);
                if v_isShared_2236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2235_, 2, v_H_x27_2244_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 1, v_a_2254_);
                    crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2208_);
                    v___x_2256_ = v___x_2235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_H_x27_2244_);
                    v___x_2256_ = v_reuseFailAlloc_2307_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_2256_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2257_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_2209_,
                    v_00_u03c3s_2210_,
                    v___x_2256_,
                    v___x_2211_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if crate::leanh::lean_obj_tag(v___x_2257_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2257_, 1);
                    crate::leanh::lean_inc_ref(v_hyps_2212_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_inc(v_u_2207_);
                    v___x_2258_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2258_, 0, v_u_2207_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 1, v_00_u03c3s_2210_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 2, v_hyps_2212_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 3, v_H_x27_2244_);
                    v___x_2259_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2258_);
                    if v_isShared_2230_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2229_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2306_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2256_);
                    crate::leanh::lean_dec_ref(v_H_x27_2244_);
                    crate::leanh::lean_dec_ref_known(v___x_2242_, 2);
                    crate::leanh::lean_dec_ref(v_proof_2233_);
                    crate::leanh::lean_dec_ref(v_restHyps_2232_);
                    crate::leanh::lean_dec_ref(v_focusHyp_2231_);
                    crate::leanh::lean_del_object(v___x_2229_);
                    crate::leanh::lean_dec(v_fst_2216_);
                    crate::leanh::lean_dec_ref(v___x_2215_);
                    crate::leanh::lean_dec_ref(v_target_2214_);
                    crate::leanh::lean_dec(v___x_2213_);
                    crate::leanh::lean_dec_ref(v_hyps_2212_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_dec(v_u_2207_);
                    return v___x_2257_;
                }
            }
            5 => {
                v___x_2262_ = 0;
                v___x_2263_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
                    v___x_2213_,
                    v___x_2261_,
                    v___x_2262_,
                    v___y_2245_,
                    v___y_2246_,
                    v___y_2247_,
                    v___y_2248_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if crate::leanh::lean_obj_tag(v___x_2263_) == 0 {
                    v_a_2264_ = crate::leanh::lean_ctor_get(v___x_2263_, 0);
                    crate::leanh::lean_inc(v_a_2264_);
                    crate::leanh::lean_dec_ref_known(v___x_2263_, 1);
                    v___x_2265_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2256_);
                    crate::leanh::lean_inc_ref(v___x_2265_);
                    crate::leanh::lean_inc_ref(v_restHyps_2232_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_inc(v_u_2207_);
                    v___x_2266_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                        v_u_2207_,
                        v_00_u03c3s_2210_,
                        v_restHyps_2232_,
                        v___x_2265_,
                    );
                    v_fst_2267_ = crate::leanh::lean_ctor_get(v___x_2266_, 0);
                    v_snd_2268_ = crate::leanh::lean_ctor_get(v___x_2266_, 1);
                    v_isSharedCheck_2297_ = (!crate::leanh::lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v___x_2270_ = v___x_2266_;
                        v_isShared_2271_ = v_isSharedCheck_2297_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2268_);
                        crate::leanh::lean_inc(v_fst_2267_);
                        crate::leanh::lean_dec(v___x_2266_);
                        v___x_2270_ = crate::leanh::lean_box(0);
                        v_isShared_2271_ = v_isSharedCheck_2297_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2256_);
                    crate::leanh::lean_dec_ref_known(v___x_2242_, 2);
                    crate::leanh::lean_dec_ref(v_proof_2233_);
                    crate::leanh::lean_dec_ref(v_restHyps_2232_);
                    crate::leanh::lean_dec_ref(v_focusHyp_2231_);
                    crate::leanh::lean_dec(v_fst_2216_);
                    crate::leanh::lean_dec_ref(v___x_2215_);
                    crate::leanh::lean_dec_ref(v_target_2214_);
                    crate::leanh::lean_dec_ref(v_hyps_2212_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_dec(v_u_2207_);
                    v_a_2298_ = crate::leanh::lean_ctor_get(v___x_2263_, 0);
                    v_isSharedCheck_2305_ = (!crate::leanh::lean_is_exclusive(v___x_2263_)) as u8;
                    if v_isSharedCheck_2305_ == 0 {
                        v___x_2300_ = v___x_2263_;
                        v_isShared_2301_ = v_isSharedCheck_2305_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2298_);
                        crate::leanh::lean_dec(v___x_2263_);
                        v___x_2300_ = crate::leanh::lean_box(0);
                        v_isShared_2301_ = v_isSharedCheck_2305_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_target_2214_);
                crate::leanh::lean_inc(v_fst_2267_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2272_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2272_, 0, v_u_2207_);
                crate::leanh::lean_ctor_set(v___x_2272_, 1, v_00_u03c3s_2210_);
                crate::leanh::lean_ctor_set(v___x_2272_, 2, v_fst_2267_);
                crate::leanh::lean_ctor_set(v___x_2272_, 3, v_target_2214_);
                v___x_2273_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2272_);
                v___x_2274_ = crate::leanh::lean_box(0);
                v___x_2275_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_2273_,
                    v___x_2274_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if crate::leanh::lean_obj_tag(v___x_2275_) == 0 {
                    v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                    crate::leanh::lean_inc_n(v_a_2276_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2275_, 1);
                    v___x_2277_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                    v___x_2278_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0;
                    v___x_2279_ = l_Lean_Name_mkStr6(
                        v___x_2237_,
                        v___x_2238_,
                        v___x_2239_,
                        v___x_2215_,
                        v___x_2277_,
                        v___x_2278_,
                    );
                    v___x_2280_ = l_Lean_mkConst(v___x_2279_, v___x_2242_);
                    v___x_2281_ = l_Lean_mkApp10(
                        v___x_2280_,
                        v_00_u03c3s_2210_,
                        v_restHyps_2232_,
                        v_focusHyp_2231_,
                        v___x_2265_,
                        v_hyps_2212_,
                        v_fst_2267_,
                        v_target_2214_,
                        v_proof_2233_,
                        v_snd_2268_,
                        v_a_2264_,
                    );
                    v___x_2282_ = l_Lean_Expr_app___override(v___x_2281_, v_a_2276_);
                    v___x_2283_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_2216_, v___x_2282_, v___y_2250_);
                    crate::leanh::lean_dec_ref(v___x_2283_);
                    v___x_2284_ = l_Lean_Expr_mvarId_x21(v_a_2276_);
                    crate::leanh::lean_dec(v_a_2276_);
                    if v_isShared_2271_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2270_, 1);
                        crate::leanh::lean_ctor_set(v___x_2270_, 1, v___x_2241_);
                        crate::leanh::lean_ctor_set(v___x_2270_, 0, v___x_2284_);
                        v___x_2286_ = v___x_2270_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2288_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2284_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2241_);
                        v___x_2286_ = v_reuseFailAlloc_2288_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2270_);
                    crate::leanh::lean_dec(v_snd_2268_);
                    crate::leanh::lean_dec(v_fst_2267_);
                    crate::leanh::lean_dec_ref(v___x_2265_);
                    crate::leanh::lean_dec(v_a_2264_);
                    crate::leanh::lean_dec_ref_known(v___x_2242_, 2);
                    crate::leanh::lean_dec_ref(v_proof_2233_);
                    crate::leanh::lean_dec_ref(v_restHyps_2232_);
                    crate::leanh::lean_dec_ref(v_focusHyp_2231_);
                    crate::leanh::lean_dec(v_fst_2216_);
                    crate::leanh::lean_dec_ref(v___x_2215_);
                    crate::leanh::lean_dec_ref(v_target_2214_);
                    crate::leanh::lean_dec_ref(v_hyps_2212_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                    v_a_2289_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                    v_isSharedCheck_2296_ = (!crate::leanh::lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2291_ = v___x_2275_;
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2289_);
                        crate::leanh::lean_dec(v___x_2275_);
                        v___x_2291_ = crate::leanh::lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2287_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_2286_,
                    v___y_2246_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                return v___x_2287_;
            }
            8 => {
                if v_isShared_2292_ == 0 {
                    v___x_2294_ = v___x_2291_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
                    v___x_2294_ = v_reuseFailAlloc_2295_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2294_;
            }
            10 => {
                if v_isShared_2301_ == 0 {
                    v___x_2303_ = v___x_2300_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
                    v___x_2303_ = v_reuseFailAlloc_2304_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2303_;
            }
            12 => {
                if v_isShared_2313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2309_);
                    v___x_2315_ = v___x_2312_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2309_);
                    v___x_2315_ = v_reuseFailAlloc_2327_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2316_ = 0;
                v___x_2317_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_2310_,
                    v___x_2315_,
                    v___x_2316_,
                    v___y_2218_,
                    v___y_2219_,
                    v___y_2220_,
                    v___y_2221_,
                    v___y_2222_,
                    v___y_2223_,
                    v___y_2224_,
                    v___y_2225_,
                );
                if crate::leanh::lean_obj_tag(v___x_2317_) == 0 {
                    v_a_2318_ = crate::leanh::lean_ctor_get(v___x_2317_, 0);
                    crate::leanh::lean_inc(v_a_2318_);
                    crate::leanh::lean_dec_ref_known(v___x_2317_, 1);
                    v_H_x27_2244_ = v_a_2318_;
                    v___y_2245_ = v___y_2218_;
                    v___y_2246_ = v___y_2219_;
                    v___y_2247_ = v___y_2220_;
                    v___y_2248_ = v___y_2221_;
                    v___y_2249_ = v___y_2222_;
                    v___y_2250_ = v___y_2223_;
                    v___y_2251_ = v___y_2224_;
                    v___y_2252_ = v___y_2225_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2242_, 2);
                    crate::leanh::lean_del_object(v___x_2235_);
                    crate::leanh::lean_dec_ref(v_proof_2233_);
                    crate::leanh::lean_dec_ref(v_restHyps_2232_);
                    crate::leanh::lean_dec_ref(v_focusHyp_2231_);
                    crate::leanh::lean_del_object(v___x_2229_);
                    crate::leanh::lean_dec(v_fst_2216_);
                    crate::leanh::lean_dec_ref(v___x_2215_);
                    crate::leanh::lean_dec_ref(v_target_2214_);
                    crate::leanh::lean_dec(v___x_2213_);
                    crate::leanh::lean_dec_ref(v_hyps_2212_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_2210_);
                    crate::leanh::lean_dec(v___x_2209_);
                    crate::leanh::lean_dec(v___x_2208_);
                    crate::leanh::lean_dec(v_u_2207_);
                    v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2317_, 0);
                    v_isSharedCheck_2326_ = (!crate::leanh::lean_is_exclusive(v___x_2317_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___x_2317_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2319_);
                        crate::leanh::lean_dec(v___x_2317_);
                        v___x_2321_ = crate::leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2322_ == 0 {
                    v___x_2324_ = v___x_2321_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2324_;
            }
            16 => {
                if v_isShared_2337_ == 0 {
                    v___x_2339_ = v___x_2336_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2350_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_2351_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2352_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2353_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_00_u03c3s_2354_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2355_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_hyps_2356_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2357_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_target_2358_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2359_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_fst_2360_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_ty_x3f_2361_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2362_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2363_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2364_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2365_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2366_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2367_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2368_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2369_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2370_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_3617__boxed_2371_: u8 = 0;
    let mut v_res_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3617__boxed_2371_ = (crate::leanh::lean_unbox(v___x_2355_) as u8);
    v_res_2372_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(
        v___x_2350_,
        v_u_2351_,
        v___x_2352_,
        v___x_2353_,
        v_00_u03c3s_2354_,
        v___x_3617__boxed_2371_,
        v_hyps_2356_,
        v___x_2357_,
        v_target_2358_,
        v___x_2359_,
        v_fst_2360_,
        v_ty_x3f_2361_,
        v___y_2362_,
        v___y_2363_,
        v___y_2364_,
        v___y_2365_,
        v___y_2366_,
        v___y_2367_,
        v___y_2368_,
        v___y_2369_,
    );
    crate::leanh::lean_dec(v___y_2369_);
    crate::leanh::lean_dec_ref(v___y_2368_);
    crate::leanh::lean_dec(v___y_2367_);
    crate::leanh::lean_dec_ref(v___y_2366_);
    crate::leanh::lean_dec(v___y_2365_);
    crate::leanh::lean_dec_ref(v___y_2364_);
    crate::leanh::lean_dec(v___y_2363_);
    crate::leanh::lean_dec_ref(v___y_2362_);
    return v_res_2372_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(
    mut v_x_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2389_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_2390_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1;
                crate::leanh::lean_inc(v_x_2379_);
                v___x_2391_ = l_Lean_Syntax_isOfKind(v_x_2379_, v___x_2390_);
                if v___x_2391_ == 0 {
                    crate::leanh::lean_dec(v_x_2379_);
                    v___x_2392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_2392_;
                } else {
                    v___x_2393_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2394_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2393_);
                    v___x_2428_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2429_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2428_);
                    v___x_2430_ = l_Lean_Syntax_isNone(v___x_2429_);
                    if v___x_2430_ == 0 {
                        crate::leanh::lean_inc(v___x_2429_);
                        v___x_2431_ = l_Lean_Syntax_matchesNull(v___x_2429_, v___x_2428_);
                        if v___x_2431_ == 0 {
                            crate::leanh::lean_dec(v___x_2429_);
                            crate::leanh::lean_dec(v___x_2394_);
                            crate::leanh::lean_dec(v_x_2379_);
                            v___x_2432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_2432_;
                        } else {
                            v_ty_x3f_2433_ = l_Lean_Syntax_getArg(v___x_2429_, v___x_2393_);
                            crate::leanh::lean_dec(v___x_2429_);
                            v___x_2434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2434_, 0, v_ty_x3f_2433_);
                            v_ty_x3f_2396_ = v___x_2434_;
                            v___y_2397_ = v_a_2380_;
                            v___y_2398_ = v_a_2381_;
                            v___y_2399_ = v_a_2382_;
                            v___y_2400_ = v_a_2383_;
                            v___y_2401_ = v_a_2384_;
                            v___y_2402_ = v_a_2385_;
                            v___y_2403_ = v_a_2386_;
                            v___y_2404_ = v_a_2387_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2429_);
                        v___x_2435_ = crate::leanh::lean_box(0);
                        v_ty_x3f_2396_ = v___x_2435_;
                        v___y_2397_ = v_a_2380_;
                        v___y_2398_ = v_a_2381_;
                        v___y_2399_ = v_a_2382_;
                        v___y_2400_ = v_a_2383_;
                        v___y_2401_ = v_a_2384_;
                        v___y_2402_ = v_a_2385_;
                        v___y_2403_ = v_a_2386_;
                        v___y_2404_ = v_a_2387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2405_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                    v___y_2397_,
                    v___y_2398_,
                    v___y_2399_,
                    v___y_2400_,
                    v___y_2401_,
                    v___y_2402_,
                    v___y_2403_,
                    v___y_2404_,
                );
                if crate::leanh::lean_obj_tag(v___x_2405_) == 0 {
                    v_a_2406_ = crate::leanh::lean_ctor_get(v___x_2405_, 0);
                    crate::leanh::lean_inc(v_a_2406_);
                    crate::leanh::lean_dec_ref_known(v___x_2405_, 1);
                    v_snd_2407_ = crate::leanh::lean_ctor_get(v_a_2406_, 1);
                    crate::leanh::lean_inc(v_snd_2407_);
                    v_fst_2408_ = crate::leanh::lean_ctor_get(v_a_2406_, 0);
                    crate::leanh::lean_inc_n(v_fst_2408_, 2);
                    crate::leanh::lean_dec(v_a_2406_);
                    v_u_2409_ = crate::leanh::lean_ctor_get(v_snd_2407_, 0);
                    crate::leanh::lean_inc(v_u_2409_);
                    v_00_u03c3s_2410_ = crate::leanh::lean_ctor_get(v_snd_2407_, 1);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_2410_);
                    v_hyps_2411_ = crate::leanh::lean_ctor_get(v_snd_2407_, 2);
                    crate::leanh::lean_inc_ref(v_hyps_2411_);
                    v_target_2412_ = crate::leanh::lean_ctor_get(v_snd_2407_, 3);
                    crate::leanh::lean_inc_ref(v_target_2412_);
                    v___x_2413_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2414_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2413_);
                    crate::leanh::lean_dec(v_x_2379_);
                    v___x_2415_ = l_Lean_Syntax_getId(v___x_2394_);
                    v___x_2416_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_2407_, v___x_2415_);
                    v___x_2417_ = crate::leanh::lean_box((v___x_2391_) as usize);
                    v___y_2418_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed
                            as *mut core::ffi::c_void,
                        21,
                        12,
                    );
                    crate::leanh::lean_closure_set(v___y_2418_, 0, v___x_2416_);
                    crate::leanh::lean_closure_set(v___y_2418_, 1, v_u_2409_);
                    crate::leanh::lean_closure_set(v___y_2418_, 2, v___x_2415_);
                    crate::leanh::lean_closure_set(v___y_2418_, 3, v___x_2394_);
                    crate::leanh::lean_closure_set(v___y_2418_, 4, v_00_u03c3s_2410_);
                    crate::leanh::lean_closure_set(v___y_2418_, 5, v___x_2417_);
                    crate::leanh::lean_closure_set(v___y_2418_, 6, v_hyps_2411_);
                    crate::leanh::lean_closure_set(v___y_2418_, 7, v___x_2414_);
                    crate::leanh::lean_closure_set(v___y_2418_, 8, v_target_2412_);
                    crate::leanh::lean_closure_set(v___y_2418_, 9, v___x_2389_);
                    crate::leanh::lean_closure_set(v___y_2418_, 10, v_fst_2408_);
                    crate::leanh::lean_closure_set(v___y_2418_, 11, v_ty_x3f_2396_);
                    v___x_2419_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_2408_, v___y_2418_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
                    return v___x_2419_;
                } else {
                    crate::leanh::lean_dec(v_ty_x3f_2396_);
                    crate::leanh::lean_dec(v___x_2394_);
                    crate::leanh::lean_dec(v_x_2379_);
                    v_a_2420_ = crate::leanh::lean_ctor_get(v___x_2405_, 0);
                    v_isSharedCheck_2427_ = (!crate::leanh::lean_is_exclusive(v___x_2405_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2422_ = v___x_2405_;
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2420_);
                        crate::leanh::lean_dec(v___x_2405_);
                        v___x_2422_ = crate::leanh::lean_box(0);
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2423_ == 0 {
                    v___x_2425_ = v___x_2422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(
    mut v_x_2436_: *mut crate::leanh::LeanObject,
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(
        v_x_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_,
        v_a_2444_,
    );
    crate::leanh::lean_dec(v_a_2444_);
    crate::leanh::lean_dec_ref(v_a_2443_);
    crate::leanh::lean_dec(v_a_2442_);
    crate::leanh::lean_dec_ref(v_a_2441_);
    crate::leanh::lean_dec(v_a_2440_);
    crate::leanh::lean_dec_ref(v_a_2439_);
    crate::leanh::lean_dec(v_a_2438_);
    crate::leanh::lean_dec_ref(v_a_2437_);
    return v_res_2446_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2457_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1;
    v___x_2458_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1;
    v___x_2459_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2456_,
        v___x_2457_,
        v___x_2458_,
        v___x_2459_,
    );
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
    return v_res_2462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Have(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
}
