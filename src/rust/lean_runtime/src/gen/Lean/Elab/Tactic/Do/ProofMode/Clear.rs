// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Clear
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Focus
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr6, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp7, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value:
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
    m_data: [67, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value:
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
    m_data: [99, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        110, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value:
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
    m_data: [109, 99, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12602713191225532779 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 67, 108, 101, 97, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value) as *mut crate::leanh::LeanObject,17134313240879321948 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = crate::leanh::lean_box(0);
    v___x_672_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_673_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_673_, 0, v___x_672_);
    crate::leanh::lean_ctor_set(v___x_673_, 1, v___x_671_);
    return v___x_673_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0);
    v___x_676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___boxed(
    mut v___y_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
    return v_res_678_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(
    mut v_00_u03b1_679_: *mut crate::leanh::LeanObject,
    mut v___y_680_: *mut crate::leanh::LeanObject,
    mut v___y_681_: *mut crate::leanh::LeanObject,
    mut v___y_682_: *mut crate::leanh::LeanObject,
    mut v___y_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
    return v___x_689_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___boxed(
    mut v_00_u03b1_690_: *mut crate::leanh::LeanObject,
    mut v___y_691_: *mut crate::leanh::LeanObject,
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
    mut v___y_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
    mut v___y_697_: *mut crate::leanh::LeanObject,
    mut v___y_698_: *mut crate::leanh::LeanObject,
    mut v___y_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(v_00_u03b1_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
    crate::leanh::lean_dec(v___y_698_);
    crate::leanh::lean_dec_ref(v___y_697_);
    crate::leanh::lean_dec(v___y_696_);
    crate::leanh::lean_dec_ref(v___y_695_);
    crate::leanh::lean_dec(v___y_694_);
    crate::leanh::lean_dec_ref(v___y_693_);
    crate::leanh::lean_dec(v___y_692_);
    crate::leanh::lean_dec_ref(v___y_691_);
    return v_res_700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
    mut v_e_701_: *mut crate::leanh::LeanObject,
    mut v___y_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_unused_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_704_ = l_Lean_Expr_hasMVar(v_e_701_);
                if v___x_704_ == 0 {
                    v___x_705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_705_, 0, v_e_701_);
                    return v___x_705_;
                } else {
                    v___x_706_ = lean_st_ref_get(v___y_702_);
                    v_mctx_707_ = crate::leanh::lean_ctor_get(v___x_706_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_707_);
                    crate::leanh::lean_dec(v___x_706_);
                    v___x_708_ = l_Lean_instantiateMVarsCore(v_mctx_707_, v_e_701_);
                    v_fst_709_ = crate::leanh::lean_ctor_get(v___x_708_, 0);
                    crate::leanh::lean_inc(v_fst_709_);
                    v_snd_710_ = crate::leanh::lean_ctor_get(v___x_708_, 1);
                    crate::leanh::lean_inc(v_snd_710_);
                    crate::leanh::lean_dec_ref(v___x_708_);
                    v___x_711_ = lean_st_ref_take(v___y_702_);
                    v_cache_712_ = crate::leanh::lean_ctor_get(v___x_711_, 1);
                    v_zetaDeltaFVarIds_713_ = crate::leanh::lean_ctor_get(v___x_711_, 2);
                    v_postponed_714_ = crate::leanh::lean_ctor_get(v___x_711_, 3);
                    v_diag_715_ = crate::leanh::lean_ctor_get(v___x_711_, 4);
                    v_isSharedCheck_724_ = (!crate::leanh::lean_is_exclusive(v___x_711_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v_unused_725_ = crate::leanh::lean_ctor_get(v___x_711_, 0);
                        crate::leanh::lean_dec(v_unused_725_);
                        v___x_717_ = v___x_711_;
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_715_);
                        crate::leanh::lean_inc(v_postponed_714_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_713_);
                        crate::leanh::lean_inc(v_cache_712_);
                        crate::leanh::lean_dec(v___x_711_);
                        v___x_717_ = crate::leanh::lean_box(0);
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_717_, 0, v_snd_710_);
                    v___x_720_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 1, v_cache_712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_715_);
                    v___x_720_ = v_reuseFailAlloc_723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_721_ = lean_st_ref_set(v___y_702_, v___x_720_);
                v___x_722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_722_, 0, v_fst_709_);
                return v___x_722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg___boxed(
    mut v_e_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
            v_e_726_, v___y_727_,
        );
    crate::leanh::lean_dec(v___y_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(
    mut v_e_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
            v_e_730_, v___y_736_,
        );
    return v___x_740_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___boxed(
    mut v_e_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(
        v_e_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_,
        v___y_748_, v___y_749_,
    );
    crate::leanh::lean_dec(v___y_749_);
    crate::leanh::lean_dec_ref(v___y_748_);
    crate::leanh::lean_dec(v___y_747_);
    crate::leanh::lean_dec_ref(v___y_746_);
    crate::leanh::lean_dec(v___y_745_);
    crate::leanh::lean_dec_ref(v___y_744_);
    crate::leanh::lean_dec(v___y_743_);
    crate::leanh::lean_dec_ref(v___y_742_);
    return v_res_751_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(
    mut v_x_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v___y_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_756_);
    crate::leanh::lean_inc_ref(v___y_755_);
    crate::leanh::lean_inc(v___y_754_);
    crate::leanh::lean_inc_ref(v___y_753_);
    v___x_762_ = crate::leanh::lean_apply_9(
        v_x_752_,
        v___y_753_,
        v___y_754_,
        v___y_755_,
        v___y_756_,
        v___y_757_,
        v___y_758_,
        v___y_759_,
        v___y_760_,
        crate::leanh::lean_box(0),
    );
    return v___x_762_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed(
    mut v_x_763_: *mut crate::leanh::LeanObject,
    mut v___y_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
    crate::leanh::lean_dec(v___y_767_);
    crate::leanh::lean_dec_ref(v___y_766_);
    crate::leanh::lean_dec(v___y_765_);
    crate::leanh::lean_dec_ref(v___y_764_);
    return v_res_773_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(
    mut v_mvarId_774_: *mut crate::leanh::LeanObject,
    mut v_x_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
    mut v___y_777_: *mut crate::leanh::LeanObject,
    mut v___y_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
    mut v___y_780_: *mut crate::leanh::LeanObject,
    mut v___y_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_779_);
                crate::leanh::lean_inc_ref(v___y_778_);
                crate::leanh::lean_inc(v___y_777_);
                crate::leanh::lean_inc_ref(v___y_776_);
                v___f_785_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_785_, 0, v_x_775_);
                crate::leanh::lean_closure_set(v___f_785_, 1, v___y_776_);
                crate::leanh::lean_closure_set(v___f_785_, 2, v___y_777_);
                crate::leanh::lean_closure_set(v___f_785_, 3, v___y_778_);
                crate::leanh::lean_closure_set(v___f_785_, 4, v___y_779_);
                v___x_786_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_774_,
                    v___f_785_,
                    v___y_780_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                );
                if crate::leanh::lean_obj_tag(v___x_786_) == 0 {
                    return v___x_786_;
                } else {
                    v_a_787_ = crate::leanh::lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_794_ = (!crate::leanh::lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v___x_789_ = v___x_786_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_787_);
                        crate::leanh::lean_dec(v___x_786_);
                        v___x_789_ = crate::leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_790_ == 0 {
                    v___x_792_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
                    v___x_792_ = v_reuseFailAlloc_793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___boxed(
    mut v_mvarId_795_: *mut crate::leanh::LeanObject,
    mut v_x_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
    mut v___y_798_: *mut crate::leanh::LeanObject,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
    mut v___y_802_: *mut crate::leanh::LeanObject,
    mut v___y_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_795_, v_x_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
    crate::leanh::lean_dec(v___y_804_);
    crate::leanh::lean_dec_ref(v___y_803_);
    crate::leanh::lean_dec(v___y_802_);
    crate::leanh::lean_dec_ref(v___y_801_);
    crate::leanh::lean_dec(v___y_800_);
    crate::leanh::lean_dec_ref(v___y_799_);
    crate::leanh::lean_dec(v___y_798_);
    crate::leanh::lean_dec_ref(v___y_797_);
    return v_res_806_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(
    mut v_00_u03b1_807_: *mut crate::leanh::LeanObject,
    mut v_mvarId_808_: *mut crate::leanh::LeanObject,
    mut v_x_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
    mut v___y_814_: *mut crate::leanh::LeanObject,
    mut v___y_815_: *mut crate::leanh::LeanObject,
    mut v___y_816_: *mut crate::leanh::LeanObject,
    mut v___y_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_808_, v_x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
    return v___x_819_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___boxed(
    mut v_00_u03b1_820_: *mut crate::leanh::LeanObject,
    mut v_mvarId_821_: *mut crate::leanh::LeanObject,
    mut v_x_822_: *mut crate::leanh::LeanObject,
    mut v___y_823_: *mut crate::leanh::LeanObject,
    mut v___y_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
    mut v___y_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
    mut v___y_829_: *mut crate::leanh::LeanObject,
    mut v___y_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(
            v_00_u03b1_820_,
            v_mvarId_821_,
            v_x_822_,
            v___y_823_,
            v___y_824_,
            v___y_825_,
            v___y_826_,
            v___y_827_,
            v___y_828_,
            v___y_829_,
            v___y_830_,
        );
    crate::leanh::lean_dec(v___y_830_);
    crate::leanh::lean_dec_ref(v___y_829_);
    crate::leanh::lean_dec(v___y_828_);
    crate::leanh::lean_dec_ref(v___y_827_);
    crate::leanh::lean_dec(v___y_826_);
    crate::leanh::lean_dec_ref(v___y_825_);
    crate::leanh::lean_dec(v___y_824_);
    crate::leanh::lean_dec_ref(v___y_823_);
    return v_res_832_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(
    mut v_x_833_: *mut crate::leanh::LeanObject,
    mut v_x_834_: *mut crate::leanh::LeanObject,
    mut v_x_835_: *mut crate::leanh::LeanObject,
    mut v_x_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_837_ = crate::leanh::lean_ctor_get(v_x_833_, 0);
                v_vs_838_ = crate::leanh::lean_ctor_get(v_x_833_, 1);
                v_isSharedCheck_862_ = (!crate::leanh::lean_is_exclusive(v_x_833_)) as u8;
                if v_isSharedCheck_862_ == 0 {
                    v___x_840_ = v_x_833_;
                    v_isShared_841_ = v_isSharedCheck_862_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_838_);
                    crate::leanh::lean_inc(v_ks_837_);
                    crate::leanh::lean_dec(v_x_833_);
                    v___x_840_ = crate::leanh::lean_box(0);
                    v_isShared_841_ = v_isSharedCheck_862_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_842_ = lean_array_get_size(v_ks_837_);
                v___x_843_ = lean_nat_dec_lt(v_x_834_, v___x_842_);
                if v___x_843_ == 0 {
                    crate::leanh::lean_dec(v_x_834_);
                    v___x_844_ = lean_array_push(v_ks_837_, v_x_835_);
                    v___x_845_ = lean_array_push(v_vs_838_, v_x_836_);
                    if v_isShared_841_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_840_, 1, v___x_845_);
                        crate::leanh::lean_ctor_set(v___x_840_, 0, v___x_844_);
                        v___x_847_ = v___x_840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
                        v___x_847_ = v_reuseFailAlloc_848_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_849_ = lean_array_fget_borrowed(v_ks_837_, v_x_834_);
                    v___x_850_ = l_Lean_instBEqMVarId_beq(v_x_835_, v_k_x27_849_);
                    if v___x_850_ == 0 {
                        if v_isShared_841_ == 0 {
                            v___x_852_ = v___x_840_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_856_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_856_, 0, v_ks_837_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_856_, 1, v_vs_838_);
                            v___x_852_ = v_reuseFailAlloc_856_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_857_ = lean_array_fset(v_ks_837_, v_x_834_, v_x_835_);
                        v___x_858_ = lean_array_fset(v_vs_838_, v_x_834_, v_x_836_);
                        crate::leanh::lean_dec(v_x_834_);
                        if v_isShared_841_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_840_, 1, v___x_858_);
                            crate::leanh::lean_ctor_set(v___x_840_, 0, v___x_857_);
                            v___x_860_ = v___x_840_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_857_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
                            v___x_860_ = v_reuseFailAlloc_861_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_847_;
            }
            3 => {
                v___x_853_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_854_ = lean_nat_add(v_x_834_, v___x_853_);
                crate::leanh::lean_dec(v_x_834_);
                v_x_833_ = v___x_852_;
                v_x_834_ = v___x_854_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_n_863_: *mut crate::leanh::LeanObject,
    mut v_k_864_: *mut crate::leanh::LeanObject,
    mut v_v_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_867_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_863_, v___x_866_, v_k_864_, v_v_865_);
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_868_: usize = 0;
    let mut v___x_869_: usize = 0;
    let mut v___x_870_: usize = 0;
    v___x_868_ = 5usize;
    v___x_869_ = 1usize;
    v___x_870_ = lean_usize_shift_left(v___x_869_, v___x_868_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    let mut v___x_873_: usize = 0;
    v___x_871_ = 1usize;
    v___x_872_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_873_ = lean_usize_sub(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_874_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(
    mut v_x_875_: *mut crate::leanh::LeanObject,
    mut v_x_876_: usize,
    mut v_x_877_: usize,
    mut v_x_878_: *mut crate::leanh::LeanObject,
    mut v_x_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: usize = 0;
    let mut v___x_882_: usize = 0;
    let mut v___x_883_: usize = 0;
    let mut v___x_884_: usize = 0;
    let mut v_j_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v_v_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_904_: u8 = 0;
    let mut v___x_905_: u8 = 0;
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_node_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_924_: u8 = 0;
    let mut v_unused_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_935_: u8 = 0;
    let mut v_ks_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: usize = 0;
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v_reuseFailAlloc_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_875_) == 0 {
                    v_es_880_ = crate::leanh::lean_ctor_get(v_x_875_, 0);
                    v___x_881_ = 5usize;
                    v___x_882_ = 1usize;
                    v___x_883_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_884_ = lean_usize_land(v_x_876_, v___x_883_);
                    v_j_885_ = lean_usize_to_nat(v___x_884_);
                    v___x_886_ = lean_array_get_size(v_es_880_);
                    v___x_887_ = lean_nat_dec_lt(v_j_885_, v___x_886_);
                    if v___x_887_ == 0 {
                        crate::leanh::lean_dec(v_j_885_);
                        crate::leanh::lean_dec(v_x_879_);
                        crate::leanh::lean_dec(v_x_878_);
                        return v_x_875_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_880_);
                        v_isSharedCheck_924_ = (!crate::leanh::lean_is_exclusive(v_x_875_)) as u8;
                        if v_isSharedCheck_924_ == 0 {
                            v_unused_925_ = crate::leanh::lean_ctor_get(v_x_875_, 0);
                            crate::leanh::lean_dec(v_unused_925_);
                            v___x_889_ = v_x_875_;
                            v_isShared_890_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_875_);
                            v___x_889_ = crate::leanh::lean_box(0);
                            v_isShared_890_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_926_ = crate::leanh::lean_ctor_get(v_x_875_, 0);
                    v_vs_927_ = crate::leanh::lean_ctor_get(v_x_875_, 1);
                    v_isSharedCheck_947_ = (!crate::leanh::lean_is_exclusive(v_x_875_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_929_ = v_x_875_;
                        v_isShared_930_ = v_isSharedCheck_947_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_927_);
                        crate::leanh::lean_inc(v_ks_926_);
                        crate::leanh::lean_dec(v_x_875_);
                        v___x_929_ = crate::leanh::lean_box(0);
                        v_isShared_930_ = v_isSharedCheck_947_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_891_ = lean_array_fget(v_es_880_, v_j_885_);
                v___x_892_ = crate::leanh::lean_box(0);
                v_xs_x27_893_ = lean_array_fset(v_es_880_, v_j_885_, v___x_892_);
                match crate::leanh::lean_obj_tag(v_v_891_) {
                    0 => {
                        v_key_900_ = crate::leanh::lean_ctor_get(v_v_891_, 0);
                        v_val_901_ = crate::leanh::lean_ctor_get(v_v_891_, 1);
                        v_isSharedCheck_911_ = (!crate::leanh::lean_is_exclusive(v_v_891_)) as u8;
                        if v_isSharedCheck_911_ == 0 {
                            v___x_903_ = v_v_891_;
                            v_isShared_904_ = v_isSharedCheck_911_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_901_);
                            crate::leanh::lean_inc(v_key_900_);
                            crate::leanh::lean_dec(v_v_891_);
                            v___x_903_ = crate::leanh::lean_box(0);
                            v_isShared_904_ = v_isSharedCheck_911_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_912_ = crate::leanh::lean_ctor_get(v_v_891_, 0);
                        v_isSharedCheck_922_ = (!crate::leanh::lean_is_exclusive(v_v_891_)) as u8;
                        if v_isSharedCheck_922_ == 0 {
                            v___x_914_ = v_v_891_;
                            v_isShared_915_ = v_isSharedCheck_922_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_912_);
                            crate::leanh::lean_dec(v_v_891_);
                            v___x_914_ = crate::leanh::lean_box(0);
                            v_isShared_915_ = v_isSharedCheck_922_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_923_, 0, v_x_878_);
                        crate::leanh::lean_ctor_set(v___x_923_, 1, v_x_879_);
                        v___y_895_ = v___x_923_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_896_ = lean_array_fset(v_xs_x27_893_, v_j_885_, v___y_895_);
                crate::leanh::lean_dec(v_j_885_);
                if v_isShared_890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_889_, 0, v___x_896_);
                    v___x_898_ = v___x_889_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
                    v___x_898_ = v_reuseFailAlloc_899_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_898_;
            }
            4 => {
                v___x_905_ = l_Lean_instBEqMVarId_beq(v_x_878_, v_key_900_);
                if v___x_905_ == 0 {
                    crate::leanh::lean_del_object(v___x_903_);
                    v___x_906_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_900_, v_val_901_, v_x_878_, v_x_879_,
                    );
                    v___x_907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_907_, 0, v___x_906_);
                    v___y_895_ = v___x_907_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_901_);
                    crate::leanh::lean_dec(v_key_900_);
                    if v_isShared_904_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_903_, 1, v_x_879_);
                        crate::leanh::lean_ctor_set(v___x_903_, 0, v_x_878_);
                        v___x_909_ = v___x_903_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 0, v_x_878_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 1, v_x_879_);
                        v___x_909_ = v_reuseFailAlloc_910_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_895_ = v___x_909_;
                state = 2;
                continue;
            }
            6 => {
                v___x_916_ = lean_usize_shift_right(v_x_876_, v___x_881_);
                v___x_917_ = lean_usize_add(v_x_877_, v___x_882_);
                v___x_918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_node_912_, v___x_916_, v___x_917_, v_x_878_, v_x_879_);
                if v_isShared_915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_914_, 0, v___x_918_);
                    v___x_920_ = v___x_914_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
                    v___x_920_ = v_reuseFailAlloc_921_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_895_ = v___x_920_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_930_ == 0 {
                    v___x_932_ = v___x_929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_946_, 0, v_ks_926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_946_, 1, v_vs_927_);
                    v___x_932_ = v_reuseFailAlloc_946_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v___x_932_, v_x_878_, v_x_879_);
                v___x_941_ = 7usize;
                v___x_942_ = lean_usize_dec_le(v___x_941_, v_x_877_);
                if v___x_942_ == 0 {
                    v___x_943_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_933_);
                    v___x_944_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_945_ = lean_nat_dec_lt(v___x_943_, v___x_944_);
                    crate::leanh::lean_dec(v___x_943_);
                    v___y_935_ = v___x_945_;
                    state = 10;
                    continue;
                } else {
                    v___y_935_ = v___x_942_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_935_ == 0 {
                    v_ks_936_ = crate::leanh::lean_ctor_get(v_newNode_933_, 0);
                    crate::leanh::lean_inc_ref(v_ks_936_);
                    v_vs_937_ = crate::leanh::lean_ctor_get(v_newNode_933_, 1);
                    crate::leanh::lean_inc_ref(v_vs_937_);
                    crate::leanh::lean_dec_ref(v_newNode_933_);
                    v___x_938_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_939_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_x_877_, v_ks_936_, v_vs_937_, v___x_938_, v___x_939_);
                    crate::leanh::lean_dec_ref(v_vs_937_);
                    crate::leanh::lean_dec_ref(v_ks_936_);
                    return v___x_940_;
                } else {
                    return v_newNode_933_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(
    mut v_depth_948_: usize,
    mut v_keys_949_: *mut crate::leanh::LeanObject,
    mut v_vals_950_: *mut crate::leanh::LeanObject,
    mut v_i_951_: *mut crate::leanh::LeanObject,
    mut v_entries_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v_k_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u64 = 0;
    let mut v_h_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v_h_964_: usize = 0;
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_953_ = lean_array_get_size(v_keys_949_);
                v___x_954_ = lean_nat_dec_lt(v_i_951_, v___x_953_);
                if v___x_954_ == 0 {
                    crate::leanh::lean_dec(v_i_951_);
                    return v_entries_952_;
                } else {
                    v_k_955_ = lean_array_fget_borrowed(v_keys_949_, v_i_951_);
                    v_v_956_ = lean_array_fget_borrowed(v_vals_950_, v_i_951_);
                    v___x_957_ = l_Lean_instHashableMVarId_hash(v_k_955_);
                    v_h_958_ = lean_uint64_to_usize(v___x_957_);
                    v___x_959_ = 5usize;
                    v___x_960_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_961_ = 1usize;
                    v___x_962_ = lean_usize_sub(v_depth_948_, v___x_961_);
                    v___x_963_ = lean_usize_mul(v___x_959_, v___x_962_);
                    v_h_964_ = lean_usize_shift_right(v_h_958_, v___x_963_);
                    v___x_965_ = lean_nat_add(v_i_951_, v___x_960_);
                    crate::leanh::lean_dec(v_i_951_);
                    crate::leanh::lean_inc(v_v_956_);
                    crate::leanh::lean_inc(v_k_955_);
                    v___x_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_entries_952_, v_h_964_, v_depth_948_, v_k_955_, v_v_956_);
                    v_i_951_ = v___x_965_;
                    v_entries_952_ = v___x_966_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_968_: *mut crate::leanh::LeanObject,
    mut v_keys_969_: *mut crate::leanh::LeanObject,
    mut v_vals_970_: *mut crate::leanh::LeanObject,
    mut v_i_971_: *mut crate::leanh::LeanObject,
    mut v_entries_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_973_: usize = 0;
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_973_ = crate::leanh::lean_unbox_usize(v_depth_968_);
    crate::leanh::lean_dec(v_depth_968_);
    v_res_974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_973_, v_keys_969_, v_vals_970_, v_i_971_, v_entries_972_);
    crate::leanh::lean_dec_ref(v_vals_970_);
    crate::leanh::lean_dec_ref(v_keys_969_);
    return v_res_974_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_975_: *mut crate::leanh::LeanObject,
    mut v_x_976_: *mut crate::leanh::LeanObject,
    mut v_x_977_: *mut crate::leanh::LeanObject,
    mut v_x_978_: *mut crate::leanh::LeanObject,
    mut v_x_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7047__boxed_980_: usize = 0;
    let mut v_x_7048__boxed_981_: usize = 0;
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7047__boxed_980_ = crate::leanh::lean_unbox_usize(v_x_976_);
    crate::leanh::lean_dec(v_x_976_);
    v_x_7048__boxed_981_ = crate::leanh::lean_unbox_usize(v_x_977_);
    crate::leanh::lean_dec(v_x_977_);
    v_res_982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_975_, v_x_7047__boxed_980_, v_x_7048__boxed_981_, v_x_978_, v_x_979_);
    return v_res_982_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(
    mut v_x_983_: *mut crate::leanh::LeanObject,
    mut v_x_984_: *mut crate::leanh::LeanObject,
    mut v_x_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_986_: u64 = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_instHashableMVarId_hash(v_x_984_);
    v___x_987_ = lean_uint64_to_usize(v___x_986_);
    v___x_988_ = 1usize;
    v___x_989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_983_, v___x_987_, v___x_988_, v_x_984_, v_x_985_);
    return v___x_989_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
    mut v_mvarId_990_: *mut crate::leanh::LeanObject,
    mut v_val_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v_depth_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1026_: u8 = 0;
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_994_ = lean_st_ref_take(v___y_992_);
                v_mctx_995_ = crate::leanh::lean_ctor_get(v___x_994_, 0);
                v_cache_996_ = crate::leanh::lean_ctor_get(v___x_994_, 1);
                v_zetaDeltaFVarIds_997_ = crate::leanh::lean_ctor_get(v___x_994_, 2);
                v_postponed_998_ = crate::leanh::lean_ctor_get(v___x_994_, 3);
                v_diag_999_ = crate::leanh::lean_ctor_get(v___x_994_, 4);
                v_isSharedCheck_1027_ = (!crate::leanh::lean_is_exclusive(v___x_994_)) as u8;
                if v_isSharedCheck_1027_ == 0 {
                    v___x_1001_ = v___x_994_;
                    v_isShared_1002_ = v_isSharedCheck_1027_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_999_);
                    crate::leanh::lean_inc(v_postponed_998_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_997_);
                    crate::leanh::lean_inc(v_cache_996_);
                    crate::leanh::lean_inc(v_mctx_995_);
                    crate::leanh::lean_dec(v___x_994_);
                    v___x_1001_ = crate::leanh::lean_box(0);
                    v_isShared_1002_ = v_isSharedCheck_1027_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1003_ = crate::leanh::lean_ctor_get(v_mctx_995_, 0);
                v_levelAssignDepth_1004_ = crate::leanh::lean_ctor_get(v_mctx_995_, 1);
                v_lmvarCounter_1005_ = crate::leanh::lean_ctor_get(v_mctx_995_, 2);
                v_mvarCounter_1006_ = crate::leanh::lean_ctor_get(v_mctx_995_, 3);
                v_lDecls_1007_ = crate::leanh::lean_ctor_get(v_mctx_995_, 4);
                v_decls_1008_ = crate::leanh::lean_ctor_get(v_mctx_995_, 5);
                v_userNames_1009_ = crate::leanh::lean_ctor_get(v_mctx_995_, 6);
                v_lAssignment_1010_ = crate::leanh::lean_ctor_get(v_mctx_995_, 7);
                v_eAssignment_1011_ = crate::leanh::lean_ctor_get(v_mctx_995_, 8);
                v_dAssignment_1012_ = crate::leanh::lean_ctor_get(v_mctx_995_, 9);
                v_isSharedCheck_1026_ = (!crate::leanh::lean_is_exclusive(v_mctx_995_)) as u8;
                if v_isSharedCheck_1026_ == 0 {
                    v___x_1014_ = v_mctx_995_;
                    v_isShared_1015_ = v_isSharedCheck_1026_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1012_);
                    crate::leanh::lean_inc(v_eAssignment_1011_);
                    crate::leanh::lean_inc(v_lAssignment_1010_);
                    crate::leanh::lean_inc(v_userNames_1009_);
                    crate::leanh::lean_inc(v_decls_1008_);
                    crate::leanh::lean_inc(v_lDecls_1007_);
                    crate::leanh::lean_inc(v_mvarCounter_1006_);
                    crate::leanh::lean_inc(v_lmvarCounter_1005_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1004_);
                    crate::leanh::lean_inc(v_depth_1003_);
                    crate::leanh::lean_dec(v_mctx_995_);
                    v___x_1014_ = crate::leanh::lean_box(0);
                    v_isShared_1015_ = v_isSharedCheck_1026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1016_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_eAssignment_1011_, v_mvarId_990_, v_val_991_);
                if v_isShared_1015_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1014_, 8, v___x_1016_);
                    v___x_1018_ = v___x_1014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1025_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_depth_1003_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1025_,
                        1,
                        v_levelAssignDepth_1004_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_lmvarCounter_1005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_mvarCounter_1006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_lDecls_1007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_decls_1008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 6, v_userNames_1009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 7, v_lAssignment_1010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 8, v___x_1016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 9, v_dAssignment_1012_);
                    v___x_1018_ = v_reuseFailAlloc_1025_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1001_, 0, v___x_1018_);
                    v___x_1020_ = v___x_1001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1024_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_cache_996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_zetaDeltaFVarIds_997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_postponed_998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_diag_999_);
                    v___x_1020_ = v_reuseFailAlloc_1024_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1021_ = lean_st_ref_set(v___y_992_, v___x_1020_);
                v___x_1022_ = crate::leanh::lean_box(0);
                v___x_1023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1023_, 0, v___x_1022_);
                return v___x_1023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg___boxed(
    mut v_mvarId_1028_: *mut crate::leanh::LeanObject,
    mut v_val_1029_: *mut crate::leanh::LeanObject,
    mut v___y_1030_: *mut crate::leanh::LeanObject,
    mut v___y_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
            v_mvarId_1028_,
            v_val_1029_,
            v___y_1030_,
        );
    crate::leanh::lean_dec(v___y_1030_);
    return v_res_1032_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(
    mut v_msgData_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1039_ = lean_st_ref_get(v___y_1037_);
    v_env_1040_ = crate::leanh::lean_ctor_get(v___x_1039_, 0);
    crate::leanh::lean_inc_ref(v_env_1040_);
    crate::leanh::lean_dec(v___x_1039_);
    v___x_1041_ = lean_st_ref_get(v___y_1035_);
    v_mctx_1042_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1042_);
    crate::leanh::lean_dec(v___x_1041_);
    v_lctx_1043_ = crate::leanh::lean_ctor_get(v___y_1034_, 2);
    v_options_1044_ = crate::leanh::lean_ctor_get(v___y_1036_, 2);
    crate::leanh::lean_inc_ref(v_options_1044_);
    crate::leanh::lean_inc_ref(v_lctx_1043_);
    v___x_1045_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1045_, 0, v_env_1040_);
    crate::leanh::lean_ctor_set(v___x_1045_, 1, v_mctx_1042_);
    crate::leanh::lean_ctor_set(v___x_1045_, 2, v_lctx_1043_);
    crate::leanh::lean_ctor_set(v___x_1045_, 3, v_options_1044_);
    v___x_1046_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_1045_);
    crate::leanh::lean_ctor_set(v___x_1046_, 1, v_msgData_1033_);
    v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4___boxed(
    mut v_msgData_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
    mut v___y_1050_: *mut crate::leanh::LeanObject,
    mut v___y_1051_: *mut crate::leanh::LeanObject,
    mut v___y_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msgData_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
    crate::leanh::lean_dec(v___y_1052_);
    crate::leanh::lean_dec_ref(v___y_1051_);
    crate::leanh::lean_dec(v___y_1050_);
    crate::leanh::lean_dec_ref(v___y_1049_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
    mut v_msg_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
    mut v___y_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1061_ = crate::leanh::lean_ctor_get(v___y_1058_, 5);
                v___x_1062_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msg_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
                v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                v_isSharedCheck_1071_ = (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                if v_isSharedCheck_1071_ == 0 {
                    v___x_1065_ = v___x_1062_;
                    v_isShared_1066_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1063_);
                    crate::leanh::lean_dec(v___x_1062_);
                    v___x_1065_ = crate::leanh::lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1061_);
                v___x_1067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1067_, 0, v_ref_1061_);
                crate::leanh::lean_ctor_set(v___x_1067_, 1, v_a_1063_);
                if v_isShared_1066_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1065_, 1);
                    crate::leanh::lean_ctor_set(v___x_1065_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg___boxed(
    mut v_msg_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
            v_msg_1072_,
            v___y_1073_,
            v___y_1074_,
            v___y_1075_,
            v___y_1076_,
        );
    crate::leanh::lean_dec(v___y_1076_);
    crate::leanh::lean_dec_ref(v___y_1075_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    return v_res_1078_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5;
    v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_hyp_1088_: *mut crate::leanh::LeanObject,
    mut v___x_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1136_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1087_);
                v___x_1099_ = l_Lean_MVarId_getType(
                    v_a_1087_,
                    v___y_1094_,
                    v___y_1095_,
                    v___y_1096_,
                    v___y_1097_,
                );
                if crate::leanh::lean_obj_tag(v___x_1099_) == 0 {
                    v_a_1100_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                    crate::leanh::lean_inc(v_a_1100_);
                    crate::leanh::lean_dec_ref_known(v___x_1099_, 1);
                    v___x_1101_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_a_1100_, v___y_1095_);
                    v_a_1102_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                    crate::leanh::lean_inc(v_a_1102_);
                    crate::leanh::lean_dec_ref(v___x_1101_);
                    v___x_1103_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1102_);
                    crate::leanh::lean_dec(v_a_1102_);
                    if crate::leanh::lean_obj_tag(v___x_1103_) == 1 {
                        v_val_1104_ = crate::leanh::lean_ctor_get(v___x_1103_, 0);
                        crate::leanh::lean_inc_n(v_val_1104_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1103_, 1);
                        v___x_1105_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                            v_val_1104_,
                            v_hyp_1088_,
                            v___y_1094_,
                            v___y_1095_,
                            v___y_1096_,
                            v___y_1097_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1105_) == 0 {
                            v_a_1106_ = crate::leanh::lean_ctor_get(v___x_1105_, 0);
                            crate::leanh::lean_inc(v_a_1106_);
                            crate::leanh::lean_dec_ref_known(v___x_1105_, 1);
                            crate::leanh::lean_inc(v_val_1104_);
                            v___x_1107_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(
                                v_a_1106_,
                                v_val_1104_,
                            );
                            v___x_1108_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1107_);
                            v___x_1109_ = crate::leanh::lean_box(0);
                            v___x_1110_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___x_1108_,
                                v___x_1109_,
                                v___y_1094_,
                                v___y_1095_,
                                v___y_1096_,
                                v___y_1097_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1110_) == 0 {
                                v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                                crate::leanh::lean_inc_n(v_a_1111_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1110_, 1);
                                v_u_1112_ = crate::leanh::lean_ctor_get(v_val_1104_, 0);
                                crate::leanh::lean_inc(v_u_1112_);
                                v_00_u03c3s_1113_ = crate::leanh::lean_ctor_get(v_val_1104_, 1);
                                crate::leanh::lean_inc_ref(v_00_u03c3s_1113_);
                                v_hyps_1114_ = crate::leanh::lean_ctor_get(v_val_1104_, 2);
                                crate::leanh::lean_inc_ref(v_hyps_1114_);
                                v_target_1115_ = crate::leanh::lean_ctor_get(v_val_1104_, 3);
                                crate::leanh::lean_inc_ref(v_target_1115_);
                                crate::leanh::lean_dec(v_val_1104_);
                                v_focusHyp_1116_ = crate::leanh::lean_ctor_get(v_a_1106_, 0);
                                crate::leanh::lean_inc_ref(v_focusHyp_1116_);
                                v_restHyps_1117_ = crate::leanh::lean_ctor_get(v_a_1106_, 1);
                                crate::leanh::lean_inc_ref(v_restHyps_1117_);
                                v_proof_1118_ = crate::leanh::lean_ctor_get(v_a_1106_, 2);
                                crate::leanh::lean_inc_ref(v_proof_1118_);
                                crate::leanh::lean_dec(v_a_1106_);
                                v___x_1119_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0;
                                v___x_1120_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1;
                                v___x_1121_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2;
                                v___x_1122_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3;
                                v___x_1123_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4;
                                v___x_1124_ = l_Lean_Name_mkStr6(
                                    v___x_1119_,
                                    v___x_1120_,
                                    v___x_1121_,
                                    v___x_1089_,
                                    v___x_1122_,
                                    v___x_1123_,
                                );
                                v___x_1125_ = crate::leanh::lean_box(0);
                                v___x_1126_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1126_, 0, v_u_1112_);
                                crate::leanh::lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                                v___x_1127_ = l_Lean_mkConst(v___x_1124_, v___x_1126_);
                                v___x_1128_ = l_Lean_mkApp7(
                                    v___x_1127_,
                                    v_00_u03c3s_1113_,
                                    v_hyps_1114_,
                                    v_restHyps_1117_,
                                    v_focusHyp_1116_,
                                    v_target_1115_,
                                    v_proof_1118_,
                                    v_a_1111_,
                                );
                                v___x_1129_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_a_1087_, v___x_1128_, v___y_1095_);
                                crate::leanh::lean_dec_ref(v___x_1129_);
                                v___x_1130_ = l_Lean_Expr_mvarId_x21(v_a_1111_);
                                crate::leanh::lean_dec(v_a_1111_);
                                v___x_1131_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                                crate::leanh::lean_ctor_set(v___x_1131_, 1, v___x_1125_);
                                v___x_1132_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                    v___x_1131_,
                                    v___y_1091_,
                                    v___y_1094_,
                                    v___y_1095_,
                                    v___y_1096_,
                                    v___y_1097_,
                                );
                                return v___x_1132_;
                            } else {
                                crate::leanh::lean_dec(v_a_1106_);
                                crate::leanh::lean_dec(v_val_1104_);
                                crate::leanh::lean_dec_ref(v___x_1089_);
                                crate::leanh::lean_dec(v_a_1087_);
                                v_a_1133_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                                v_isSharedCheck_1140_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                                if v_isSharedCheck_1140_ == 0 {
                                    v___x_1135_ = v___x_1110_;
                                    v_isShared_1136_ = v_isSharedCheck_1140_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1133_);
                                    crate::leanh::lean_dec(v___x_1110_);
                                    v___x_1135_ = crate::leanh::lean_box(0);
                                    v_isShared_1136_ = v_isSharedCheck_1140_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_1104_);
                            crate::leanh::lean_dec_ref(v___x_1089_);
                            crate::leanh::lean_dec(v_a_1087_);
                            v_a_1141_ = crate::leanh::lean_ctor_get(v___x_1105_, 0);
                            v_isSharedCheck_1148_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1105_)) as u8;
                            if v_isSharedCheck_1148_ == 0 {
                                v___x_1143_ = v___x_1105_;
                                v_isShared_1144_ = v_isSharedCheck_1148_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1141_);
                                crate::leanh::lean_dec(v___x_1105_);
                                v___x_1143_ = crate::leanh::lean_box(0);
                                v_isShared_1144_ = v_isSharedCheck_1148_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1103_);
                        crate::leanh::lean_dec_ref(v___x_1089_);
                        crate::leanh::lean_dec(v_hyp_1088_);
                        crate::leanh::lean_dec(v_a_1087_);
                        v___x_1149_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6);
                        v___x_1150_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v___x_1149_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
                        return v___x_1150_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1089_);
                    crate::leanh::lean_dec(v_hyp_1088_);
                    crate::leanh::lean_dec(v_a_1087_);
                    v_a_1151_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1158_ = (!crate::leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1158_ == 0 {
                        v___x_1153_ = v___x_1099_;
                        v_isShared_1154_ = v_isSharedCheck_1158_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1151_);
                        crate::leanh::lean_dec(v___x_1099_);
                        v___x_1153_ = crate::leanh::lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1158_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1136_ == 0 {
                    v___x_1138_ = v___x_1135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
                    v___x_1138_ = v_reuseFailAlloc_1139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1138_;
            }
            3 => {
                if v_isShared_1144_ == 0 {
                    v___x_1146_ = v___x_1143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1146_;
            }
            5 => {
                if v_isShared_1154_ == 0 {
                    v___x_1156_ = v___x_1153_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
                    v___x_1156_ = v_reuseFailAlloc_1157_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed(
    mut v_a_1159_: *mut crate::leanh::LeanObject,
    mut v_hyp_1160_: *mut crate::leanh::LeanObject,
    mut v___x_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(
        v_a_1159_,
        v_hyp_1160_,
        v___x_1161_,
        v___y_1162_,
        v___y_1163_,
        v___y_1164_,
        v___y_1165_,
        v___y_1166_,
        v___y_1167_,
        v___y_1168_,
        v___y_1169_,
    );
    crate::leanh::lean_dec(v___y_1169_);
    crate::leanh::lean_dec_ref(v___y_1168_);
    crate::leanh::lean_dec(v___y_1167_);
    crate::leanh::lean_dec_ref(v___y_1166_);
    crate::leanh::lean_dec(v___y_1165_);
    crate::leanh::lean_dec_ref(v___y_1164_);
    crate::leanh::lean_dec(v___y_1163_);
    crate::leanh::lean_dec_ref(v___y_1162_);
    return v_res_1171_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(
    mut v_x_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyp_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1194_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2;
                v___x_1195_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4;
                crate::leanh::lean_inc(v_x_1184_);
                v___x_1196_ = l_Lean_Syntax_isOfKind(v_x_1184_, v___x_1195_);
                if v___x_1196_ == 0 {
                    crate::leanh::lean_dec(v_x_1184_);
                    v___x_1197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
                    return v___x_1197_;
                } else {
                    v___x_1198_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_hyp_1199_ = l_Lean_Syntax_getArg(v_x_1184_, v___x_1198_);
                    crate::leanh::lean_dec(v_x_1184_);
                    v___x_1200_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6;
                    crate::leanh::lean_inc(v_hyp_1199_);
                    v___x_1201_ = l_Lean_Syntax_isOfKind(v_hyp_1199_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        crate::leanh::lean_dec(v_hyp_1199_);
                        v___x_1202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
                        return v___x_1202_;
                    } else {
                        v___x_1203_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v_a_1186_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1203_) == 0 {
                            v_a_1204_ = crate::leanh::lean_ctor_get(v___x_1203_, 0);
                            crate::leanh::lean_inc_n(v_a_1204_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1203_, 1);
                            v___f_1205_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                12,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_1205_, 0, v_a_1204_);
                            crate::leanh::lean_closure_set(v___f_1205_, 1, v_hyp_1199_);
                            crate::leanh::lean_closure_set(v___f_1205_, 2, v___x_1194_);
                            v___x_1206_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_a_1204_, v___f_1205_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
                            return v___x_1206_;
                        } else {
                            crate::leanh::lean_dec(v_hyp_1199_);
                            v_a_1207_ = crate::leanh::lean_ctor_get(v___x_1203_, 0);
                            v_isSharedCheck_1214_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1203_)) as u8;
                            if v_isSharedCheck_1214_ == 0 {
                                v___x_1209_ = v___x_1203_;
                                v_isShared_1210_ = v_isSharedCheck_1214_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1207_);
                                crate::leanh::lean_dec(v___x_1203_);
                                v___x_1209_ = crate::leanh::lean_box(0);
                                v_isShared_1210_ = v_isSharedCheck_1214_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1210_ == 0 {
                    v___x_1212_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed(
    mut v_x_1215_: *mut crate::leanh::LeanObject,
    mut v_a_1216_: *mut crate::leanh::LeanObject,
    mut v_a_1217_: *mut crate::leanh::LeanObject,
    mut v_a_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
    mut v_a_1223_: *mut crate::leanh::LeanObject,
    mut v_a_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(
        v_x_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_,
        v_a_1223_,
    );
    crate::leanh::lean_dec(v_a_1223_);
    crate::leanh::lean_dec_ref(v_a_1222_);
    crate::leanh::lean_dec(v_a_1221_);
    crate::leanh::lean_dec_ref(v_a_1220_);
    crate::leanh::lean_dec(v_a_1219_);
    crate::leanh::lean_dec_ref(v_a_1218_);
    crate::leanh::lean_dec(v_a_1217_);
    crate::leanh::lean_dec_ref(v_a_1216_);
    return v_res_1225_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(
    mut v_mvarId_1226_: *mut crate::leanh::LeanObject,
    mut v_val_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
            v_mvarId_1226_,
            v_val_1227_,
            v___y_1233_,
        );
    return v___x_1237_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___boxed(
    mut v_mvarId_1238_: *mut crate::leanh::LeanObject,
    mut v_val_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(
        v_mvarId_1238_,
        v_val_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
        v___y_1247_,
    );
    crate::leanh::lean_dec(v___y_1247_);
    crate::leanh::lean_dec_ref(v___y_1246_);
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec_ref(v___y_1244_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(
    mut v_00_u03b1_1250_: *mut crate::leanh::LeanObject,
    mut v_msg_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
            v_msg_1251_,
            v___y_1256_,
            v___y_1257_,
            v___y_1258_,
            v___y_1259_,
        );
    return v___x_1261_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___boxed(
    mut v_00_u03b1_1262_: *mut crate::leanh::LeanObject,
    mut v_msg_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(
        v_00_u03b1_1262_,
        v_msg_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
        v___y_1270_,
        v___y_1271_,
    );
    crate::leanh::lean_dec(v___y_1271_);
    crate::leanh::lean_dec_ref(v___y_1270_);
    crate::leanh::lean_dec(v___y_1269_);
    crate::leanh::lean_dec_ref(v___y_1268_);
    crate::leanh::lean_dec(v___y_1267_);
    crate::leanh::lean_dec_ref(v___y_1266_);
    crate::leanh::lean_dec(v___y_1265_);
    crate::leanh::lean_dec_ref(v___y_1264_);
    return v_res_1273_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2(
    mut v_00_u03b2_1274_: *mut crate::leanh::LeanObject,
    mut v_x_1275_: *mut crate::leanh::LeanObject,
    mut v_x_1276_: *mut crate::leanh::LeanObject,
    mut v_x_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_x_1275_, v_x_1276_, v_x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1279_: *mut crate::leanh::LeanObject,
    mut v_x_1280_: *mut crate::leanh::LeanObject,
    mut v_x_1281_: usize,
    mut v_x_1282_: usize,
    mut v_x_1283_: *mut crate::leanh::LeanObject,
    mut v_x_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_1280_, v_x_1281_, v_x_1282_, v_x_1283_, v_x_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1286_: *mut crate::leanh::LeanObject,
    mut v_x_1287_: *mut crate::leanh::LeanObject,
    mut v_x_1288_: *mut crate::leanh::LeanObject,
    mut v_x_1289_: *mut crate::leanh::LeanObject,
    mut v_x_1290_: *mut crate::leanh::LeanObject,
    mut v_x_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7642__boxed_1292_: usize = 0;
    let mut v_x_7643__boxed_1293_: usize = 0;
    let mut v_res_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7642__boxed_1292_ = crate::leanh::lean_unbox_usize(v_x_1288_);
    crate::leanh::lean_dec(v_x_1288_);
    v_x_7643__boxed_1293_ = crate::leanh::lean_unbox_usize(v_x_1289_);
    crate::leanh::lean_dec(v_x_1289_);
    v_res_1294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(v_00_u03b2_1286_, v_x_1287_, v_x_7642__boxed_1292_, v_x_7643__boxed_1293_, v_x_1290_, v_x_1291_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1295_: *mut crate::leanh::LeanObject,
    mut v_n_1296_: *mut crate::leanh::LeanObject,
    mut v_k_1297_: *mut crate::leanh::LeanObject,
    mut v_v_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v_n_1296_, v_k_1297_, v_v_1298_);
    return v___x_1299_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1300_: *mut crate::leanh::LeanObject,
    mut v_depth_1301_: usize,
    mut v_keys_1302_: *mut crate::leanh::LeanObject,
    mut v_vals_1303_: *mut crate::leanh::LeanObject,
    mut v_heq_1304_: *mut crate::leanh::LeanObject,
    mut v_i_1305_: *mut crate::leanh::LeanObject,
    mut v_entries_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_1301_, v_keys_1302_, v_vals_1303_, v_i_1305_, v_entries_1306_);
    return v___x_1307_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_1308_: *mut crate::leanh::LeanObject,
    mut v_depth_1309_: *mut crate::leanh::LeanObject,
    mut v_keys_1310_: *mut crate::leanh::LeanObject,
    mut v_vals_1311_: *mut crate::leanh::LeanObject,
    mut v_heq_1312_: *mut crate::leanh::LeanObject,
    mut v_i_1313_: *mut crate::leanh::LeanObject,
    mut v_entries_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1315_: usize = 0;
    let mut v_res_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1315_ = crate::leanh::lean_unbox_usize(v_depth_1309_);
    crate::leanh::lean_dec(v_depth_1309_);
    v_res_1316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_1308_, v_depth_boxed_1315_, v_keys_1310_, v_vals_1311_, v_heq_1312_, v_i_1313_, v_entries_1314_);
    crate::leanh::lean_dec_ref(v_vals_1311_);
    crate::leanh::lean_dec_ref(v_keys_1310_);
    return v_res_1316_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8(
    mut v_00_u03b2_1317_: *mut crate::leanh::LeanObject,
    mut v_x_1318_: *mut crate::leanh::LeanObject,
    mut v_x_1319_: *mut crate::leanh::LeanObject,
    mut v_x_1320_: *mut crate::leanh::LeanObject,
    mut v_x_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_1318_, v_x_1319_, v_x_1320_, v_x_1321_);
    return v___x_1322_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1334_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1335_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4;
    v___x_1336_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3;
    v___x_1337_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1338_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1334_,
        v___x_1335_,
        v___x_1336_,
        v___x_1337_,
    );
    return v___x_1338_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(
    mut v_a_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
    return v_res_1340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(
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
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
}
