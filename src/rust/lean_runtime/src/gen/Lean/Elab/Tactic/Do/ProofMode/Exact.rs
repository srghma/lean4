// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Exact
// Imports: Lean.Elab.Tactic.Do.ProofMode.Basic Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind,
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
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabTermEnsuringType,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkConst,
    l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
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
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value:
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
    m_data: [69, 120, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value:
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
    m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value)
            as *mut crate::leanh::LeanObject,
        3997838883980794615 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5_value)
            as *mut crate::leanh::LeanObject,
        10473037714726111349 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        109, 101, 120, 97, 99, 116, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100,
        44, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97,
        108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        80, 114, 111, 112, 65, 115, 83, 80, 114, 101, 100, 84, 97, 117, 116, 111, 108, 111, 103,
        121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2932917581903347504 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        102, 114, 111, 109, 95, 116, 97, 117, 116, 111, 108, 111, 103, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4_value)
            as *mut crate::leanh::LeanObject,
        3997838883980794615 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5_value)
            as *mut crate::leanh::LeanObject,
        18101383377255682623 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        109, 101, 120, 97, 99, 116, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100,
        44, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 83, 80, 114, 101, 100, 32, 116, 97, 117,
        116, 111, 108, 111, 103, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value:
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
    m_data: [109, 101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2_value)
            as *mut crate::leanh::LeanObject,
        6500623445574529423 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 69, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2_value) as *mut crate::leanh::LeanObject,8330976338982593627 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(
    mut v_msgData_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_908_ = lean_st_ref_get(v___y_906_);
    v_env_909_ = crate::leanh::lean_ctor_get(v___x_908_, 0);
    crate::leanh::lean_inc_ref(v_env_909_);
    crate::leanh::lean_dec(v___x_908_);
    v___x_910_ = lean_st_ref_get(v___y_904_);
    v_mctx_911_ = crate::leanh::lean_ctor_get(v___x_910_, 0);
    crate::leanh::lean_inc_ref(v_mctx_911_);
    crate::leanh::lean_dec(v___x_910_);
    v_lctx_912_ = crate::leanh::lean_ctor_get(v___y_903_, 2);
    v_options_913_ = crate::leanh::lean_ctor_get(v___y_905_, 2);
    crate::leanh::lean_inc_ref(v_options_913_);
    crate::leanh::lean_inc_ref(v_lctx_912_);
    v___x_914_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_914_, 0, v_env_909_);
    crate::leanh::lean_ctor_set(v___x_914_, 1, v_mctx_911_);
    crate::leanh::lean_ctor_set(v___x_914_, 2, v_lctx_912_);
    crate::leanh::lean_ctor_set(v___x_914_, 3, v_options_913_);
    v___x_915_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_914_);
    crate::leanh::lean_ctor_set(v___x_915_, 1, v_msgData_902_);
    v___x_916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_915_);
    return v___x_916_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0___boxed(
    mut v_msgData_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msgData_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
    crate::leanh::lean_dec(v___y_921_);
    crate::leanh::lean_dec_ref(v___y_920_);
    crate::leanh::lean_dec(v___y_919_);
    crate::leanh::lean_dec_ref(v___y_918_);
    return v_res_923_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(
    mut v_msg_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_935_: u8 = 0;
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_930_ = crate::leanh::lean_ctor_get(v___y_927_, 5);
                v___x_931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
                v_a_932_ = crate::leanh::lean_ctor_get(v___x_931_, 0);
                v_isSharedCheck_940_ = (!crate::leanh::lean_is_exclusive(v___x_931_)) as u8;
                if v_isSharedCheck_940_ == 0 {
                    v___x_934_ = v___x_931_;
                    v_isShared_935_ = v_isSharedCheck_940_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_932_);
                    crate::leanh::lean_dec(v___x_931_);
                    v___x_934_ = crate::leanh::lean_box(0);
                    v_isShared_935_ = v_isSharedCheck_940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_930_);
                v___x_936_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_936_, 0, v_ref_930_);
                crate::leanh::lean_ctor_set(v___x_936_, 1, v_a_932_);
                if v_isShared_935_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_934_, 1);
                    crate::leanh::lean_ctor_set(v___x_934_, 0, v___x_936_);
                    v___x_938_ = v___x_934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
                    v___x_938_ = v_reuseFailAlloc_939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg___boxed(
    mut v_msg_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(
            v_msg_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_,
        );
    crate::leanh::lean_dec(v___y_945_);
    crate::leanh::lean_dec_ref(v___y_944_);
    crate::leanh::lean_dec(v___y_943_);
    crate::leanh::lean_dec_ref(v___y_942_);
    return v_res_947_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7;
    v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
    return v___x_963_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_965_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9;
    v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
    return v___x_966_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(
    mut v_goal_967_: *mut crate::leanh::LeanObject,
    mut v_hyp_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
    mut v_a_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_985_: u8 = 0;
    let mut v_u_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_a_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut v_unused_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_974_ = l_Lean_Syntax_getId(v_hyp_968_);
                crate::leanh::lean_inc_ref(v_goal_967_);
                v___x_975_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_967_, v___x_974_);
                crate::leanh::lean_dec(v___x_974_);
                if crate::leanh::lean_obj_tag(v___x_975_) == 0 {
                    crate::leanh::lean_dec(v_hyp_968_);
                    crate::leanh::lean_dec_ref(v_goal_967_);
                    v___x_976_ = crate::leanh::lean_box(0);
                    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
                    return v___x_977_;
                } else {
                    v_isSharedCheck_1041_ = (!crate::leanh::lean_is_exclusive(v___x_975_)) as u8;
                    if v_isSharedCheck_1041_ == 0 {
                        v_unused_1042_ = crate::leanh::lean_ctor_get(v___x_975_, 0);
                        crate::leanh::lean_dec(v_unused_1042_);
                        v___x_979_ = v___x_975_;
                        v_isShared_980_ = v_isSharedCheck_1041_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_975_);
                        v___x_979_ = crate::leanh::lean_box(0);
                        v_isShared_980_ = v_isSharedCheck_1041_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_hyp_968_);
                crate::leanh::lean_inc_ref(v_goal_967_);
                v___x_981_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                    v_goal_967_,
                    v_hyp_968_,
                    v_a_969_,
                    v_a_970_,
                    v_a_971_,
                    v_a_972_,
                );
                if crate::leanh::lean_obj_tag(v___x_981_) == 0 {
                    v_a_982_ = crate::leanh::lean_ctor_get(v___x_981_, 0);
                    v_isSharedCheck_1032_ = (!crate::leanh::lean_is_exclusive(v___x_981_)) as u8;
                    if v_isSharedCheck_1032_ == 0 {
                        v___x_984_ = v___x_981_;
                        v_isShared_985_ = v_isSharedCheck_1032_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_982_);
                        crate::leanh::lean_dec(v___x_981_);
                        v___x_984_ = crate::leanh::lean_box(0);
                        v_isShared_985_ = v_isSharedCheck_1032_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_979_);
                    crate::leanh::lean_dec(v_hyp_968_);
                    crate::leanh::lean_dec_ref(v_goal_967_);
                    v_a_1033_ = crate::leanh::lean_ctor_get(v___x_981_, 0);
                    v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v___x_981_)) as u8;
                    if v_isSharedCheck_1040_ == 0 {
                        v___x_1035_ = v___x_981_;
                        v_isShared_1036_ = v_isSharedCheck_1040_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1033_);
                        crate::leanh::lean_dec(v___x_981_);
                        v___x_1035_ = crate::leanh::lean_box(0);
                        v_isShared_1036_ = v_isSharedCheck_1040_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_u_986_ = crate::leanh::lean_ctor_get(v_goal_967_, 0);
                crate::leanh::lean_inc(v_u_986_);
                v_00_u03c3s_987_ = crate::leanh::lean_ctor_get(v_goal_967_, 1);
                crate::leanh::lean_inc_ref(v_00_u03c3s_987_);
                v_hyps_988_ = crate::leanh::lean_ctor_get(v_goal_967_, 2);
                crate::leanh::lean_inc_ref(v_hyps_988_);
                v_target_989_ = crate::leanh::lean_ctor_get(v_goal_967_, 3);
                crate::leanh::lean_inc_ref_n(v_target_989_, 3);
                crate::leanh::lean_dec_ref(v_goal_967_);
                v_focusHyp_990_ = crate::leanh::lean_ctor_get(v_a_982_, 0);
                crate::leanh::lean_inc_ref(v_focusHyp_990_);
                v_restHyps_991_ = crate::leanh::lean_ctor_get(v_a_982_, 1);
                crate::leanh::lean_inc_ref(v_restHyps_991_);
                v_proof_992_ = crate::leanh::lean_ctor_get(v_a_982_, 2);
                crate::leanh::lean_inc_ref(v_proof_992_);
                crate::leanh::lean_dec(v_a_982_);
                v___x_993_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6;
                v___x_994_ = crate::leanh::lean_box(0);
                v___x_995_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_995_, 0, v_u_986_);
                crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
                v___x_996_ = l_Lean_mkConst(v___x_993_, v___x_995_);
                v___x_997_ = l_Lean_mkApp5(
                    v___x_996_,
                    v_00_u03c3s_987_,
                    v_hyps_988_,
                    v_restHyps_991_,
                    v_target_989_,
                    v_proof_992_,
                );
                v___x_1005_ = l_Lean_Meta_isExprDefEq(
                    v_focusHyp_990_,
                    v_target_989_,
                    v_a_969_,
                    v_a_970_,
                    v_a_971_,
                    v_a_972_,
                );
                if crate::leanh::lean_obj_tag(v___x_1005_) == 0 {
                    v_a_1006_ = crate::leanh::lean_ctor_get(v___x_1005_, 0);
                    crate::leanh::lean_inc(v_a_1006_);
                    crate::leanh::lean_dec_ref_known(v___x_1005_, 1);
                    v___x_1007_ = (crate::leanh::lean_unbox(v_a_1006_) as u8);
                    crate::leanh::lean_dec(v_a_1006_);
                    if v___x_1007_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_997_);
                        crate::leanh::lean_del_object(v___x_984_);
                        crate::leanh::lean_del_object(v___x_979_);
                        v___x_1008_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8,
                        );
                        v___x_1009_ = l_Lean_MessageData_ofSyntax(v_hyp_968_);
                        v___x_1010_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1010_, 0, v___x_1008_);
                        crate::leanh::lean_ctor_set(v___x_1010_, 1, v___x_1009_);
                        v___x_1011_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10,
                        );
                        v___x_1012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1010_);
                        crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
                        v___x_1013_ = l_Lean_MessageData_ofExpr(v_target_989_);
                        v___x_1014_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1014_, 0, v___x_1012_);
                        crate::leanh::lean_ctor_set(v___x_1014_, 1, v___x_1013_);
                        v___x_1015_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(v___x_1014_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
                        v_a_1016_ = crate::leanh::lean_ctor_get(v___x_1015_, 0);
                        v_isSharedCheck_1023_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1015_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v___x_1018_ = v___x_1015_;
                            v_isShared_1019_ = v_isSharedCheck_1023_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1016_);
                            crate::leanh::lean_dec(v___x_1015_);
                            v___x_1018_ = crate::leanh::lean_box(0);
                            v_isShared_1019_ = v_isSharedCheck_1023_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_target_989_);
                        crate::leanh::lean_dec(v_hyp_968_);
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_997_);
                    crate::leanh::lean_dec_ref(v_target_989_);
                    crate::leanh::lean_del_object(v___x_984_);
                    crate::leanh::lean_del_object(v___x_979_);
                    crate::leanh::lean_dec(v_hyp_968_);
                    v_a_1024_ = crate::leanh::lean_ctor_get(v___x_1005_, 0);
                    v_isSharedCheck_1031_ = (!crate::leanh::lean_is_exclusive(v___x_1005_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v___x_1026_ = v___x_1005_;
                        v_isShared_1027_ = v_isSharedCheck_1031_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1024_);
                        crate::leanh::lean_dec(v___x_1005_);
                        v___x_1026_ = crate::leanh::lean_box(0);
                        v_isShared_1027_ = v_isSharedCheck_1031_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_979_, 0, v___x_997_);
                    v___x_1000_ = v___x_979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_997_);
                    v___x_1000_ = v_reuseFailAlloc_1004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_984_, 0, v___x_1000_);
                    v___x_1002_ = v___x_984_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
                    v___x_1002_ = v_reuseFailAlloc_1003_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1002_;
            }
            6 => {
                if v_isShared_1019_ == 0 {
                    v___x_1021_ = v___x_1018_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
                    v___x_1021_ = v_reuseFailAlloc_1022_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1021_;
            }
            8 => {
                if v_isShared_1027_ == 0 {
                    v___x_1029_ = v___x_1026_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
                    v___x_1029_ = v_reuseFailAlloc_1030_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1029_;
            }
            10 => {
                if v_isShared_1036_ == 0 {
                    v___x_1038_ = v___x_1035_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
                    v___x_1038_ = v_reuseFailAlloc_1039_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___boxed(
    mut v_goal_1043_: *mut crate::leanh::LeanObject,
    mut v_hyp_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(
        v_goal_1043_,
        v_hyp_1044_,
        v_a_1045_,
        v_a_1046_,
        v_a_1047_,
        v_a_1048_,
    );
    crate::leanh::lean_dec(v_a_1048_);
    crate::leanh::lean_dec_ref(v_a_1047_);
    crate::leanh::lean_dec(v_a_1046_);
    crate::leanh::lean_dec_ref(v_a_1045_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(
    mut v_00_u03b1_1051_: *mut crate::leanh::LeanObject,
    mut v_msg_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
    mut v___y_1054_: *mut crate::leanh::LeanObject,
    mut v___y_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___redArg(
            v_msg_1052_,
            v___y_1053_,
            v___y_1054_,
            v___y_1055_,
            v___y_1056_,
        );
    return v___x_1058_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0___boxed(
    mut v_00_u03b1_1059_: *mut crate::leanh::LeanObject,
    mut v_msg_1060_: *mut crate::leanh::LeanObject,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0(
        v_00_u03b1_1059_,
        v_msg_1060_,
        v___y_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
    );
    crate::leanh::lean_dec(v___y_1064_);
    crate::leanh::lean_dec_ref(v___y_1063_);
    crate::leanh::lean_dec(v___y_1062_);
    crate::leanh::lean_dec_ref(v___y_1061_);
    return v_res_1066_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(
    mut v_msg_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1073_ = crate::leanh::lean_ctor_get(v___y_1070_, 5);
                v___x_1074_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exact_spec__0_spec__0(v_msg_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
                v_a_1075_ = crate::leanh::lean_ctor_get(v___x_1074_, 0);
                v_isSharedCheck_1083_ = (!crate::leanh::lean_is_exclusive(v___x_1074_)) as u8;
                if v_isSharedCheck_1083_ == 0 {
                    v___x_1077_ = v___x_1074_;
                    v_isShared_1078_ = v_isSharedCheck_1083_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1075_);
                    crate::leanh::lean_dec(v___x_1074_);
                    v___x_1077_ = crate::leanh::lean_box(0);
                    v_isShared_1078_ = v_isSharedCheck_1083_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1073_);
                v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1079_, 0, v_ref_1073_);
                crate::leanh::lean_ctor_set(v___x_1079_, 1, v_a_1075_);
                if v_isShared_1078_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1077_, 1);
                    crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1079_);
                    v___x_1081_ = v___x_1077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
                    v___x_1081_ = v_reuseFailAlloc_1082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg___boxed(
    mut v_msg_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(
            v_msg_1084_,
            v___y_1085_,
            v___y_1086_,
            v___y_1087_,
            v___y_1088_,
        );
    crate::leanh::lean_dec(v___y_1088_);
    crate::leanh::lean_dec_ref(v___y_1087_);
    crate::leanh::lean_dec(v___y_1086_);
    crate::leanh::lean_dec_ref(v___y_1085_);
    return v_res_1090_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = crate::leanh::lean_box(0);
    v___x_1092_ = l_Lean_mkSort(v___x_1091_);
    return v___x_1092_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0,
    );
    v___x_1094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7;
    v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
    return v___x_1116_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9;
    v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
    return v___x_1119_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(
    mut v_goal_1120_: *mut crate::leanh::LeanObject,
    mut v_hyp_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v_u_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v_val_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v_a_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1190_: u8 = 0;
    let mut v_reuseFailAlloc_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1192_: u8 = 0;
    let mut v_reuseFailAlloc_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1131_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1,
                );
                v___x_1132_ = 0;
                v___x_1133_ = crate::leanh::lean_box(0);
                v___x_1134_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_1131_,
                    v___x_1132_,
                    v___x_1133_,
                    v_a_1126_,
                    v_a_1127_,
                    v_a_1128_,
                    v_a_1129_,
                );
                if crate::leanh::lean_obj_tag(v___x_1134_) == 0 {
                    v_a_1135_ = crate::leanh::lean_ctor_get(v___x_1134_, 0);
                    v_isSharedCheck_1194_ = (!crate::leanh::lean_is_exclusive(v___x_1134_)) as u8;
                    if v_isSharedCheck_1194_ == 0 {
                        v___x_1137_ = v___x_1134_;
                        v_isShared_1138_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1135_);
                        crate::leanh::lean_dec(v___x_1134_);
                        v___x_1137_ = crate::leanh::lean_box(0);
                        v_isShared_1138_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_hyp_1121_);
                    crate::leanh::lean_dec_ref(v_goal_1120_);
                    return v___x_1134_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1135_);
                if v_isShared_1138_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1137_, 1);
                    v___x_1140_ = v___x_1137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1135_);
                    v___x_1140_ = v_reuseFailAlloc_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1141_ = 0;
                crate::leanh::lean_inc(v_hyp_1121_);
                v___x_1142_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
                    v_hyp_1121_,
                    v___x_1140_,
                    v___x_1141_,
                    v_a_1122_,
                    v_a_1123_,
                    v_a_1124_,
                    v_a_1125_,
                    v_a_1126_,
                    v_a_1127_,
                    v_a_1128_,
                    v_a_1129_,
                );
                if crate::leanh::lean_obj_tag(v___x_1142_) == 0 {
                    v_a_1143_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                    v_isSharedCheck_1192_ = (!crate::leanh::lean_is_exclusive(v___x_1142_)) as u8;
                    if v_isSharedCheck_1192_ == 0 {
                        v___x_1145_ = v___x_1142_;
                        v_isShared_1146_ = v_isSharedCheck_1192_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1143_);
                        crate::leanh::lean_dec(v___x_1142_);
                        v___x_1145_ = crate::leanh::lean_box(0);
                        v_isShared_1146_ = v_isSharedCheck_1192_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1135_);
                    crate::leanh::lean_dec(v_hyp_1121_);
                    crate::leanh::lean_dec_ref(v_goal_1120_);
                    return v___x_1142_;
                }
            }
            3 => {
                v_u_1147_ = crate::leanh::lean_ctor_get(v_goal_1120_, 0);
                crate::leanh::lean_inc(v_u_1147_);
                v_00_u03c3s_1148_ = crate::leanh::lean_ctor_get(v_goal_1120_, 1);
                crate::leanh::lean_inc_ref_n(v_00_u03c3s_1148_, 2);
                v_hyps_1149_ = crate::leanh::lean_ctor_get(v_goal_1120_, 2);
                crate::leanh::lean_inc_ref(v_hyps_1149_);
                v_target_1150_ = crate::leanh::lean_ctor_get(v_goal_1120_, 3);
                crate::leanh::lean_inc_ref(v_target_1150_);
                crate::leanh::lean_dec_ref(v_goal_1120_);
                v___x_1151_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2;
                v___x_1152_ = crate::leanh::lean_box(0);
                v___x_1153_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1153_, 0, v_u_1147_);
                crate::leanh::lean_ctor_set(v___x_1153_, 1, v___x_1152_);
                crate::leanh::lean_inc_ref(v___x_1153_);
                v___x_1154_ = l_Lean_mkConst(v___x_1151_, v___x_1153_);
                v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_00_u03c3s_1148_);
                if v_isShared_1146_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1145_, 1);
                    crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1155_);
                    v___x_1157_ = v_reuseFailAlloc_1191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1158_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_1157_,
                    v___x_1132_,
                    v___x_1133_,
                    v_a_1126_,
                    v_a_1127_,
                    v_a_1128_,
                    v_a_1129_,
                );
                if crate::leanh::lean_obj_tag(v___x_1158_) == 0 {
                    v_a_1159_ = crate::leanh::lean_ctor_get(v___x_1158_, 0);
                    crate::leanh::lean_inc(v_a_1159_);
                    crate::leanh::lean_dec_ref_known(v___x_1158_, 1);
                    v___x_1160_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
                    crate::leanh::lean_inc_ref(v___x_1153_);
                    v___x_1161_ = l_Lean_mkConst(v___x_1160_, v___x_1153_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_1148_);
                    crate::leanh::lean_inc(v_a_1135_);
                    v___x_1162_ =
                        l_Lean_mkApp3(v___x_1161_, v_a_1135_, v_00_u03c3s_1148_, v_a_1159_);
                    v___x_1163_ = crate::leanh::lean_box(0);
                    v___x_1164_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_1162_,
                        v___x_1163_,
                        v_a_1126_,
                        v_a_1127_,
                        v_a_1128_,
                        v_a_1129_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1164_) == 0 {
                        v_a_1165_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                        v_isSharedCheck_1182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                        if v_isSharedCheck_1182_ == 0 {
                            v___x_1167_ = v___x_1164_;
                            v_isShared_1168_ = v_isSharedCheck_1182_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1165_);
                            crate::leanh::lean_dec(v___x_1164_);
                            v___x_1167_ = crate::leanh::lean_box(0);
                            v_isShared_1168_ = v_isSharedCheck_1182_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1153_, 2);
                        crate::leanh::lean_dec_ref(v_target_1150_);
                        crate::leanh::lean_dec_ref(v_hyps_1149_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_1148_);
                        crate::leanh::lean_dec(v_a_1143_);
                        crate::leanh::lean_dec(v_a_1135_);
                        crate::leanh::lean_dec(v_hyp_1121_);
                        v_a_1183_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                        v_isSharedCheck_1190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                        if v_isSharedCheck_1190_ == 0 {
                            v___x_1185_ = v___x_1164_;
                            v_isShared_1186_ = v_isSharedCheck_1190_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1183_);
                            crate::leanh::lean_dec(v___x_1164_);
                            v___x_1185_ = crate::leanh::lean_box(0);
                            v_isShared_1186_ = v_isSharedCheck_1190_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1153_, 2);
                    crate::leanh::lean_dec_ref(v_target_1150_);
                    crate::leanh::lean_dec_ref(v_hyps_1149_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1148_);
                    crate::leanh::lean_dec(v_a_1143_);
                    crate::leanh::lean_dec(v_a_1135_);
                    crate::leanh::lean_dec(v_hyp_1121_);
                    return v___x_1158_;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_1165_) == 1 {
                    crate::leanh::lean_dec(v_hyp_1121_);
                    v_val_1169_ = crate::leanh::lean_ctor_get(v_a_1165_, 0);
                    crate::leanh::lean_inc(v_val_1169_);
                    crate::leanh::lean_dec_ref_known(v_a_1165_, 1);
                    v___x_1170_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
                    v___x_1171_ = l_Lean_mkConst(v___x_1170_, v___x_1153_);
                    v___x_1172_ = l_Lean_mkApp6(
                        v___x_1171_,
                        v_00_u03c3s_1148_,
                        v_a_1135_,
                        v_hyps_1149_,
                        v_target_1150_,
                        v_val_1169_,
                        v_a_1143_,
                    );
                    if v_isShared_1168_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1172_);
                        v___x_1174_ = v___x_1167_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
                        v___x_1174_ = v_reuseFailAlloc_1175_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1167_);
                    crate::leanh::lean_dec(v_a_1165_);
                    crate::leanh::lean_dec_ref_known(v___x_1153_, 2);
                    crate::leanh::lean_dec_ref(v_target_1150_);
                    crate::leanh::lean_dec_ref(v_hyps_1149_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1148_);
                    crate::leanh::lean_dec(v_a_1143_);
                    crate::leanh::lean_dec(v_a_1135_);
                    v___x_1176_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8,
                    );
                    v___x_1177_ = l_Lean_MessageData_ofSyntax(v_hyp_1121_);
                    v___x_1178_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1176_);
                    crate::leanh::lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                    v___x_1179_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10,
                    );
                    v___x_1180_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1180_, 0, v___x_1178_);
                    crate::leanh::lean_ctor_set(v___x_1180_, 1, v___x_1179_);
                    v___x_1181_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_1180_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
                    return v___x_1181_;
                }
            }
            6 => {
                return v___x_1174_;
            }
            7 => {
                if v_isShared_1186_ == 0 {
                    v___x_1188_ = v___x_1185_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
                    v___x_1188_ = v_reuseFailAlloc_1189_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___boxed(
    mut v_goal_1195_: *mut crate::leanh::LeanObject,
    mut v_hyp_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
    mut v_a_1204_: *mut crate::leanh::LeanObject,
    mut v_a_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1206_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(
        v_goal_1195_,
        v_hyp_1196_,
        v_a_1197_,
        v_a_1198_,
        v_a_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
        v_a_1203_,
        v_a_1204_,
    );
    crate::leanh::lean_dec(v_a_1204_);
    crate::leanh::lean_dec_ref(v_a_1203_);
    crate::leanh::lean_dec(v_a_1202_);
    crate::leanh::lean_dec_ref(v_a_1201_);
    crate::leanh::lean_dec(v_a_1200_);
    crate::leanh::lean_dec_ref(v_a_1199_);
    crate::leanh::lean_dec(v_a_1198_);
    crate::leanh::lean_dec_ref(v_a_1197_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(
    mut v_00_u03b1_1207_: *mut crate::leanh::LeanObject,
    mut v_msg_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(
            v_msg_1208_,
            v___y_1213_,
            v___y_1214_,
            v___y_1215_,
            v___y_1216_,
        );
    return v___x_1218_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___boxed(
    mut v_00_u03b1_1219_: *mut crate::leanh::LeanObject,
    mut v_msg_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0(
        v_00_u03b1_1219_,
        v_msg_1220_,
        v___y_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
        v___y_1225_,
        v___y_1226_,
        v___y_1227_,
        v___y_1228_,
    );
    crate::leanh::lean_dec(v___y_1228_);
    crate::leanh::lean_dec_ref(v___y_1227_);
    crate::leanh::lean_dec(v___y_1226_);
    crate::leanh::lean_dec_ref(v___y_1225_);
    crate::leanh::lean_dec(v___y_1224_);
    crate::leanh::lean_dec_ref(v___y_1223_);
    crate::leanh::lean_dec(v___y_1222_);
    crate::leanh::lean_dec_ref(v___y_1221_);
    return v_res_1230_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = crate::leanh::lean_box(0);
    v___x_1232_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1233_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
    crate::leanh::lean_ctor_set(v___x_1233_, 1, v___x_1231_);
    return v___x_1233_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___closed__0);
    v___x_1236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    return v___x_1236_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg___boxed(
    mut v___y_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
    return v_res_1238_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(
    mut v_00_u03b1_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
    return v___x_1249_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___boxed(
    mut v_00_u03b1_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0(v_00_u03b1_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
    crate::leanh::lean_dec(v___y_1258_);
    crate::leanh::lean_dec_ref(v___y_1257_);
    crate::leanh::lean_dec(v___y_1256_);
    crate::leanh::lean_dec_ref(v___y_1255_);
    crate::leanh::lean_dec(v___y_1254_);
    crate::leanh::lean_dec_ref(v___y_1253_);
    crate::leanh::lean_dec(v___y_1252_);
    crate::leanh::lean_dec_ref(v___y_1251_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(
    mut v_e_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_unused_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = l_Lean_Expr_hasMVar(v_e_1261_);
                if v___x_1264_ == 0 {
                    v___x_1265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1265_, 0, v_e_1261_);
                    return v___x_1265_;
                } else {
                    v___x_1266_ = lean_st_ref_get(v___y_1262_);
                    v_mctx_1267_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1267_);
                    crate::leanh::lean_dec(v___x_1266_);
                    v___x_1268_ = l_Lean_instantiateMVarsCore(v_mctx_1267_, v_e_1261_);
                    v_fst_1269_ = crate::leanh::lean_ctor_get(v___x_1268_, 0);
                    crate::leanh::lean_inc(v_fst_1269_);
                    v_snd_1270_ = crate::leanh::lean_ctor_get(v___x_1268_, 1);
                    crate::leanh::lean_inc(v_snd_1270_);
                    crate::leanh::lean_dec_ref(v___x_1268_);
                    v___x_1271_ = lean_st_ref_take(v___y_1262_);
                    v_cache_1272_ = crate::leanh::lean_ctor_get(v___x_1271_, 1);
                    v_zetaDeltaFVarIds_1273_ = crate::leanh::lean_ctor_get(v___x_1271_, 2);
                    v_postponed_1274_ = crate::leanh::lean_ctor_get(v___x_1271_, 3);
                    v_diag_1275_ = crate::leanh::lean_ctor_get(v___x_1271_, 4);
                    v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v___x_1271_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v_unused_1285_ = crate::leanh::lean_ctor_get(v___x_1271_, 0);
                        crate::leanh::lean_dec(v_unused_1285_);
                        v___x_1277_ = v___x_1271_;
                        v_isShared_1278_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1275_);
                        crate::leanh::lean_inc(v_postponed_1274_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1273_);
                        crate::leanh::lean_inc(v_cache_1272_);
                        crate::leanh::lean_dec(v___x_1271_);
                        v___x_1277_ = crate::leanh::lean_box(0);
                        v_isShared_1278_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v_snd_1270_);
                    v___x_1280_ = v___x_1277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_snd_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_cache_1272_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1283_,
                        2,
                        v_zetaDeltaFVarIds_1273_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_postponed_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_diag_1275_);
                    v___x_1280_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1281_ = lean_st_ref_set(v___y_1262_, v___x_1280_);
                v___x_1282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1282_, 0, v_fst_1269_);
                return v___x_1282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg___boxed(
    mut v_e_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(
            v_e_1286_,
            v___y_1287_,
        );
    crate::leanh::lean_dec(v___y_1287_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(
    mut v_e_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(
            v_e_1290_,
            v___y_1296_,
        );
    return v___x_1300_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___boxed(
    mut v_e_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1(
        v_e_1301_,
        v___y_1302_,
        v___y_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
    );
    crate::leanh::lean_dec(v___y_1309_);
    crate::leanh::lean_dec_ref(v___y_1308_);
    crate::leanh::lean_dec(v___y_1307_);
    crate::leanh::lean_dec_ref(v___y_1306_);
    crate::leanh::lean_dec(v___y_1305_);
    crate::leanh::lean_dec_ref(v___y_1304_);
    crate::leanh::lean_dec(v___y_1303_);
    crate::leanh::lean_dec_ref(v___y_1302_);
    return v_res_1311_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(
    mut v_x_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1316_);
    crate::leanh::lean_inc_ref(v___y_1315_);
    crate::leanh::lean_inc(v___y_1314_);
    crate::leanh::lean_inc_ref(v___y_1313_);
    v___x_1322_ = crate::leanh::lean_apply_9(
        v_x_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
        crate::leanh::lean_box(0),
    );
    return v___x_1322_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed(
    mut v_x_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0(v_x_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
    crate::leanh::lean_dec(v___y_1327_);
    crate::leanh::lean_dec_ref(v___y_1326_);
    crate::leanh::lean_dec(v___y_1325_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    return v_res_1333_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(
    mut v_mvarId_1334_: *mut crate::leanh::LeanObject,
    mut v_x_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1339_);
                crate::leanh::lean_inc_ref(v___y_1338_);
                crate::leanh::lean_inc(v___y_1337_);
                crate::leanh::lean_inc_ref(v___y_1336_);
                v___f_1345_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1345_, 0, v_x_1335_);
                crate::leanh::lean_closure_set(v___f_1345_, 1, v___y_1336_);
                crate::leanh::lean_closure_set(v___f_1345_, 2, v___y_1337_);
                crate::leanh::lean_closure_set(v___f_1345_, 3, v___y_1338_);
                crate::leanh::lean_closure_set(v___f_1345_, 4, v___y_1339_);
                v___x_1346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1334_,
                    v___f_1345_,
                    v___y_1340_,
                    v___y_1341_,
                    v___y_1342_,
                    v___y_1343_,
                );
                if crate::leanh::lean_obj_tag(v___x_1346_) == 0 {
                    return v___x_1346_;
                } else {
                    v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1346_, 0);
                    v_isSharedCheck_1354_ = (!crate::leanh::lean_is_exclusive(v___x_1346_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1349_ = v___x_1346_;
                        v_isShared_1350_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1347_);
                        crate::leanh::lean_dec(v___x_1346_);
                        v___x_1349_ = crate::leanh::lean_box(0);
                        v_isShared_1350_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg___boxed(
    mut v_mvarId_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_1355_, v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
    crate::leanh::lean_dec(v___y_1364_);
    crate::leanh::lean_dec_ref(v___y_1363_);
    crate::leanh::lean_dec(v___y_1362_);
    crate::leanh::lean_dec_ref(v___y_1361_);
    crate::leanh::lean_dec(v___y_1360_);
    crate::leanh::lean_dec_ref(v___y_1359_);
    crate::leanh::lean_dec(v___y_1358_);
    crate::leanh::lean_dec_ref(v___y_1357_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(
    mut v_00_u03b1_1367_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1368_: *mut crate::leanh::LeanObject,
    mut v_x_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_mvarId_1368_, v_x_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___boxed(
    mut v_00_u03b1_1380_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1392_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3(
            v_00_u03b1_1380_,
            v_mvarId_1381_,
            v_x_1382_,
            v___y_1383_,
            v___y_1384_,
            v___y_1385_,
            v___y_1386_,
            v___y_1387_,
            v___y_1388_,
            v___y_1389_,
            v___y_1390_,
        );
    crate::leanh::lean_dec(v___y_1390_);
    crate::leanh::lean_dec_ref(v___y_1389_);
    crate::leanh::lean_dec(v___y_1388_);
    crate::leanh::lean_dec_ref(v___y_1387_);
    crate::leanh::lean_dec(v___y_1386_);
    crate::leanh::lean_dec_ref(v___y_1385_);
    crate::leanh::lean_dec(v___y_1384_);
    crate::leanh::lean_dec_ref(v___y_1383_);
    return v_res_1392_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_1393_: *mut crate::leanh::LeanObject,
    mut v_x_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
    mut v_x_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1397_ = crate::leanh::lean_ctor_get(v_x_1393_, 0);
                v_vs_1398_ = crate::leanh::lean_ctor_get(v_x_1393_, 1);
                v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v_x_1393_)) as u8;
                if v_isSharedCheck_1422_ == 0 {
                    v___x_1400_ = v_x_1393_;
                    v_isShared_1401_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1398_);
                    crate::leanh::lean_inc(v_ks_1397_);
                    crate::leanh::lean_dec(v_x_1393_);
                    v___x_1400_ = crate::leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1402_ = lean_array_get_size(v_ks_1397_);
                v___x_1403_ = lean_nat_dec_lt(v_x_1394_, v___x_1402_);
                if v___x_1403_ == 0 {
                    crate::leanh::lean_dec(v_x_1394_);
                    v___x_1404_ = lean_array_push(v_ks_1397_, v_x_1395_);
                    v___x_1405_ = lean_array_push(v_vs_1398_, v_x_1396_);
                    if v_isShared_1401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1405_);
                        crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1404_);
                        v___x_1407_ = v___x_1400_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1408_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1404_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1405_);
                        v___x_1407_ = v_reuseFailAlloc_1408_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1409_ = lean_array_fget_borrowed(v_ks_1397_, v_x_1394_);
                    v___x_1410_ = l_Lean_instBEqMVarId_beq(v_x_1395_, v_k_x27_1409_);
                    if v___x_1410_ == 0 {
                        if v_isShared_1401_ == 0 {
                            v___x_1412_ = v___x_1400_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1416_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_ks_1397_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_vs_1398_);
                            v___x_1412_ = v_reuseFailAlloc_1416_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1417_ = lean_array_fset(v_ks_1397_, v_x_1394_, v_x_1395_);
                        v___x_1418_ = lean_array_fset(v_vs_1398_, v_x_1394_, v_x_1396_);
                        crate::leanh::lean_dec(v_x_1394_);
                        if v_isShared_1401_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1418_);
                            crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1417_);
                            v___x_1420_ = v___x_1400_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1421_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1417_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
                            v___x_1420_ = v_reuseFailAlloc_1421_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1407_;
            }
            3 => {
                v___x_1413_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1414_ = lean_nat_add(v_x_1394_, v___x_1413_);
                crate::leanh::lean_dec(v_x_1394_);
                v_x_1393_ = v___x_1412_;
                v_x_1394_ = v___x_1414_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(
    mut v_n_1423_: *mut crate::leanh::LeanObject,
    mut v_k_1424_: *mut crate::leanh::LeanObject,
    mut v_v_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1427_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_1423_, v___x_1426_, v_k_1424_, v_v_1425_);
    return v___x_1427_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1428_: usize = 0;
    let mut v___x_1429_: usize = 0;
    let mut v___x_1430_: usize = 0;
    v___x_1428_ = 5usize;
    v___x_1429_ = 1usize;
    v___x_1430_ = lean_usize_shift_left(v___x_1429_, v___x_1428_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    let mut v___x_1433_: usize = 0;
    v___x_1431_ = 1usize;
    v___x_1432_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_1433_ = lean_usize_sub(v___x_1432_, v___x_1431_);
    return v___x_1433_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1434_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(
    mut v_x_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: usize,
    mut v_x_1437_: usize,
    mut v_x_1438_: *mut crate::leanh::LeanObject,
    mut v_x_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: usize = 0;
    let mut v___x_1443_: usize = 0;
    let mut v___x_1444_: usize = 0;
    let mut v_j_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v_v_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v_node_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: usize = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_unused_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1495_: u8 = 0;
    let mut v_ks_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: usize = 0;
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1435_) == 0 {
                    v_es_1440_ = crate::leanh::lean_ctor_get(v_x_1435_, 0);
                    v___x_1441_ = 5usize;
                    v___x_1442_ = 1usize;
                    v___x_1443_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_1444_ = lean_usize_land(v_x_1436_, v___x_1443_);
                    v_j_1445_ = lean_usize_to_nat(v___x_1444_);
                    v___x_1446_ = lean_array_get_size(v_es_1440_);
                    v___x_1447_ = lean_nat_dec_lt(v_j_1445_, v___x_1446_);
                    if v___x_1447_ == 0 {
                        crate::leanh::lean_dec(v_j_1445_);
                        crate::leanh::lean_dec(v_x_1439_);
                        crate::leanh::lean_dec(v_x_1438_);
                        return v_x_1435_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1440_);
                        v_isSharedCheck_1484_ = (!crate::leanh::lean_is_exclusive(v_x_1435_)) as u8;
                        if v_isSharedCheck_1484_ == 0 {
                            v_unused_1485_ = crate::leanh::lean_ctor_get(v_x_1435_, 0);
                            crate::leanh::lean_dec(v_unused_1485_);
                            v___x_1449_ = v_x_1435_;
                            v_isShared_1450_ = v_isSharedCheck_1484_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1435_);
                            v___x_1449_ = crate::leanh::lean_box(0);
                            v_isShared_1450_ = v_isSharedCheck_1484_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1486_ = crate::leanh::lean_ctor_get(v_x_1435_, 0);
                    v_vs_1487_ = crate::leanh::lean_ctor_get(v_x_1435_, 1);
                    v_isSharedCheck_1507_ = (!crate::leanh::lean_is_exclusive(v_x_1435_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1489_ = v_x_1435_;
                        v_isShared_1490_ = v_isSharedCheck_1507_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1487_);
                        crate::leanh::lean_inc(v_ks_1486_);
                        crate::leanh::lean_dec(v_x_1435_);
                        v___x_1489_ = crate::leanh::lean_box(0);
                        v_isShared_1490_ = v_isSharedCheck_1507_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1451_ = lean_array_fget(v_es_1440_, v_j_1445_);
                v___x_1452_ = crate::leanh::lean_box(0);
                v_xs_x27_1453_ = lean_array_fset(v_es_1440_, v_j_1445_, v___x_1452_);
                match crate::leanh::lean_obj_tag(v_v_1451_) {
                    0 => {
                        v_key_1460_ = crate::leanh::lean_ctor_get(v_v_1451_, 0);
                        v_val_1461_ = crate::leanh::lean_ctor_get(v_v_1451_, 1);
                        v_isSharedCheck_1471_ = (!crate::leanh::lean_is_exclusive(v_v_1451_)) as u8;
                        if v_isSharedCheck_1471_ == 0 {
                            v___x_1463_ = v_v_1451_;
                            v_isShared_1464_ = v_isSharedCheck_1471_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1461_);
                            crate::leanh::lean_inc(v_key_1460_);
                            crate::leanh::lean_dec(v_v_1451_);
                            v___x_1463_ = crate::leanh::lean_box(0);
                            v_isShared_1464_ = v_isSharedCheck_1471_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1472_ = crate::leanh::lean_ctor_get(v_v_1451_, 0);
                        v_isSharedCheck_1482_ = (!crate::leanh::lean_is_exclusive(v_v_1451_)) as u8;
                        if v_isSharedCheck_1482_ == 0 {
                            v___x_1474_ = v_v_1451_;
                            v_isShared_1475_ = v_isSharedCheck_1482_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1472_);
                            crate::leanh::lean_dec(v_v_1451_);
                            v___x_1474_ = crate::leanh::lean_box(0);
                            v_isShared_1475_ = v_isSharedCheck_1482_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1483_, 0, v_x_1438_);
                        crate::leanh::lean_ctor_set(v___x_1483_, 1, v_x_1439_);
                        v___y_1455_ = v___x_1483_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1456_ = lean_array_fset(v_xs_x27_1453_, v_j_1445_, v___y_1455_);
                crate::leanh::lean_dec(v_j_1445_);
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v___x_1456_);
                    v___x_1458_ = v___x_1449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
                    v___x_1458_ = v_reuseFailAlloc_1459_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1458_;
            }
            4 => {
                v___x_1465_ = l_Lean_instBEqMVarId_beq(v_x_1438_, v_key_1460_);
                if v___x_1465_ == 0 {
                    crate::leanh::lean_del_object(v___x_1463_);
                    v___x_1466_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1460_,
                        v_val_1461_,
                        v_x_1438_,
                        v_x_1439_,
                    );
                    v___x_1467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
                    v___y_1455_ = v___x_1467_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1461_);
                    crate::leanh::lean_dec(v_key_1460_);
                    if v_isShared_1464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1463_, 1, v_x_1439_);
                        crate::leanh::lean_ctor_set(v___x_1463_, 0, v_x_1438_);
                        v___x_1469_ = v___x_1463_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_x_1438_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_x_1439_);
                        v___x_1469_ = v_reuseFailAlloc_1470_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1455_ = v___x_1469_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1476_ = lean_usize_shift_right(v_x_1436_, v___x_1441_);
                v___x_1477_ = lean_usize_add(v_x_1437_, v___x_1442_);
                v___x_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_node_1472_, v___x_1476_, v___x_1477_, v_x_1438_, v_x_1439_);
                if v_isShared_1475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1478_);
                    v___x_1480_ = v___x_1474_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
                    v___x_1480_ = v_reuseFailAlloc_1481_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1455_ = v___x_1480_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_ks_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_vs_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1506_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v___x_1492_, v_x_1438_, v_x_1439_);
                v___x_1501_ = 7usize;
                v___x_1502_ = lean_usize_dec_le(v___x_1501_, v_x_1437_);
                if v___x_1502_ == 0 {
                    v___x_1503_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1493_);
                    v___x_1504_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1505_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
                    crate::leanh::lean_dec(v___x_1503_);
                    v___y_1495_ = v___x_1505_;
                    state = 10;
                    continue;
                } else {
                    v___y_1495_ = v___x_1502_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1495_ == 0 {
                    v_ks_1496_ = crate::leanh::lean_ctor_get(v_newNode_1493_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1496_);
                    v_vs_1497_ = crate::leanh::lean_ctor_get(v_newNode_1493_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1497_);
                    crate::leanh::lean_dec_ref(v_newNode_1493_);
                    v___x_1498_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1499_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_1500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_x_1437_, v_ks_1496_, v_vs_1497_, v___x_1498_, v___x_1499_);
                    crate::leanh::lean_dec_ref(v_vs_1497_);
                    crate::leanh::lean_dec_ref(v_ks_1496_);
                    return v___x_1500_;
                } else {
                    return v_newNode_1493_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(
    mut v_depth_1508_: usize,
    mut v_keys_1509_: *mut crate::leanh::LeanObject,
    mut v_vals_1510_: *mut crate::leanh::LeanObject,
    mut v_i_1511_: *mut crate::leanh::LeanObject,
    mut v_entries_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v_k_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u64 = 0;
    let mut v_h_1518_: usize = 0;
    let mut v___x_1519_: usize = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: usize = 0;
    let mut v_h_1524_: usize = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1513_ = lean_array_get_size(v_keys_1509_);
                v___x_1514_ = lean_nat_dec_lt(v_i_1511_, v___x_1513_);
                if v___x_1514_ == 0 {
                    crate::leanh::lean_dec(v_i_1511_);
                    return v_entries_1512_;
                } else {
                    v_k_1515_ = lean_array_fget_borrowed(v_keys_1509_, v_i_1511_);
                    v_v_1516_ = lean_array_fget_borrowed(v_vals_1510_, v_i_1511_);
                    v___x_1517_ = l_Lean_instHashableMVarId_hash(v_k_1515_);
                    v_h_1518_ = lean_uint64_to_usize(v___x_1517_);
                    v___x_1519_ = 5usize;
                    v___x_1520_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1521_ = 1usize;
                    v___x_1522_ = lean_usize_sub(v_depth_1508_, v___x_1521_);
                    v___x_1523_ = lean_usize_mul(v___x_1519_, v___x_1522_);
                    v_h_1524_ = lean_usize_shift_right(v_h_1518_, v___x_1523_);
                    v___x_1525_ = lean_nat_add(v_i_1511_, v___x_1520_);
                    crate::leanh::lean_dec(v_i_1511_);
                    crate::leanh::lean_inc(v_v_1516_);
                    crate::leanh::lean_inc(v_k_1515_);
                    v___x_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_entries_1512_, v_h_1524_, v_depth_1508_, v_k_1515_, v_v_1516_);
                    v_i_1511_ = v___x_1525_;
                    v_entries_1512_ = v___x_1526_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_depth_1528_: *mut crate::leanh::LeanObject,
    mut v_keys_1529_: *mut crate::leanh::LeanObject,
    mut v_vals_1530_: *mut crate::leanh::LeanObject,
    mut v_i_1531_: *mut crate::leanh::LeanObject,
    mut v_entries_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1533_: usize = 0;
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1533_ = crate::leanh::lean_unbox_usize(v_depth_1528_);
    crate::leanh::lean_dec(v_depth_1528_);
    v_res_1534_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_boxed_1533_, v_keys_1529_, v_vals_1530_, v_i_1531_, v_entries_1532_);
    crate::leanh::lean_dec_ref(v_vals_1530_);
    crate::leanh::lean_dec_ref(v_keys_1529_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1535_: *mut crate::leanh::LeanObject,
    mut v_x_1536_: *mut crate::leanh::LeanObject,
    mut v_x_1537_: *mut crate::leanh::LeanObject,
    mut v_x_1538_: *mut crate::leanh::LeanObject,
    mut v_x_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5114__boxed_1540_: usize = 0;
    let mut v_x_5115__boxed_1541_: usize = 0;
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5114__boxed_1540_ = crate::leanh::lean_unbox_usize(v_x_1536_);
    crate::leanh::lean_dec(v_x_1536_);
    v_x_5115__boxed_1541_ = crate::leanh::lean_unbox_usize(v_x_1537_);
    crate::leanh::lean_dec(v_x_1537_);
    v_res_1542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_1535_, v_x_5114__boxed_1540_, v_x_5115__boxed_1541_, v_x_1538_, v_x_1539_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(
    mut v_x_1543_: *mut crate::leanh::LeanObject,
    mut v_x_1544_: *mut crate::leanh::LeanObject,
    mut v_x_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: u64 = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_instHashableMVarId_hash(v_x_1544_);
    v___x_1547_ = lean_uint64_to_usize(v___x_1546_);
    v___x_1548_ = 1usize;
    v___x_1549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_1543_, v___x_1547_, v___x_1548_, v_x_1544_, v_x_1545_);
    return v___x_1549_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(
    mut v_mvarId_1550_: *mut crate::leanh::LeanObject,
    mut v_val_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v_depth_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1554_ = lean_st_ref_take(v___y_1552_);
                v_mctx_1555_ = crate::leanh::lean_ctor_get(v___x_1554_, 0);
                v_cache_1556_ = crate::leanh::lean_ctor_get(v___x_1554_, 1);
                v_zetaDeltaFVarIds_1557_ = crate::leanh::lean_ctor_get(v___x_1554_, 2);
                v_postponed_1558_ = crate::leanh::lean_ctor_get(v___x_1554_, 3);
                v_diag_1559_ = crate::leanh::lean_ctor_get(v___x_1554_, 4);
                v_isSharedCheck_1587_ = (!crate::leanh::lean_is_exclusive(v___x_1554_)) as u8;
                if v_isSharedCheck_1587_ == 0 {
                    v___x_1561_ = v___x_1554_;
                    v_isShared_1562_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1559_);
                    crate::leanh::lean_inc(v_postponed_1558_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1557_);
                    crate::leanh::lean_inc(v_cache_1556_);
                    crate::leanh::lean_inc(v_mctx_1555_);
                    crate::leanh::lean_dec(v___x_1554_);
                    v___x_1561_ = crate::leanh::lean_box(0);
                    v_isShared_1562_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1563_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 0);
                v_levelAssignDepth_1564_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 1);
                v_lmvarCounter_1565_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 2);
                v_mvarCounter_1566_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 3);
                v_lDecls_1567_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 4);
                v_decls_1568_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 5);
                v_userNames_1569_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 6);
                v_lAssignment_1570_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 7);
                v_eAssignment_1571_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 8);
                v_dAssignment_1572_ = crate::leanh::lean_ctor_get(v_mctx_1555_, 9);
                v_isSharedCheck_1586_ = (!crate::leanh::lean_is_exclusive(v_mctx_1555_)) as u8;
                if v_isSharedCheck_1586_ == 0 {
                    v___x_1574_ = v_mctx_1555_;
                    v_isShared_1575_ = v_isSharedCheck_1586_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1572_);
                    crate::leanh::lean_inc(v_eAssignment_1571_);
                    crate::leanh::lean_inc(v_lAssignment_1570_);
                    crate::leanh::lean_inc(v_userNames_1569_);
                    crate::leanh::lean_inc(v_decls_1568_);
                    crate::leanh::lean_inc(v_lDecls_1567_);
                    crate::leanh::lean_inc(v_mvarCounter_1566_);
                    crate::leanh::lean_inc(v_lmvarCounter_1565_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1564_);
                    crate::leanh::lean_inc(v_depth_1563_);
                    crate::leanh::lean_dec(v_mctx_1555_);
                    v___x_1574_ = crate::leanh::lean_box(0);
                    v_isShared_1575_ = v_isSharedCheck_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1576_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_eAssignment_1571_, v_mvarId_1550_, v_val_1551_);
                if v_isShared_1575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1574_, 8, v___x_1576_);
                    v___x_1578_ = v___x_1574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_depth_1563_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1585_,
                        1,
                        v_levelAssignDepth_1564_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_lmvarCounter_1565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_mvarCounter_1566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_lDecls_1567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_decls_1568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_userNames_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_lAssignment_1570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 8, v___x_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 9, v_dAssignment_1572_);
                    v___x_1578_ = v_reuseFailAlloc_1585_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1578_);
                    v___x_1580_ = v___x_1561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_cache_1556_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1584_,
                        2,
                        v_zetaDeltaFVarIds_1557_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_postponed_1558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_diag_1559_);
                    v___x_1580_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1581_ = lean_st_ref_set(v___y_1552_, v___x_1580_);
                v___x_1582_ = crate::leanh::lean_box(0);
                v___x_1583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1582_);
                return v___x_1583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg___boxed(
    mut v_mvarId_1588_: *mut crate::leanh::LeanObject,
    mut v_val_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(
            v_mvarId_1588_,
            v_val_1589_,
            v___y_1590_,
        );
    crate::leanh::lean_dec(v___y_1590_);
    return v_res_1592_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0;
    v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v___x_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1596_);
                v___x_1615_ = l_Lean_MVarId_getType(
                    v_a_1596_,
                    v___y_1602_,
                    v___y_1603_,
                    v___y_1604_,
                    v___y_1605_,
                );
                if crate::leanh::lean_obj_tag(v___x_1615_) == 0 {
                    v_a_1616_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                    crate::leanh::lean_inc(v_a_1616_);
                    crate::leanh::lean_dec_ref_known(v___x_1615_, 1);
                    v___x_1617_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__1___redArg(v_a_1616_, v___y_1603_);
                    v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                    crate::leanh::lean_inc(v_a_1618_);
                    crate::leanh::lean_dec_ref(v___x_1617_);
                    v___x_1619_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1618_);
                    crate::leanh::lean_dec(v_a_1618_);
                    if crate::leanh::lean_obj_tag(v___x_1619_) == 1 {
                        v_val_1620_ = crate::leanh::lean_ctor_get(v___x_1619_, 0);
                        crate::leanh::lean_inc_n(v_val_1620_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1619_, 1);
                        crate::leanh::lean_inc(v___x_1597_);
                        v___x_1621_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(
                            v_val_1620_,
                            v___x_1597_,
                            v___y_1602_,
                            v___y_1603_,
                            v___y_1604_,
                            v___y_1605_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1621_) == 0 {
                            v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                            crate::leanh::lean_inc(v_a_1622_);
                            crate::leanh::lean_dec_ref_known(v___x_1621_, 1);
                            if crate::leanh::lean_obj_tag(v_a_1622_) == 1 {
                                crate::leanh::lean_dec(v_val_1620_);
                                crate::leanh::lean_dec(v___x_1597_);
                                v_val_1623_ = crate::leanh::lean_ctor_get(v_a_1622_, 0);
                                crate::leanh::lean_inc(v_val_1623_);
                                crate::leanh::lean_dec_ref_known(v_a_1622_, 1);
                                v___x_1624_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_1596_, v_val_1623_, v___y_1603_);
                                crate::leanh::lean_dec_ref(v___x_1624_);
                                v___y_1608_ = v___y_1599_;
                                v___y_1609_ = v___y_1602_;
                                v___y_1610_ = v___y_1603_;
                                v___y_1611_ = v___y_1604_;
                                v___y_1612_ = v___y_1605_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1622_);
                                v___x_1625_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(
                                    v_val_1620_,
                                    v___x_1597_,
                                    v___y_1598_,
                                    v___y_1599_,
                                    v___y_1600_,
                                    v___y_1601_,
                                    v___y_1602_,
                                    v___y_1603_,
                                    v___y_1604_,
                                    v___y_1605_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1625_) == 0 {
                                    v_a_1626_ = crate::leanh::lean_ctor_get(v___x_1625_, 0);
                                    crate::leanh::lean_inc(v_a_1626_);
                                    crate::leanh::lean_dec_ref_known(v___x_1625_, 1);
                                    v___x_1627_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(v_a_1596_, v_a_1626_, v___y_1603_);
                                    crate::leanh::lean_dec_ref(v___x_1627_);
                                    v___y_1608_ = v___y_1599_;
                                    v___y_1609_ = v___y_1602_;
                                    v___y_1610_ = v___y_1603_;
                                    v___y_1611_ = v___y_1604_;
                                    v___y_1612_ = v___y_1605_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1596_);
                                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1625_, 0);
                                    v_isSharedCheck_1635_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1625_)) as u8;
                                    if v_isSharedCheck_1635_ == 0 {
                                        v___x_1630_ = v___x_1625_;
                                        v_isShared_1631_ = v_isSharedCheck_1635_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1628_);
                                        crate::leanh::lean_dec(v___x_1625_);
                                        v___x_1630_ = crate::leanh::lean_box(0);
                                        v_isShared_1631_ = v_isSharedCheck_1635_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_1620_);
                            crate::leanh::lean_dec(v___x_1597_);
                            crate::leanh::lean_dec(v_a_1596_);
                            v_a_1636_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                            v_isSharedCheck_1643_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1621_)) as u8;
                            if v_isSharedCheck_1643_ == 0 {
                                v___x_1638_ = v___x_1621_;
                                v_isShared_1639_ = v_isSharedCheck_1643_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1636_);
                                crate::leanh::lean_dec(v___x_1621_);
                                v___x_1638_ = crate::leanh::lean_box(0);
                                v_isShared_1639_ = v_isSharedCheck_1643_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1619_);
                        crate::leanh::lean_dec(v___x_1597_);
                        crate::leanh::lean_dec(v_a_1596_);
                        v___x_1644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1);
                        v___x_1645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure_spec__0___redArg(v___x_1644_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
                        return v___x_1645_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1597_);
                    crate::leanh::lean_dec(v_a_1596_);
                    v_a_1646_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                    v_isSharedCheck_1653_ = (!crate::leanh::lean_is_exclusive(v___x_1615_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1648_ = v___x_1615_;
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1646_);
                        crate::leanh::lean_dec(v___x_1615_);
                        v___x_1648_ = crate::leanh::lean_box(0);
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1613_ = crate::leanh::lean_box(0);
                v___x_1614_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_1613_,
                    v___y_1608_,
                    v___y_1609_,
                    v___y_1610_,
                    v___y_1611_,
                    v___y_1612_,
                );
                return v___x_1614_;
            }
            2 => {
                if v_isShared_1631_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1633_;
            }
            4 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1641_;
            }
            6 => {
                if v_isShared_1649_ == 0 {
                    v___x_1651_ = v___x_1648_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
                    v___x_1651_ = v_reuseFailAlloc_1652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed(
    mut v_a_1654_: *mut crate::leanh::LeanObject,
    mut v___x_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(
        v_a_1654_,
        v___x_1655_,
        v___y_1656_,
        v___y_1657_,
        v___y_1658_,
        v___y_1659_,
        v___y_1660_,
        v___y_1661_,
        v___y_1662_,
        v___y_1663_,
    );
    crate::leanh::lean_dec(v___y_1663_);
    crate::leanh::lean_dec_ref(v___y_1662_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    crate::leanh::lean_dec(v___y_1659_);
    crate::leanh::lean_dec_ref(v___y_1658_);
    crate::leanh::lean_dec(v___y_1657_);
    crate::leanh::lean_dec_ref(v___y_1656_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(
    mut v_x_1674_: *mut crate::leanh::LeanObject,
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v_a_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_a_1679_: *mut crate::leanh::LeanObject,
    mut v_a_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1684_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3;
                crate::leanh::lean_inc(v_x_1674_);
                v___x_1685_ = l_Lean_Syntax_isOfKind(v_x_1674_, v___x_1684_);
                if v___x_1685_ == 0 {
                    crate::leanh::lean_dec(v_x_1674_);
                    v___x_1686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__0___redArg();
                    return v___x_1686_;
                } else {
                    v___x_1687_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v_a_1676_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1687_) == 0 {
                        v_a_1688_ = crate::leanh::lean_ctor_get(v___x_1687_, 0);
                        crate::leanh::lean_inc_n(v_a_1688_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1687_, 1);
                        v___x_1689_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1690_ = l_Lean_Syntax_getArg(v_x_1674_, v___x_1689_);
                        crate::leanh::lean_dec(v_x_1674_);
                        v___f_1691_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___boxed
                                as *mut core::ffi::c_void,
                            11,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1691_, 0, v_a_1688_);
                        crate::leanh::lean_closure_set(v___f_1691_, 1, v___x_1690_);
                        v___x_1692_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__3___redArg(v_a_1688_, v___f_1691_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
                        return v___x_1692_;
                    } else {
                        crate::leanh::lean_dec(v_x_1674_);
                        v_a_1693_ = crate::leanh::lean_ctor_get(v___x_1687_, 0);
                        v_isSharedCheck_1700_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1687_)) as u8;
                        if v_isSharedCheck_1700_ == 0 {
                            v___x_1695_ = v___x_1687_;
                            v_isShared_1696_ = v_isSharedCheck_1700_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1693_);
                            crate::leanh::lean_dec(v___x_1687_);
                            v___x_1695_ = crate::leanh::lean_box(0);
                            v_isShared_1696_ = v_isSharedCheck_1700_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1696_ == 0 {
                    v___x_1698_ = v___x_1695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
                    v___x_1698_ = v_reuseFailAlloc_1699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed(
    mut v_x_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(
        v_x_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_,
        v_a_1709_,
    );
    crate::leanh::lean_dec(v_a_1709_);
    crate::leanh::lean_dec_ref(v_a_1708_);
    crate::leanh::lean_dec(v_a_1707_);
    crate::leanh::lean_dec_ref(v_a_1706_);
    crate::leanh::lean_dec(v_a_1705_);
    crate::leanh::lean_dec_ref(v_a_1704_);
    crate::leanh::lean_dec(v_a_1703_);
    crate::leanh::lean_dec_ref(v_a_1702_);
    return v_res_1711_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(
    mut v_mvarId_1712_: *mut crate::leanh::LeanObject,
    mut v_val_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___redArg(
            v_mvarId_1712_,
            v_val_1713_,
            v___y_1719_,
        );
    return v___x_1723_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2___boxed(
    mut v_mvarId_1724_: *mut crate::leanh::LeanObject,
    mut v_val_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1735_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2(
        v_mvarId_1724_,
        v_val_1725_,
        v___y_1726_,
        v___y_1727_,
        v___y_1728_,
        v___y_1729_,
        v___y_1730_,
        v___y_1731_,
        v___y_1732_,
        v___y_1733_,
    );
    crate::leanh::lean_dec(v___y_1733_);
    crate::leanh::lean_dec_ref(v___y_1732_);
    crate::leanh::lean_dec(v___y_1731_);
    crate::leanh::lean_dec_ref(v___y_1730_);
    crate::leanh::lean_dec(v___y_1729_);
    crate::leanh::lean_dec_ref(v___y_1728_);
    crate::leanh::lean_dec(v___y_1727_);
    crate::leanh::lean_dec_ref(v___y_1726_);
    return v_res_1735_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2(
    mut v_00_u03b2_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
    mut v_x_1738_: *mut crate::leanh::LeanObject,
    mut v_x_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2___redArg(v_x_1737_, v_x_1738_, v_x_1739_);
    return v___x_1740_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1741_: *mut crate::leanh::LeanObject,
    mut v_x_1742_: *mut crate::leanh::LeanObject,
    mut v_x_1743_: usize,
    mut v_x_1744_: usize,
    mut v_x_1745_: *mut crate::leanh::LeanObject,
    mut v_x_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___redArg(v_x_1742_, v_x_1743_, v_x_1744_, v_x_1745_, v_x_1746_);
    return v___x_1747_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1748_: *mut crate::leanh::LeanObject,
    mut v_x_1749_: *mut crate::leanh::LeanObject,
    mut v_x_1750_: *mut crate::leanh::LeanObject,
    mut v_x_1751_: *mut crate::leanh::LeanObject,
    mut v_x_1752_: *mut crate::leanh::LeanObject,
    mut v_x_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5577__boxed_1754_: usize = 0;
    let mut v_x_5578__boxed_1755_: usize = 0;
    let mut v_res_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5577__boxed_1754_ = crate::leanh::lean_unbox_usize(v_x_1750_);
    crate::leanh::lean_dec(v_x_1750_);
    v_x_5578__boxed_1755_ = crate::leanh::lean_unbox_usize(v_x_1751_);
    crate::leanh::lean_dec(v_x_1751_);
    v_res_1756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4(v_00_u03b2_1748_, v_x_1749_, v_x_5577__boxed_1754_, v_x_5578__boxed_1755_, v_x_1752_, v_x_1753_);
    return v_res_1756_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1757_: *mut crate::leanh::LeanObject,
    mut v_n_1758_: *mut crate::leanh::LeanObject,
    mut v_k_1759_: *mut crate::leanh::LeanObject,
    mut v_v_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5___redArg(v_n_1758_, v_k_1759_, v_v_1760_);
    return v___x_1761_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(
    mut v_00_u03b2_1762_: *mut crate::leanh::LeanObject,
    mut v_depth_1763_: usize,
    mut v_keys_1764_: *mut crate::leanh::LeanObject,
    mut v_vals_1765_: *mut crate::leanh::LeanObject,
    mut v_heq_1766_: *mut crate::leanh::LeanObject,
    mut v_i_1767_: *mut crate::leanh::LeanObject,
    mut v_entries_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_1763_, v_keys_1764_, v_vals_1765_, v_i_1767_, v_entries_1768_);
    return v___x_1769_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_1770_: *mut crate::leanh::LeanObject,
    mut v_depth_1771_: *mut crate::leanh::LeanObject,
    mut v_keys_1772_: *mut crate::leanh::LeanObject,
    mut v_vals_1773_: *mut crate::leanh::LeanObject,
    mut v_heq_1774_: *mut crate::leanh::LeanObject,
    mut v_i_1775_: *mut crate::leanh::LeanObject,
    mut v_entries_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1777_: usize = 0;
    let mut v_res_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1777_ = crate::leanh::lean_unbox_usize(v_depth_1771_);
    crate::leanh::lean_dec(v_depth_1771_);
    v_res_1778_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_1770_, v_depth_boxed_1777_, v_keys_1772_, v_vals_1773_, v_heq_1774_, v_i_1775_, v_entries_1776_);
    crate::leanh::lean_dec_ref(v_vals_1773_);
    crate::leanh::lean_dec_ref(v_keys_1772_);
    return v_res_1778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
    mut v_x_1781_: *mut crate::leanh::LeanObject,
    mut v_x_1782_: *mut crate::leanh::LeanObject,
    mut v_x_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExact_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1780_, v_x_1781_, v_x_1782_, v_x_1783_);
    return v___x_1784_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1797_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3;
    v___x_1798_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3;
    v___x_1799_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1800_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1796_,
        v___x_1797_,
        v___x_1798_,
        v___x_1799_,
    );
    return v___x_1800_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___boxed(
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
    return v_res_1802_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
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
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Exact_0__Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
}
