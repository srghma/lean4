// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Constructor
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp6, l_Lean_mkConst,
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
    lean_nat_dec_lt, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 83, 80, 114, 101, 100,
        46, 97, 110, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value:
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
    m_data: [97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value:
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
    m_data: [97, 110, 100, 95, 105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value)
            as *mut crate::leanh::LeanObject,
        8506583206358682360 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value) as *mut crate::leanh::LeanObject,15307255260373031539 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 77, 67, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value) as *mut crate::leanh::LeanObject,12918838808455169038 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(
    mut v_e_702_: *mut crate::leanh::LeanObject,
    mut v___y_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_unused_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_705_ = l_Lean_Expr_hasMVar(v_e_702_);
                if v___x_705_ == 0 {
                    v___x_706_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_706_, 0, v_e_702_);
                    return v___x_706_;
                } else {
                    v___x_707_ = lean_st_ref_get(v___y_703_);
                    v_mctx_708_ = crate::leanh::lean_ctor_get(v___x_707_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_708_);
                    crate::leanh::lean_dec(v___x_707_);
                    v___x_709_ = l_Lean_instantiateMVarsCore(v_mctx_708_, v_e_702_);
                    v_fst_710_ = crate::leanh::lean_ctor_get(v___x_709_, 0);
                    crate::leanh::lean_inc(v_fst_710_);
                    v_snd_711_ = crate::leanh::lean_ctor_get(v___x_709_, 1);
                    crate::leanh::lean_inc(v_snd_711_);
                    crate::leanh::lean_dec_ref(v___x_709_);
                    v___x_712_ = lean_st_ref_take(v___y_703_);
                    v_cache_713_ = crate::leanh::lean_ctor_get(v___x_712_, 1);
                    v_zetaDeltaFVarIds_714_ = crate::leanh::lean_ctor_get(v___x_712_, 2);
                    v_postponed_715_ = crate::leanh::lean_ctor_get(v___x_712_, 3);
                    v_diag_716_ = crate::leanh::lean_ctor_get(v___x_712_, 4);
                    v_isSharedCheck_725_ = (!crate::leanh::lean_is_exclusive(v___x_712_)) as u8;
                    if v_isSharedCheck_725_ == 0 {
                        v_unused_726_ = crate::leanh::lean_ctor_get(v___x_712_, 0);
                        crate::leanh::lean_dec(v_unused_726_);
                        v___x_718_ = v___x_712_;
                        v_isShared_719_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_716_);
                        crate::leanh::lean_inc(v_postponed_715_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_714_);
                        crate::leanh::lean_inc(v_cache_713_);
                        crate::leanh::lean_dec(v___x_712_);
                        v___x_718_ = crate::leanh::lean_box(0);
                        v_isShared_719_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_718_, 0, v_snd_711_);
                    v___x_721_ = v___x_718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 0, v_snd_711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 1, v_cache_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 2, v_zetaDeltaFVarIds_714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 3, v_postponed_715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 4, v_diag_716_);
                    v___x_721_ = v_reuseFailAlloc_724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_722_ = lean_st_ref_set(v___y_703_, v___x_721_);
                v___x_723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_723_, 0, v_fst_710_);
                return v___x_723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg___boxed(
    mut v_e_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_727_, v___y_728_);
    crate::leanh::lean_dec(v___y_728_);
    return v_res_730_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(
    mut v_e_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_731_, v___y_733_);
    return v___x_737_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___boxed(
    mut v_e_738_: *mut crate::leanh::LeanObject,
    mut v___y_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(
            v_e_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_,
        );
    crate::leanh::lean_dec(v___y_742_);
    crate::leanh::lean_dec_ref(v___y_741_);
    crate::leanh::lean_dec(v___y_740_);
    crate::leanh::lean_dec_ref(v___y_739_);
    return v_res_744_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(
    mut v_msgData_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = lean_st_ref_get(v___y_749_);
    v_env_752_ = crate::leanh::lean_ctor_get(v___x_751_, 0);
    crate::leanh::lean_inc_ref(v_env_752_);
    crate::leanh::lean_dec(v___x_751_);
    v___x_753_ = lean_st_ref_get(v___y_747_);
    v_mctx_754_ = crate::leanh::lean_ctor_get(v___x_753_, 0);
    crate::leanh::lean_inc_ref(v_mctx_754_);
    crate::leanh::lean_dec(v___x_753_);
    v_lctx_755_ = crate::leanh::lean_ctor_get(v___y_746_, 2);
    v_options_756_ = crate::leanh::lean_ctor_get(v___y_748_, 2);
    crate::leanh::lean_inc_ref(v_options_756_);
    crate::leanh::lean_inc_ref(v_lctx_755_);
    v___x_757_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_757_, 0, v_env_752_);
    crate::leanh::lean_ctor_set(v___x_757_, 1, v_mctx_754_);
    crate::leanh::lean_ctor_set(v___x_757_, 2, v_lctx_755_);
    crate::leanh::lean_ctor_set(v___x_757_, 3, v_options_756_);
    v___x_758_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_757_);
    crate::leanh::lean_ctor_set(v___x_758_, 1, v_msgData_745_);
    v___x_759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_759_, 0, v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0___boxed(
    mut v_msgData_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
    mut v___y_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msgData_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
    crate::leanh::lean_dec(v___y_764_);
    crate::leanh::lean_dec_ref(v___y_763_);
    crate::leanh::lean_dec(v___y_762_);
    crate::leanh::lean_dec_ref(v___y_761_);
    return v_res_766_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
    mut v_msg_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_773_ = crate::leanh::lean_ctor_get(v___y_770_, 5);
                v___x_774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
                v_a_775_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                v_isSharedCheck_783_ = (!crate::leanh::lean_is_exclusive(v___x_774_)) as u8;
                if v_isSharedCheck_783_ == 0 {
                    v___x_777_ = v___x_774_;
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_775_);
                    crate::leanh::lean_dec(v___x_774_);
                    v___x_777_ = crate::leanh::lean_box(0);
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_773_);
                v___x_779_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_779_, 0, v_ref_773_);
                crate::leanh::lean_ctor_set(v___x_779_, 1, v_a_775_);
                if v_isShared_778_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_777_, 1);
                    crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_779_);
                    v___x_781_ = v___x_777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                    v___x_781_ = v_reuseFailAlloc_782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg___boxed(
    mut v_msg_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
            v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_,
        );
    crate::leanh::lean_dec(v___y_788_);
    crate::leanh::lean_dec_ref(v___y_787_);
    crate::leanh::lean_dec(v___y_786_);
    crate::leanh::lean_dec_ref(v___y_785_);
    return v_res_790_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_x_791_: *mut crate::leanh::LeanObject,
    mut v_x_792_: *mut crate::leanh::LeanObject,
    mut v_x_793_: *mut crate::leanh::LeanObject,
    mut v_x_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_795_ = crate::leanh::lean_ctor_get(v_x_791_, 0);
                v_vs_796_ = crate::leanh::lean_ctor_get(v_x_791_, 1);
                v_isSharedCheck_820_ = (!crate::leanh::lean_is_exclusive(v_x_791_)) as u8;
                if v_isSharedCheck_820_ == 0 {
                    v___x_798_ = v_x_791_;
                    v_isShared_799_ = v_isSharedCheck_820_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_796_);
                    crate::leanh::lean_inc(v_ks_795_);
                    crate::leanh::lean_dec(v_x_791_);
                    v___x_798_ = crate::leanh::lean_box(0);
                    v_isShared_799_ = v_isSharedCheck_820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_800_ = lean_array_get_size(v_ks_795_);
                v___x_801_ = lean_nat_dec_lt(v_x_792_, v___x_800_);
                if v___x_801_ == 0 {
                    crate::leanh::lean_dec(v_x_792_);
                    v___x_802_ = lean_array_push(v_ks_795_, v_x_793_);
                    v___x_803_ = lean_array_push(v_vs_796_, v_x_794_);
                    if v_isShared_799_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_798_, 1, v___x_803_);
                        crate::leanh::lean_ctor_set(v___x_798_, 0, v___x_802_);
                        v___x_805_ = v___x_798_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_806_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_803_);
                        v___x_805_ = v_reuseFailAlloc_806_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_807_ = lean_array_fget_borrowed(v_ks_795_, v_x_792_);
                    v___x_808_ = l_Lean_instBEqMVarId_beq(v_x_793_, v_k_x27_807_);
                    if v___x_808_ == 0 {
                        if v_isShared_799_ == 0 {
                            v___x_810_ = v___x_798_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_814_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_ks_795_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 1, v_vs_796_);
                            v___x_810_ = v_reuseFailAlloc_814_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_815_ = lean_array_fset(v_ks_795_, v_x_792_, v_x_793_);
                        v___x_816_ = lean_array_fset(v_vs_796_, v_x_792_, v_x_794_);
                        crate::leanh::lean_dec(v_x_792_);
                        if v_isShared_799_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_798_, 1, v___x_816_);
                            crate::leanh::lean_ctor_set(v___x_798_, 0, v___x_815_);
                            v___x_818_ = v___x_798_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_819_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_815_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
                            v___x_818_ = v_reuseFailAlloc_819_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_805_;
            }
            3 => {
                v___x_811_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_812_ = lean_nat_add(v_x_792_, v___x_811_);
                crate::leanh::lean_dec(v_x_792_);
                v_x_791_ = v___x_810_;
                v_x_792_ = v___x_812_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_n_821_: *mut crate::leanh::LeanObject,
    mut v_k_822_: *mut crate::leanh::LeanObject,
    mut v_v_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_821_, v___x_824_, v_k_822_, v_v_823_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: usize = 0;
    let mut v___x_828_: usize = 0;
    v___x_826_ = 5usize;
    v___x_827_ = 1usize;
    v___x_828_ = lean_usize_shift_left(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_829_: usize = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    v___x_829_ = 1usize;
    v___x_830_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_831_ = lean_usize_sub(v___x_830_, v___x_829_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_832_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(
    mut v_x_833_: *mut crate::leanh::LeanObject,
    mut v_x_834_: usize,
    mut v_x_835_: usize,
    mut v_x_836_: *mut crate::leanh::LeanObject,
    mut v_x_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: usize = 0;
    let mut v___x_840_: usize = 0;
    let mut v___x_841_: usize = 0;
    let mut v___x_842_: usize = 0;
    let mut v_j_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: u8 = 0;
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_848_: u8 = 0;
    let mut v_v_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v_node_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_873_: u8 = 0;
    let mut v___x_874_: usize = 0;
    let mut v___x_875_: usize = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_unused_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_893_: u8 = 0;
    let mut v_ks_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v_reuseFailAlloc_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_833_) == 0 {
                    v_es_838_ = crate::leanh::lean_ctor_get(v_x_833_, 0);
                    v___x_839_ = 5usize;
                    v___x_840_ = 1usize;
                    v___x_841_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_842_ = lean_usize_land(v_x_834_, v___x_841_);
                    v_j_843_ = lean_usize_to_nat(v___x_842_);
                    v___x_844_ = lean_array_get_size(v_es_838_);
                    v___x_845_ = lean_nat_dec_lt(v_j_843_, v___x_844_);
                    if v___x_845_ == 0 {
                        crate::leanh::lean_dec(v_j_843_);
                        crate::leanh::lean_dec(v_x_837_);
                        crate::leanh::lean_dec(v_x_836_);
                        return v_x_833_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_838_);
                        v_isSharedCheck_882_ = (!crate::leanh::lean_is_exclusive(v_x_833_)) as u8;
                        if v_isSharedCheck_882_ == 0 {
                            v_unused_883_ = crate::leanh::lean_ctor_get(v_x_833_, 0);
                            crate::leanh::lean_dec(v_unused_883_);
                            v___x_847_ = v_x_833_;
                            v_isShared_848_ = v_isSharedCheck_882_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_833_);
                            v___x_847_ = crate::leanh::lean_box(0);
                            v_isShared_848_ = v_isSharedCheck_882_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_884_ = crate::leanh::lean_ctor_get(v_x_833_, 0);
                    v_vs_885_ = crate::leanh::lean_ctor_get(v_x_833_, 1);
                    v_isSharedCheck_905_ = (!crate::leanh::lean_is_exclusive(v_x_833_)) as u8;
                    if v_isSharedCheck_905_ == 0 {
                        v___x_887_ = v_x_833_;
                        v_isShared_888_ = v_isSharedCheck_905_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_885_);
                        crate::leanh::lean_inc(v_ks_884_);
                        crate::leanh::lean_dec(v_x_833_);
                        v___x_887_ = crate::leanh::lean_box(0);
                        v_isShared_888_ = v_isSharedCheck_905_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_849_ = lean_array_fget(v_es_838_, v_j_843_);
                v___x_850_ = crate::leanh::lean_box(0);
                v_xs_x27_851_ = lean_array_fset(v_es_838_, v_j_843_, v___x_850_);
                match crate::leanh::lean_obj_tag(v_v_849_) {
                    0 => {
                        v_key_858_ = crate::leanh::lean_ctor_get(v_v_849_, 0);
                        v_val_859_ = crate::leanh::lean_ctor_get(v_v_849_, 1);
                        v_isSharedCheck_869_ = (!crate::leanh::lean_is_exclusive(v_v_849_)) as u8;
                        if v_isSharedCheck_869_ == 0 {
                            v___x_861_ = v_v_849_;
                            v_isShared_862_ = v_isSharedCheck_869_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_859_);
                            crate::leanh::lean_inc(v_key_858_);
                            crate::leanh::lean_dec(v_v_849_);
                            v___x_861_ = crate::leanh::lean_box(0);
                            v_isShared_862_ = v_isSharedCheck_869_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_870_ = crate::leanh::lean_ctor_get(v_v_849_, 0);
                        v_isSharedCheck_880_ = (!crate::leanh::lean_is_exclusive(v_v_849_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_872_ = v_v_849_;
                            v_isShared_873_ = v_isSharedCheck_880_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_870_);
                            crate::leanh::lean_dec(v_v_849_);
                            v___x_872_ = crate::leanh::lean_box(0);
                            v_isShared_873_ = v_isSharedCheck_880_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_881_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_881_, 0, v_x_836_);
                        crate::leanh::lean_ctor_set(v___x_881_, 1, v_x_837_);
                        v___y_853_ = v___x_881_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_854_ = lean_array_fset(v_xs_x27_851_, v_j_843_, v___y_853_);
                crate::leanh::lean_dec(v_j_843_);
                if v_isShared_848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_847_, 0, v___x_854_);
                    v___x_856_ = v___x_847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_857_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
                    v___x_856_ = v_reuseFailAlloc_857_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_856_;
            }
            4 => {
                v___x_863_ = l_Lean_instBEqMVarId_beq(v_x_836_, v_key_858_);
                if v___x_863_ == 0 {
                    crate::leanh::lean_del_object(v___x_861_);
                    v___x_864_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_858_, v_val_859_, v_x_836_, v_x_837_,
                    );
                    v___x_865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_864_);
                    v___y_853_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_859_);
                    crate::leanh::lean_dec(v_key_858_);
                    if v_isShared_862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_861_, 1, v_x_837_);
                        crate::leanh::lean_ctor_set(v___x_861_, 0, v_x_836_);
                        v___x_867_ = v___x_861_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_x_836_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 1, v_x_837_);
                        v___x_867_ = v_reuseFailAlloc_868_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_853_ = v___x_867_;
                state = 2;
                continue;
            }
            6 => {
                v___x_874_ = lean_usize_shift_right(v_x_834_, v___x_839_);
                v___x_875_ = lean_usize_add(v_x_835_, v___x_840_);
                v___x_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_node_870_, v___x_874_, v___x_875_, v_x_836_, v_x_837_);
                if v_isShared_873_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_876_);
                    v___x_878_ = v___x_872_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_853_ = v___x_878_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_888_ == 0 {
                    v___x_890_ = v___x_887_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_904_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_904_, 0, v_ks_884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_904_, 1, v_vs_885_);
                    v___x_890_ = v_reuseFailAlloc_904_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_891_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_890_, v_x_836_, v_x_837_);
                v___x_899_ = 7usize;
                v___x_900_ = lean_usize_dec_le(v___x_899_, v_x_835_);
                if v___x_900_ == 0 {
                    v___x_901_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_891_);
                    v___x_902_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
                    crate::leanh::lean_dec(v___x_901_);
                    v___y_893_ = v___x_903_;
                    state = 10;
                    continue;
                } else {
                    v___y_893_ = v___x_900_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_893_ == 0 {
                    v_ks_894_ = crate::leanh::lean_ctor_get(v_newNode_891_, 0);
                    crate::leanh::lean_inc_ref(v_ks_894_);
                    v_vs_895_ = crate::leanh::lean_ctor_get(v_newNode_891_, 1);
                    crate::leanh::lean_inc_ref(v_vs_895_);
                    crate::leanh::lean_dec_ref(v_newNode_891_);
                    v___x_896_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2);
                    v___x_898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_835_, v_ks_894_, v_vs_895_, v___x_896_, v___x_897_);
                    crate::leanh::lean_dec_ref(v_vs_895_);
                    crate::leanh::lean_dec_ref(v_ks_894_);
                    return v___x_898_;
                } else {
                    return v_newNode_891_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_depth_906_: usize,
    mut v_keys_907_: *mut crate::leanh::LeanObject,
    mut v_vals_908_: *mut crate::leanh::LeanObject,
    mut v_i_909_: *mut crate::leanh::LeanObject,
    mut v_entries_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v_k_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u64 = 0;
    let mut v_h_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: usize = 0;
    let mut v___x_921_: usize = 0;
    let mut v_h_922_: usize = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_911_ = lean_array_get_size(v_keys_907_);
                v___x_912_ = lean_nat_dec_lt(v_i_909_, v___x_911_);
                if v___x_912_ == 0 {
                    crate::leanh::lean_dec(v_i_909_);
                    return v_entries_910_;
                } else {
                    v_k_913_ = lean_array_fget_borrowed(v_keys_907_, v_i_909_);
                    v_v_914_ = lean_array_fget_borrowed(v_vals_908_, v_i_909_);
                    v___x_915_ = l_Lean_instHashableMVarId_hash(v_k_913_);
                    v_h_916_ = lean_uint64_to_usize(v___x_915_);
                    v___x_917_ = 5usize;
                    v___x_918_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_919_ = 1usize;
                    v___x_920_ = lean_usize_sub(v_depth_906_, v___x_919_);
                    v___x_921_ = lean_usize_mul(v___x_917_, v___x_920_);
                    v_h_922_ = lean_usize_shift_right(v_h_916_, v___x_921_);
                    v___x_923_ = lean_nat_add(v_i_909_, v___x_918_);
                    crate::leanh::lean_dec(v_i_909_);
                    crate::leanh::lean_inc(v_v_914_);
                    crate::leanh::lean_inc(v_k_913_);
                    v___x_924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_entries_910_, v_h_922_, v_depth_906_, v_k_913_, v_v_914_);
                    v_i_909_ = v___x_923_;
                    v_entries_910_ = v___x_924_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_depth_926_: *mut crate::leanh::LeanObject,
    mut v_keys_927_: *mut crate::leanh::LeanObject,
    mut v_vals_928_: *mut crate::leanh::LeanObject,
    mut v_i_929_: *mut crate::leanh::LeanObject,
    mut v_entries_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_931_: usize = 0;
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_931_ = crate::leanh::lean_unbox_usize(v_depth_926_);
    crate::leanh::lean_dec(v_depth_926_);
    v_res_932_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_931_, v_keys_927_, v_vals_928_, v_i_929_, v_entries_930_);
    crate::leanh::lean_dec_ref(v_vals_928_);
    crate::leanh::lean_dec_ref(v_keys_927_);
    return v_res_932_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_933_: *mut crate::leanh::LeanObject,
    mut v_x_934_: *mut crate::leanh::LeanObject,
    mut v_x_935_: *mut crate::leanh::LeanObject,
    mut v_x_936_: *mut crate::leanh::LeanObject,
    mut v_x_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3583__boxed_938_: usize = 0;
    let mut v_x_3584__boxed_939_: usize = 0;
    let mut v_res_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3583__boxed_938_ = crate::leanh::lean_unbox_usize(v_x_934_);
    crate::leanh::lean_dec(v_x_934_);
    v_x_3584__boxed_939_ = crate::leanh::lean_unbox_usize(v_x_935_);
    crate::leanh::lean_dec(v_x_935_);
    v_res_940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_933_, v_x_3583__boxed_938_, v_x_3584__boxed_939_, v_x_936_, v_x_937_);
    return v_res_940_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(
    mut v_x_941_: *mut crate::leanh::LeanObject,
    mut v_x_942_: *mut crate::leanh::LeanObject,
    mut v_x_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: u64 = 0;
    let mut v___x_945_: usize = 0;
    let mut v___x_946_: usize = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Lean_instHashableMVarId_hash(v_x_942_);
    v___x_945_ = lean_uint64_to_usize(v___x_944_);
    v___x_946_ = 1usize;
    v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_941_, v___x_945_, v___x_946_, v_x_942_, v_x_943_);
    return v___x_947_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(
    mut v_mvarId_948_: *mut crate::leanh::LeanObject,
    mut v_val_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_960_: u8 = 0;
    let mut v_depth_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_973_: u8 = 0;
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_952_ = lean_st_ref_take(v___y_950_);
                v_mctx_953_ = crate::leanh::lean_ctor_get(v___x_952_, 0);
                v_cache_954_ = crate::leanh::lean_ctor_get(v___x_952_, 1);
                v_zetaDeltaFVarIds_955_ = crate::leanh::lean_ctor_get(v___x_952_, 2);
                v_postponed_956_ = crate::leanh::lean_ctor_get(v___x_952_, 3);
                v_diag_957_ = crate::leanh::lean_ctor_get(v___x_952_, 4);
                v_isSharedCheck_985_ = (!crate::leanh::lean_is_exclusive(v___x_952_)) as u8;
                if v_isSharedCheck_985_ == 0 {
                    v___x_959_ = v___x_952_;
                    v_isShared_960_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_957_);
                    crate::leanh::lean_inc(v_postponed_956_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_955_);
                    crate::leanh::lean_inc(v_cache_954_);
                    crate::leanh::lean_inc(v_mctx_953_);
                    crate::leanh::lean_dec(v___x_952_);
                    v___x_959_ = crate::leanh::lean_box(0);
                    v_isShared_960_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_961_ = crate::leanh::lean_ctor_get(v_mctx_953_, 0);
                v_levelAssignDepth_962_ = crate::leanh::lean_ctor_get(v_mctx_953_, 1);
                v_lmvarCounter_963_ = crate::leanh::lean_ctor_get(v_mctx_953_, 2);
                v_mvarCounter_964_ = crate::leanh::lean_ctor_get(v_mctx_953_, 3);
                v_lDecls_965_ = crate::leanh::lean_ctor_get(v_mctx_953_, 4);
                v_decls_966_ = crate::leanh::lean_ctor_get(v_mctx_953_, 5);
                v_userNames_967_ = crate::leanh::lean_ctor_get(v_mctx_953_, 6);
                v_lAssignment_968_ = crate::leanh::lean_ctor_get(v_mctx_953_, 7);
                v_eAssignment_969_ = crate::leanh::lean_ctor_get(v_mctx_953_, 8);
                v_dAssignment_970_ = crate::leanh::lean_ctor_get(v_mctx_953_, 9);
                v_isSharedCheck_984_ = (!crate::leanh::lean_is_exclusive(v_mctx_953_)) as u8;
                if v_isSharedCheck_984_ == 0 {
                    v___x_972_ = v_mctx_953_;
                    v_isShared_973_ = v_isSharedCheck_984_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_970_);
                    crate::leanh::lean_inc(v_eAssignment_969_);
                    crate::leanh::lean_inc(v_lAssignment_968_);
                    crate::leanh::lean_inc(v_userNames_967_);
                    crate::leanh::lean_inc(v_decls_966_);
                    crate::leanh::lean_inc(v_lDecls_965_);
                    crate::leanh::lean_inc(v_mvarCounter_964_);
                    crate::leanh::lean_inc(v_lmvarCounter_963_);
                    crate::leanh::lean_inc(v_levelAssignDepth_962_);
                    crate::leanh::lean_inc(v_depth_961_);
                    crate::leanh::lean_dec(v_mctx_953_);
                    v___x_972_ = crate::leanh::lean_box(0);
                    v_isShared_973_ = v_isSharedCheck_984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_974_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_eAssignment_969_, v_mvarId_948_, v_val_949_);
                if v_isShared_973_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_972_, 8, v___x_974_);
                    v___x_976_ = v___x_972_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 0, v_depth_961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 1, v_levelAssignDepth_962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 2, v_lmvarCounter_963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 3, v_mvarCounter_964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 4, v_lDecls_965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 5, v_decls_966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 6, v_userNames_967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 7, v_lAssignment_968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 8, v___x_974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 9, v_dAssignment_970_);
                    v___x_976_ = v_reuseFailAlloc_983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_960_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_976_);
                    v___x_978_ = v___x_959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_982_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 1, v_cache_954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 2, v_zetaDeltaFVarIds_955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 3, v_postponed_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 4, v_diag_957_);
                    v___x_978_ = v_reuseFailAlloc_982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_979_ = lean_st_ref_set(v___y_950_, v___x_978_);
                v___x_980_ = crate::leanh::lean_box(0);
                v___x_981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_981_, 0, v___x_980_);
                return v___x_981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg___boxed(
    mut v_mvarId_986_: *mut crate::leanh::LeanObject,
    mut v_val_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_986_, v_val_987_, v___y_988_);
    crate::leanh::lean_dec(v___y_988_);
    return v_res_990_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0;
    v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8;
    v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
    mut v_mvar_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v_arg_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_unused_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_a_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_unused_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvar_1007_);
                v___x_1020_ =
                    l_Lean_MVarId_getType(v_mvar_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
                if crate::leanh::lean_obj_tag(v___x_1020_) == 0 {
                    v_a_1021_ = crate::leanh::lean_ctor_get(v___x_1020_, 0);
                    crate::leanh::lean_inc(v_a_1021_);
                    crate::leanh::lean_dec_ref_known(v___x_1020_, 1);
                    v___x_1022_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_a_1021_, v_a_1009_);
                    v_a_1023_ = crate::leanh::lean_ctor_get(v___x_1022_, 0);
                    crate::leanh::lean_inc(v_a_1023_);
                    crate::leanh::lean_dec_ref(v___x_1022_);
                    v___x_1024_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1023_);
                    crate::leanh::lean_dec(v_a_1023_);
                    if crate::leanh::lean_obj_tag(v___x_1024_) == 1 {
                        v_val_1025_ = crate::leanh::lean_ctor_get(v___x_1024_, 0);
                        crate::leanh::lean_inc(v_val_1025_);
                        crate::leanh::lean_dec_ref_known(v___x_1024_, 1);
                        v_target_1026_ = crate::leanh::lean_ctor_get(v_val_1025_, 3);
                        crate::leanh::lean_inc_ref(v_target_1026_);
                        if crate::leanh::lean_obj_tag(v_target_1026_) == 5 {
                            v_fn_1027_ = crate::leanh::lean_ctor_get(v_target_1026_, 0);
                            crate::leanh::lean_inc_ref(v_fn_1027_);
                            if crate::leanh::lean_obj_tag(v_fn_1027_) == 5 {
                                v_fn_1028_ = crate::leanh::lean_ctor_get(v_fn_1027_, 0);
                                crate::leanh::lean_inc_ref(v_fn_1028_);
                                if crate::leanh::lean_obj_tag(v_fn_1028_) == 5 {
                                    v_fn_1029_ = crate::leanh::lean_ctor_get(v_fn_1028_, 0);
                                    if crate::leanh::lean_obj_tag(v_fn_1029_) == 4 {
                                        v_declName_1030_ =
                                            crate::leanh::lean_ctor_get(v_fn_1029_, 0);
                                        crate::leanh::lean_inc(v_declName_1030_);
                                        if crate::leanh::lean_obj_tag(v_declName_1030_) == 1 {
                                            v_pre_1031_ =
                                                crate::leanh::lean_ctor_get(v_declName_1030_, 0);
                                            crate::leanh::lean_inc(v_pre_1031_);
                                            if crate::leanh::lean_obj_tag(v_pre_1031_) == 1 {
                                                v_pre_1032_ =
                                                    crate::leanh::lean_ctor_get(v_pre_1031_, 0);
                                                crate::leanh::lean_inc(v_pre_1032_);
                                                if crate::leanh::lean_obj_tag(v_pre_1032_) == 1 {
                                                    v_pre_1033_ =
                                                        crate::leanh::lean_ctor_get(v_pre_1032_, 0);
                                                    crate::leanh::lean_inc(v_pre_1033_);
                                                    if crate::leanh::lean_obj_tag(v_pre_1033_) == 1
                                                    {
                                                        v_pre_1034_ = crate::leanh::lean_ctor_get(
                                                            v_pre_1033_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_pre_1034_);
                                                        if crate::leanh::lean_obj_tag(v_pre_1034_)
                                                            == 0
                                                        {
                                                            v_u_1035_ = crate::leanh::lean_ctor_get(
                                                                v_val_1025_,
                                                                0,
                                                            );
                                                            v_00_u03c3s_1036_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_val_1025_,
                                                                    1,
                                                                );
                                                            v_hyps_1037_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_val_1025_,
                                                                    2,
                                                                );
                                                            v_isSharedCheck_1099_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v_val_1025_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1099_ == 0 {
                                                                v_unused_1100_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_val_1025_,
                                                                        3,
                                                                    );
                                                                crate::leanh::lean_dec(
                                                                    v_unused_1100_,
                                                                );
                                                                v___x_1039_ = v_val_1025_;
                                                                v_isShared_1040_ =
                                                                    v_isSharedCheck_1099_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(
                                                                    v_hyps_1037_,
                                                                );
                                                                crate::leanh::lean_inc(
                                                                    v_00_u03c3s_1036_,
                                                                );
                                                                crate::leanh::lean_inc(v_u_1035_);
                                                                crate::leanh::lean_dec(v_val_1025_);
                                                                v___x_1039_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1040_ =
                                                                    v_isSharedCheck_1099_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_pre_1034_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_pre_1033_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_pre_1032_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_pre_1031_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_declName_1030_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fn_1028_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fn_1027_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_target_1026_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec(v_val_1025_);
                                                            crate::leanh::lean_dec(v_mvar_1007_);
                                                            v___y_1014_ = v_a_1008_;
                                                            v___y_1015_ = v_a_1009_;
                                                            v___y_1016_ = v_a_1010_;
                                                            v___y_1017_ = v_a_1011_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_pre_1033_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1032_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1031_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_1030_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_fn_1028_, 2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_fn_1027_, 2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_target_1026_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec(v_val_1025_);
                                                        crate::leanh::lean_dec(v_mvar_1007_);
                                                        v___y_1014_ = v_a_1008_;
                                                        v___y_1015_ = v_a_1009_;
                                                        v___y_1016_ = v_a_1010_;
                                                        v___y_1017_ = v_a_1011_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_pre_1031_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_pre_1032_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_declName_1030_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec_ref_known(v_fn_1028_, 2);
                                                    crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_target_1026_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_val_1025_);
                                                    crate::leanh::lean_dec(v_mvar_1007_);
                                                    v___y_1014_ = v_a_1008_;
                                                    v___y_1015_ = v_a_1009_;
                                                    v___y_1016_ = v_a_1010_;
                                                    v___y_1017_ = v_a_1011_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_pre_1031_);
                                                crate::leanh::lean_dec_ref_known(
                                                    v_declName_1030_,
                                                    2,
                                                );
                                                crate::leanh::lean_dec_ref_known(v_fn_1028_, 2);
                                                crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                                                crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                                                crate::leanh::lean_dec(v_val_1025_);
                                                crate::leanh::lean_dec(v_mvar_1007_);
                                                v___y_1014_ = v_a_1008_;
                                                v___y_1015_ = v_a_1009_;
                                                v___y_1016_ = v_a_1010_;
                                                v___y_1017_ = v_a_1011_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_declName_1030_);
                                            crate::leanh::lean_dec_ref_known(v_fn_1028_, 2);
                                            crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                                            crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                                            crate::leanh::lean_dec(v_val_1025_);
                                            crate::leanh::lean_dec(v_mvar_1007_);
                                            v___y_1014_ = v_a_1008_;
                                            v___y_1015_ = v_a_1009_;
                                            v___y_1016_ = v_a_1010_;
                                            v___y_1017_ = v_a_1011_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_fn_1028_, 2);
                                        crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                                        crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                                        crate::leanh::lean_dec(v_val_1025_);
                                        crate::leanh::lean_dec(v_mvar_1007_);
                                        v___y_1014_ = v_a_1008_;
                                        v___y_1015_ = v_a_1009_;
                                        v___y_1016_ = v_a_1010_;
                                        v___y_1017_ = v_a_1011_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_fn_1028_);
                                    crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                                    crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                                    crate::leanh::lean_dec(v_val_1025_);
                                    crate::leanh::lean_dec(v_mvar_1007_);
                                    v___y_1014_ = v_a_1008_;
                                    v___y_1015_ = v_a_1009_;
                                    v___y_1016_ = v_a_1010_;
                                    v___y_1017_ = v_a_1011_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                                crate::leanh::lean_dec_ref(v_fn_1027_);
                                crate::leanh::lean_dec(v_val_1025_);
                                crate::leanh::lean_dec(v_mvar_1007_);
                                v___y_1014_ = v_a_1008_;
                                v___y_1015_ = v_a_1009_;
                                v___y_1016_ = v_a_1010_;
                                v___y_1017_ = v_a_1011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_target_1026_);
                            crate::leanh::lean_dec(v_val_1025_);
                            crate::leanh::lean_dec(v_mvar_1007_);
                            v___y_1014_ = v_a_1008_;
                            v___y_1015_ = v_a_1009_;
                            v___y_1016_ = v_a_1010_;
                            v___y_1017_ = v_a_1011_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1024_);
                        crate::leanh::lean_dec(v_mvar_1007_);
                        v___x_1101_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9,
                        );
                        v___x_1102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_1101_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
                        return v___x_1102_;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvar_1007_);
                    v_a_1103_ = crate::leanh::lean_ctor_get(v___x_1020_, 0);
                    v_isSharedCheck_1110_ = (!crate::leanh::lean_is_exclusive(v___x_1020_)) as u8;
                    if v_isSharedCheck_1110_ == 0 {
                        v___x_1105_ = v___x_1020_;
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1103_);
                        crate::leanh::lean_dec(v___x_1020_);
                        v___x_1105_ = crate::leanh::lean_box(0);
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1018_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1,
                );
                v___x_1019_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_1018_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
                return v___x_1019_;
            }
            2 => {
                v_arg_1041_ = crate::leanh::lean_ctor_get(v_target_1026_, 1);
                crate::leanh::lean_inc_ref(v_arg_1041_);
                crate::leanh::lean_dec_ref_known(v_target_1026_, 2);
                v_arg_1042_ = crate::leanh::lean_ctor_get(v_fn_1027_, 1);
                crate::leanh::lean_inc_ref(v_arg_1042_);
                crate::leanh::lean_dec_ref_known(v_fn_1027_, 2);
                v_arg_1043_ = crate::leanh::lean_ctor_get(v_fn_1028_, 1);
                crate::leanh::lean_inc_ref(v_arg_1043_);
                crate::leanh::lean_dec_ref_known(v_fn_1028_, 2);
                v_str_1044_ = crate::leanh::lean_ctor_get(v_declName_1030_, 1);
                crate::leanh::lean_inc_ref(v_str_1044_);
                crate::leanh::lean_dec_ref_known(v_declName_1030_, 2);
                v_str_1045_ = crate::leanh::lean_ctor_get(v_pre_1031_, 1);
                crate::leanh::lean_inc_ref(v_str_1045_);
                crate::leanh::lean_dec_ref_known(v_pre_1031_, 2);
                v_str_1046_ = crate::leanh::lean_ctor_get(v_pre_1032_, 1);
                crate::leanh::lean_inc_ref(v_str_1046_);
                crate::leanh::lean_dec_ref_known(v_pre_1032_, 2);
                v_str_1047_ = crate::leanh::lean_ctor_get(v_pre_1033_, 1);
                crate::leanh::lean_inc_ref(v_str_1047_);
                crate::leanh::lean_dec_ref_known(v_pre_1033_, 2);
                v___x_1048_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2;
                v___x_1049_ = lean_string_dec_eq(v_str_1047_, v___x_1048_);
                crate::leanh::lean_dec_ref(v_str_1047_);
                if v___x_1049_ == 0 {
                    crate::leanh::lean_dec_ref(v_str_1046_);
                    crate::leanh::lean_dec_ref(v_str_1045_);
                    crate::leanh::lean_dec_ref(v_str_1044_);
                    crate::leanh::lean_dec_ref(v_arg_1043_);
                    crate::leanh::lean_dec_ref(v_arg_1042_);
                    crate::leanh::lean_dec_ref(v_arg_1041_);
                    crate::leanh::lean_del_object(v___x_1039_);
                    crate::leanh::lean_dec_ref(v_hyps_1037_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1036_);
                    crate::leanh::lean_dec(v_u_1035_);
                    crate::leanh::lean_dec(v_mvar_1007_);
                    v___y_1014_ = v_a_1008_;
                    v___y_1015_ = v_a_1009_;
                    v___y_1016_ = v_a_1010_;
                    v___y_1017_ = v_a_1011_;
                    state = 1;
                    continue;
                } else {
                    v___x_1050_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3;
                    v___x_1051_ = lean_string_dec_eq(v_str_1046_, v___x_1050_);
                    crate::leanh::lean_dec_ref(v_str_1046_);
                    if v___x_1051_ == 0 {
                        crate::leanh::lean_dec_ref(v_str_1045_);
                        crate::leanh::lean_dec_ref(v_str_1044_);
                        crate::leanh::lean_dec_ref(v_arg_1043_);
                        crate::leanh::lean_dec_ref(v_arg_1042_);
                        crate::leanh::lean_dec_ref(v_arg_1041_);
                        crate::leanh::lean_del_object(v___x_1039_);
                        crate::leanh::lean_dec_ref(v_hyps_1037_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_1036_);
                        crate::leanh::lean_dec(v_u_1035_);
                        crate::leanh::lean_dec(v_mvar_1007_);
                        v___y_1014_ = v_a_1008_;
                        v___y_1015_ = v_a_1009_;
                        v___y_1016_ = v_a_1010_;
                        v___y_1017_ = v_a_1011_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1052_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4;
                        v___x_1053_ = lean_string_dec_eq(v_str_1045_, v___x_1052_);
                        crate::leanh::lean_dec_ref(v_str_1045_);
                        if v___x_1053_ == 0 {
                            crate::leanh::lean_dec_ref(v_str_1044_);
                            crate::leanh::lean_dec_ref(v_arg_1043_);
                            crate::leanh::lean_dec_ref(v_arg_1042_);
                            crate::leanh::lean_dec_ref(v_arg_1041_);
                            crate::leanh::lean_del_object(v___x_1039_);
                            crate::leanh::lean_dec_ref(v_hyps_1037_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_1036_);
                            crate::leanh::lean_dec(v_u_1035_);
                            crate::leanh::lean_dec(v_mvar_1007_);
                            v___y_1014_ = v_a_1008_;
                            v___y_1015_ = v_a_1009_;
                            v___y_1016_ = v_a_1010_;
                            v___y_1017_ = v_a_1011_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1054_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5;
                            v___x_1055_ = lean_string_dec_eq(v_str_1044_, v___x_1054_);
                            crate::leanh::lean_dec_ref(v_str_1044_);
                            if v___x_1055_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_1043_);
                                crate::leanh::lean_dec_ref(v_arg_1042_);
                                crate::leanh::lean_dec_ref(v_arg_1041_);
                                crate::leanh::lean_del_object(v___x_1039_);
                                crate::leanh::lean_dec_ref(v_hyps_1037_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_1036_);
                                crate::leanh::lean_dec(v_u_1035_);
                                crate::leanh::lean_dec(v_mvar_1007_);
                                v___y_1014_ = v_a_1008_;
                                v___y_1015_ = v_a_1009_;
                                v___y_1016_ = v_a_1010_;
                                v___y_1017_ = v_a_1011_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_arg_1042_);
                                crate::leanh::lean_inc_ref(v_hyps_1037_);
                                crate::leanh::lean_inc_ref(v_00_u03c3s_1036_);
                                crate::leanh::lean_inc(v_u_1035_);
                                if v_isShared_1040_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1039_, 3, v_arg_1042_);
                                    v___x_1057_ = v___x_1039_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1098_ =
                                        crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1098_,
                                        0,
                                        v_u_1035_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1098_,
                                        1,
                                        v_00_u03c3s_1036_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1098_,
                                        2,
                                        v_hyps_1037_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1098_,
                                        3,
                                        v_arg_1042_,
                                    );
                                    v___x_1057_ = v_reuseFailAlloc_1098_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1058_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1057_);
                v___x_1059_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1058_,
                    v_pre_1034_,
                    v_a_1008_,
                    v_a_1009_,
                    v_a_1010_,
                    v_a_1011_,
                );
                if crate::leanh::lean_obj_tag(v___x_1059_) == 0 {
                    v_a_1060_ = crate::leanh::lean_ctor_get(v___x_1059_, 0);
                    crate::leanh::lean_inc(v_a_1060_);
                    crate::leanh::lean_dec_ref_known(v___x_1059_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1041_);
                    crate::leanh::lean_inc_ref(v_hyps_1037_);
                    crate::leanh::lean_inc(v_u_1035_);
                    v___x_1061_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1061_, 0, v_u_1035_);
                    crate::leanh::lean_ctor_set(v___x_1061_, 1, v_00_u03c3s_1036_);
                    crate::leanh::lean_ctor_set(v___x_1061_, 2, v_hyps_1037_);
                    crate::leanh::lean_ctor_set(v___x_1061_, 3, v_arg_1041_);
                    v___x_1062_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1061_);
                    v___x_1063_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1062_,
                        v_pre_1034_,
                        v_a_1008_,
                        v_a_1009_,
                        v_a_1010_,
                        v_a_1011_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1063_) == 0 {
                        v_a_1064_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                        crate::leanh::lean_inc_n(v_a_1064_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1063_, 1);
                        v___x_1065_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7;
                        v___x_1066_ = crate::leanh::lean_box(0);
                        v___x_1067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1067_, 0, v_u_1035_);
                        crate::leanh::lean_ctor_set(v___x_1067_, 1, v___x_1066_);
                        v___x_1068_ = l_Lean_mkConst(v___x_1065_, v___x_1067_);
                        crate::leanh::lean_inc(v_a_1060_);
                        v___x_1069_ = l_Lean_mkApp6(
                            v___x_1068_,
                            v_arg_1043_,
                            v_hyps_1037_,
                            v_arg_1042_,
                            v_arg_1041_,
                            v_a_1060_,
                            v_a_1064_,
                        );
                        v___x_1070_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvar_1007_, v___x_1069_, v_a_1009_);
                        v_isSharedCheck_1080_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1070_)) as u8;
                        if v_isSharedCheck_1080_ == 0 {
                            v_unused_1081_ = crate::leanh::lean_ctor_get(v___x_1070_, 0);
                            crate::leanh::lean_dec(v_unused_1081_);
                            v___x_1072_ = v___x_1070_;
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1070_);
                            v___x_1072_ = crate::leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1060_);
                        crate::leanh::lean_dec_ref(v_arg_1043_);
                        crate::leanh::lean_dec_ref(v_arg_1042_);
                        crate::leanh::lean_dec_ref(v_arg_1041_);
                        crate::leanh::lean_dec_ref(v_hyps_1037_);
                        crate::leanh::lean_dec(v_u_1035_);
                        crate::leanh::lean_dec(v_mvar_1007_);
                        v_a_1082_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                        v_isSharedCheck_1089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1063_)) as u8;
                        if v_isSharedCheck_1089_ == 0 {
                            v___x_1084_ = v___x_1063_;
                            v_isShared_1085_ = v_isSharedCheck_1089_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1082_);
                            crate::leanh::lean_dec(v___x_1063_);
                            v___x_1084_ = crate::leanh::lean_box(0);
                            v_isShared_1085_ = v_isSharedCheck_1089_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_1043_);
                    crate::leanh::lean_dec_ref(v_arg_1042_);
                    crate::leanh::lean_dec_ref(v_arg_1041_);
                    crate::leanh::lean_dec_ref(v_hyps_1037_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1036_);
                    crate::leanh::lean_dec(v_u_1035_);
                    crate::leanh::lean_dec(v_mvar_1007_);
                    v_a_1090_ = crate::leanh::lean_ctor_get(v___x_1059_, 0);
                    v_isSharedCheck_1097_ = (!crate::leanh::lean_is_exclusive(v___x_1059_)) as u8;
                    if v_isSharedCheck_1097_ == 0 {
                        v___x_1092_ = v___x_1059_;
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1090_);
                        crate::leanh::lean_dec(v___x_1059_);
                        v___x_1092_ = crate::leanh::lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1074_ = l_Lean_Expr_mvarId_x21(v_a_1060_);
                crate::leanh::lean_dec(v_a_1060_);
                v___x_1075_ = l_Lean_Expr_mvarId_x21(v_a_1064_);
                crate::leanh::lean_dec(v_a_1064_);
                v___x_1076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1076_, 0, v___x_1074_);
                crate::leanh::lean_ctor_set(v___x_1076_, 1, v___x_1075_);
                if v_isShared_1073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1076_);
                    v___x_1078_ = v___x_1072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1078_;
            }
            6 => {
                if v_isShared_1085_ == 0 {
                    v___x_1087_ = v___x_1084_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
                    v___x_1087_ = v_reuseFailAlloc_1088_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1087_;
            }
            8 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1095_;
            }
            10 => {
                if v_isShared_1106_ == 0 {
                    v___x_1108_ = v___x_1105_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
                    v___x_1108_ = v_reuseFailAlloc_1109_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___boxed(
    mut v_mvar_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
        v_mvar_1111_,
        v_a_1112_,
        v_a_1113_,
        v_a_1114_,
        v_a_1115_,
    );
    crate::leanh::lean_dec(v_a_1115_);
    crate::leanh::lean_dec_ref(v_a_1114_);
    crate::leanh::lean_dec(v_a_1113_);
    crate::leanh::lean_dec_ref(v_a_1112_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(
    mut v_00_u03b1_1118_: *mut crate::leanh::LeanObject,
    mut v_msg_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
            v_msg_1119_,
            v___y_1120_,
            v___y_1121_,
            v___y_1122_,
            v___y_1123_,
        );
    return v___x_1125_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___boxed(
    mut v_00_u03b1_1126_: *mut crate::leanh::LeanObject,
    mut v_msg_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(
        v_00_u03b1_1126_,
        v_msg_1127_,
        v___y_1128_,
        v___y_1129_,
        v___y_1130_,
        v___y_1131_,
    );
    crate::leanh::lean_dec(v___y_1131_);
    crate::leanh::lean_dec_ref(v___y_1130_);
    crate::leanh::lean_dec(v___y_1129_);
    crate::leanh::lean_dec_ref(v___y_1128_);
    return v_res_1133_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(
    mut v_mvarId_1134_: *mut crate::leanh::LeanObject,
    mut v_val_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_1134_, v_val_1135_, v___y_1137_);
    return v___x_1141_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___boxed(
    mut v_mvarId_1142_: *mut crate::leanh::LeanObject,
    mut v_val_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(
            v_mvarId_1142_,
            v_val_1143_,
            v___y_1144_,
            v___y_1145_,
            v___y_1146_,
            v___y_1147_,
        );
    crate::leanh::lean_dec(v___y_1147_);
    crate::leanh::lean_dec_ref(v___y_1146_);
    crate::leanh::lean_dec(v___y_1145_);
    crate::leanh::lean_dec_ref(v___y_1144_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3(
    mut v_00_u03b2_1150_: *mut crate::leanh::LeanObject,
    mut v_x_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_x_1151_, v_x_1152_, v_x_1153_);
    return v___x_1154_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1155_: *mut crate::leanh::LeanObject,
    mut v_x_1156_: *mut crate::leanh::LeanObject,
    mut v_x_1157_: usize,
    mut v_x_1158_: usize,
    mut v_x_1159_: *mut crate::leanh::LeanObject,
    mut v_x_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_1156_, v_x_1157_, v_x_1158_, v_x_1159_, v_x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1162_: *mut crate::leanh::LeanObject,
    mut v_x_1163_: *mut crate::leanh::LeanObject,
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v_x_1165_: *mut crate::leanh::LeanObject,
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4087__boxed_1168_: usize = 0;
    let mut v_x_4088__boxed_1169_: usize = 0;
    let mut v_res_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4087__boxed_1168_ = crate::leanh::lean_unbox_usize(v_x_1164_);
    crate::leanh::lean_dec(v_x_1164_);
    v_x_4088__boxed_1169_ = crate::leanh::lean_unbox_usize(v_x_1165_);
    crate::leanh::lean_dec(v_x_1165_);
    v_res_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(v_00_u03b2_1162_, v_x_1163_, v_x_4087__boxed_1168_, v_x_4088__boxed_1169_, v_x_1166_, v_x_1167_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1171_: *mut crate::leanh::LeanObject,
    mut v_n_1172_: *mut crate::leanh::LeanObject,
    mut v_k_1173_: *mut crate::leanh::LeanObject,
    mut v_v_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1172_, v_k_1173_, v_v_1174_);
    return v___x_1175_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1176_: *mut crate::leanh::LeanObject,
    mut v_depth_1177_: usize,
    mut v_keys_1178_: *mut crate::leanh::LeanObject,
    mut v_vals_1179_: *mut crate::leanh::LeanObject,
    mut v_heq_1180_: *mut crate::leanh::LeanObject,
    mut v_i_1181_: *mut crate::leanh::LeanObject,
    mut v_entries_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_1177_, v_keys_1178_, v_vals_1179_, v_i_1181_, v_entries_1182_);
    return v___x_1183_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_1184_: *mut crate::leanh::LeanObject,
    mut v_depth_1185_: *mut crate::leanh::LeanObject,
    mut v_keys_1186_: *mut crate::leanh::LeanObject,
    mut v_vals_1187_: *mut crate::leanh::LeanObject,
    mut v_heq_1188_: *mut crate::leanh::LeanObject,
    mut v_i_1189_: *mut crate::leanh::LeanObject,
    mut v_entries_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1191_: usize = 0;
    let mut v_res_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1191_ = crate::leanh::lean_unbox_usize(v_depth_1185_);
    crate::leanh::lean_dec(v_depth_1185_);
    v_res_1192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_1184_, v_depth_boxed_1191_, v_keys_1186_, v_vals_1187_, v_heq_1188_, v_i_1189_, v_entries_1190_);
    crate::leanh::lean_dec_ref(v_vals_1187_);
    crate::leanh::lean_dec_ref(v_keys_1186_);
    return v_res_1192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1193_: *mut crate::leanh::LeanObject,
    mut v_x_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v_x_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_1194_, v_x_1195_, v_x_1196_, v_x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(
    mut v_x_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1203_);
    crate::leanh::lean_inc_ref(v___y_1202_);
    crate::leanh::lean_inc(v___y_1201_);
    crate::leanh::lean_inc_ref(v___y_1200_);
    v___x_1209_ = crate::leanh::lean_apply_9(
        v_x_1199_,
        v___y_1200_,
        v___y_1201_,
        v___y_1202_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
        v___y_1206_,
        v___y_1207_,
        crate::leanh::lean_box(0),
    );
    return v___x_1209_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed(
    mut v_x_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    crate::leanh::lean_dec(v___y_1212_);
    crate::leanh::lean_dec_ref(v___y_1211_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(
    mut v_mvarId_1221_: *mut crate::leanh::LeanObject,
    mut v_x_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1226_);
                crate::leanh::lean_inc_ref(v___y_1225_);
                crate::leanh::lean_inc(v___y_1224_);
                crate::leanh::lean_inc_ref(v___y_1223_);
                v___f_1232_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1232_, 0, v_x_1222_);
                crate::leanh::lean_closure_set(v___f_1232_, 1, v___y_1223_);
                crate::leanh::lean_closure_set(v___f_1232_, 2, v___y_1224_);
                crate::leanh::lean_closure_set(v___f_1232_, 3, v___y_1225_);
                crate::leanh::lean_closure_set(v___f_1232_, 4, v___y_1226_);
                v___x_1233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1221_,
                    v___f_1232_,
                    v___y_1227_,
                    v___y_1228_,
                    v___y_1229_,
                    v___y_1230_,
                );
                if crate::leanh::lean_obj_tag(v___x_1233_) == 0 {
                    return v___x_1233_;
                } else {
                    v_a_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                    v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v___x_1233_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1236_ = v___x_1233_;
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1234_);
                        crate::leanh::lean_dec(v___x_1233_);
                        v___x_1236_ = crate::leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___boxed(
    mut v_mvarId_1242_: *mut crate::leanh::LeanObject,
    mut v_x_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1253_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_1242_, v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
    crate::leanh::lean_dec(v___y_1251_);
    crate::leanh::lean_dec_ref(v___y_1250_);
    crate::leanh::lean_dec(v___y_1249_);
    crate::leanh::lean_dec_ref(v___y_1248_);
    crate::leanh::lean_dec(v___y_1247_);
    crate::leanh::lean_dec_ref(v___y_1246_);
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec_ref(v___y_1244_);
    return v_res_1253_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(
    mut v_00_u03b1_1254_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1255_: *mut crate::leanh::LeanObject,
    mut v_x_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_1255_, v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
    return v___x_1266_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___boxed(
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(
            v_00_u03b1_1267_,
            v_mvarId_1268_,
            v_x_1269_,
            v___y_1270_,
            v___y_1271_,
            v___y_1272_,
            v___y_1273_,
            v___y_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
        );
    crate::leanh::lean_dec(v___y_1277_);
    crate::leanh::lean_dec_ref(v___y_1276_);
    crate::leanh::lean_dec(v___y_1275_);
    crate::leanh::lean_dec_ref(v___y_1274_);
    crate::leanh::lean_dec(v___y_1273_);
    crate::leanh::lean_dec_ref(v___y_1272_);
    crate::leanh::lean_dec(v___y_1271_);
    crate::leanh::lean_dec_ref(v___y_1270_);
    return v_res_1279_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
    mut v___y_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
    mut v___y_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_a_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
                    v_a_1280_,
                    v___y_1285_,
                    v___y_1286_,
                    v___y_1287_,
                    v___y_1288_,
                );
                if crate::leanh::lean_obj_tag(v___x_1290_) == 0 {
                    v_a_1291_ = crate::leanh::lean_ctor_get(v___x_1290_, 0);
                    crate::leanh::lean_inc(v_a_1291_);
                    crate::leanh::lean_dec_ref_known(v___x_1290_, 1);
                    v_fst_1292_ = crate::leanh::lean_ctor_get(v_a_1291_, 0);
                    v_snd_1293_ = crate::leanh::lean_ctor_get(v_a_1291_, 1);
                    v_isSharedCheck_1303_ = (!crate::leanh::lean_is_exclusive(v_a_1291_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v___x_1295_ = v_a_1291_;
                        v_isShared_1296_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1293_);
                        crate::leanh::lean_inc(v_fst_1292_);
                        crate::leanh::lean_dec(v_a_1291_);
                        v___x_1295_ = crate::leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1304_ = crate::leanh::lean_ctor_get(v___x_1290_, 0);
                    v_isSharedCheck_1311_ = (!crate::leanh::lean_is_exclusive(v___x_1290_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1306_ = v___x_1290_;
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1304_);
                        crate::leanh::lean_dec(v___x_1290_);
                        v___x_1306_ = crate::leanh::lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1297_ = crate::leanh::lean_box(0);
                if v_isShared_1296_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1295_, 1);
                    crate::leanh::lean_ctor_set(v___x_1295_, 1, v___x_1297_);
                    crate::leanh::lean_ctor_set(v___x_1295_, 0, v_snd_1293_);
                    v___x_1299_ = v___x_1295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_snd_1293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1297_);
                    v___x_1299_ = v_reuseFailAlloc_1302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1300_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1300_, 0, v_fst_1292_);
                crate::leanh::lean_ctor_set(v___x_1300_, 1, v___x_1299_);
                v___x_1301_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_1300_,
                    v___y_1282_,
                    v___y_1285_,
                    v___y_1286_,
                    v___y_1287_,
                    v___y_1288_,
                );
                return v___x_1301_;
            }
            3 => {
                if v_isShared_1307_ == 0 {
                    v___x_1309_ = v___x_1306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed(
    mut v_a_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(
        v_a_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
    );
    crate::leanh::lean_dec(v___y_1320_);
    crate::leanh::lean_dec_ref(v___y_1319_);
    crate::leanh::lean_dec(v___y_1318_);
    crate::leanh::lean_dec_ref(v___y_1317_);
    crate::leanh::lean_dec(v___y_1316_);
    crate::leanh::lean_dec_ref(v___y_1315_);
    crate::leanh::lean_dec(v___y_1314_);
    crate::leanh::lean_dec_ref(v___y_1313_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
    mut v_a_1329_: *mut crate::leanh::LeanObject,
    mut v_a_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1332_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1324_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_,
                );
                if crate::leanh::lean_obj_tag(v___x_1332_) == 0 {
                    v_a_1333_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                    crate::leanh::lean_inc_n(v_a_1333_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1332_, 1);
                    v___f_1334_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1334_, 0, v_a_1333_);
                    v___x_1335_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_a_1333_, v___f_1334_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
                    return v___x_1335_;
                } else {
                    v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                    v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1338_ = v___x_1332_;
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1336_);
                        crate::leanh::lean_dec(v___x_1332_);
                        v___x_1338_ = crate::leanh::lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___boxed(
    mut v_a_1344_: *mut crate::leanh::LeanObject,
    mut v_a_1345_: *mut crate::leanh::LeanObject,
    mut v_a_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_a_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
    mut v_a_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1353_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
        v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_,
    );
    crate::leanh::lean_dec(v_a_1351_);
    crate::leanh::lean_dec_ref(v_a_1350_);
    crate::leanh::lean_dec(v_a_1349_);
    crate::leanh::lean_dec_ref(v_a_1348_);
    crate::leanh::lean_dec(v_a_1347_);
    crate::leanh::lean_dec_ref(v_a_1346_);
    crate::leanh::lean_dec(v_a_1345_);
    crate::leanh::lean_dec_ref(v_a_1344_);
    return v_res_1353_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(
    mut v_x_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
        v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_,
    );
    return v___x_1364_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed(
    mut v_x_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
    mut v_a_1371_: *mut crate::leanh::LeanObject,
    mut v_a_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(
        v_x_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_,
        v_a_1373_,
    );
    crate::leanh::lean_dec(v_a_1373_);
    crate::leanh::lean_dec_ref(v_a_1372_);
    crate::leanh::lean_dec(v_a_1371_);
    crate::leanh::lean_dec_ref(v_a_1370_);
    crate::leanh::lean_dec(v_a_1369_);
    crate::leanh::lean_dec_ref(v_a_1368_);
    crate::leanh::lean_dec(v_a_1367_);
    crate::leanh::lean_dec_ref(v_a_1366_);
    crate::leanh::lean_dec(v_x_1365_);
    return v_res_1375_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1397_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4;
    v___x_1398_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8;
    v___x_1399_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1400_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1396_,
        v___x_1397_,
        v___x_1398_,
        v___x_1399_,
    );
    return v___x_1400_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(
    mut v_a_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
    return v_res_1402_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(
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
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
}
