// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.LeftRight
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
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
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp5, l_Lean_mkConst,
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
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 83, 80, 114, 101, 100,
        46, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5_value:
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
    m_data: [111, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value:
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
    m_data: [111, 114, 95, 105, 110, 116, 114, 111, 95, 108, 39, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value)
            as *mut leanh::LeanObject,
        1202395330367735780 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value:
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
    m_data: [111, 114, 95, 105, 110, 116, 114, 111, 95, 114, 39, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value)
            as *mut leanh::LeanObject,
        11171667744829353048 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
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
        110, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value) as *mut leanh::LeanObject,2178903791838909049 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value) as *mut leanh::LeanObject,18257750338902299769 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value) as *mut leanh::LeanObject,2331578203406103374 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value) as *mut leanh::LeanObject,17324181706230996700 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(
    mut v_e_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_791_: u8 = 0;
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_unused_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_777_ = l_Lean_Expr_hasMVar(v_e_774_);
                if v___x_777_ == 0 {
                    v___x_778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_778_, 0, v_e_774_);
                    return v___x_778_;
                } else {
                    v___x_779_ = lean_st_ref_get(v___y_775_);
                    v_mctx_780_ = leanh::lean_ctor_get(v___x_779_, 0);
                    leanh::lean_inc_ref(v_mctx_780_);
                    leanh::lean_dec(v___x_779_);
                    v___x_781_ = l_Lean_instantiateMVarsCore(v_mctx_780_, v_e_774_);
                    v_fst_782_ = leanh::lean_ctor_get(v___x_781_, 0);
                    leanh::lean_inc(v_fst_782_);
                    v_snd_783_ = leanh::lean_ctor_get(v___x_781_, 1);
                    leanh::lean_inc(v_snd_783_);
                    leanh::lean_dec_ref(v___x_781_);
                    v___x_784_ = lean_st_ref_take(v___y_775_);
                    v_cache_785_ = leanh::lean_ctor_get(v___x_784_, 1);
                    v_zetaDeltaFVarIds_786_ = leanh::lean_ctor_get(v___x_784_, 2);
                    v_postponed_787_ = leanh::lean_ctor_get(v___x_784_, 3);
                    v_diag_788_ = leanh::lean_ctor_get(v___x_784_, 4);
                    v_isSharedCheck_797_ = (!leanh::lean_is_exclusive(v___x_784_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v_unused_798_ = leanh::lean_ctor_get(v___x_784_, 0);
                        leanh::lean_dec(v_unused_798_);
                        v___x_790_ = v___x_784_;
                        v_isShared_791_ = v_isSharedCheck_797_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_788_);
                        leanh::lean_inc(v_postponed_787_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_786_);
                        leanh::lean_inc(v_cache_785_);
                        leanh::lean_dec(v___x_784_);
                        v___x_790_ = leanh::lean_box(0);
                        v_isShared_791_ = v_isSharedCheck_797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_791_ == 0 {
                    leanh::lean_ctor_set(v___x_790_, 0, v_snd_783_);
                    v___x_793_ = v___x_790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_snd_783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 1, v_cache_785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 2, v_zetaDeltaFVarIds_786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 3, v_postponed_787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 4, v_diag_788_);
                    v___x_793_ = v_reuseFailAlloc_796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_794_ = lean_st_ref_set(v___y_775_, v___x_793_);
                v___x_795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_795_, 0, v_fst_782_);
                return v___x_795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg___boxed(
    mut v_e_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_799_, v___y_800_);
    leanh::lean_dec(v___y_800_);
    return v_res_802_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(
    mut v_e_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
    mut v___y_805_: *mut leanh::LeanObject,
    mut v___y_806_: *mut leanh::LeanObject,
    mut v___y_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_803_, v___y_805_);
    return v___x_809_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___boxed(
    mut v_e_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
    mut v___y_813_: *mut leanh::LeanObject,
    mut v___y_814_: *mut leanh::LeanObject,
    mut v___y_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(
            v_e_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_,
        );
    leanh::lean_dec(v___y_814_);
    leanh::lean_dec_ref(v___y_813_);
    leanh::lean_dec(v___y_812_);
    leanh::lean_dec_ref(v___y_811_);
    return v_res_816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_x_817_: *mut leanh::LeanObject,
    mut v_x_818_: *mut leanh::LeanObject,
    mut v_x_819_: *mut leanh::LeanObject,
    mut v_x_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_825_: u8 = 0;
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_821_ = leanh::lean_ctor_get(v_x_817_, 0);
                v_vs_822_ = leanh::lean_ctor_get(v_x_817_, 1);
                v_isSharedCheck_846_ = (!leanh::lean_is_exclusive(v_x_817_)) as u8;
                if v_isSharedCheck_846_ == 0 {
                    v___x_824_ = v_x_817_;
                    v_isShared_825_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_822_);
                    leanh::lean_inc(v_ks_821_);
                    leanh::lean_dec(v_x_817_);
                    v___x_824_ = leanh::lean_box(0);
                    v_isShared_825_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_826_ = lean_array_get_size(v_ks_821_);
                v___x_827_ = lean_nat_dec_lt(v_x_818_, v___x_826_);
                if v___x_827_ == 0 {
                    leanh::lean_dec(v_x_818_);
                    v___x_828_ = lean_array_push(v_ks_821_, v_x_819_);
                    v___x_829_ = lean_array_push(v_vs_822_, v_x_820_);
                    if v_isShared_825_ == 0 {
                        leanh::lean_ctor_set(v___x_824_, 1, v___x_829_);
                        leanh::lean_ctor_set(v___x_824_, 0, v___x_828_);
                        v___x_831_ = v___x_824_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_832_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
                        v___x_831_ = v_reuseFailAlloc_832_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_833_ = lean_array_fget_borrowed(v_ks_821_, v_x_818_);
                    v___x_834_ = l_Lean_instBEqMVarId_beq(v_x_819_, v_k_x27_833_);
                    if v___x_834_ == 0 {
                        if v_isShared_825_ == 0 {
                            v___x_836_ = v___x_824_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_840_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_840_, 0, v_ks_821_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_840_, 1, v_vs_822_);
                            v___x_836_ = v_reuseFailAlloc_840_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_841_ = lean_array_fset(v_ks_821_, v_x_818_, v_x_819_);
                        v___x_842_ = lean_array_fset(v_vs_822_, v_x_818_, v_x_820_);
                        leanh::lean_dec(v_x_818_);
                        if v_isShared_825_ == 0 {
                            leanh::lean_ctor_set(v___x_824_, 1, v___x_842_);
                            leanh::lean_ctor_set(v___x_824_, 0, v___x_841_);
                            v___x_844_ = v___x_824_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_845_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_841_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_842_);
                            v___x_844_ = v_reuseFailAlloc_845_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_831_;
            }
            3 => {
                v___x_837_ = leanh::lean_unsigned_to_nat(1);
                v___x_838_ = lean_nat_add(v_x_818_, v___x_837_);
                leanh::lean_dec(v_x_818_);
                v_x_817_ = v___x_836_;
                v_x_818_ = v___x_838_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_n_847_: *mut leanh::LeanObject,
    mut v_k_848_: *mut leanh::LeanObject,
    mut v_v_849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = leanh::lean_unsigned_to_nat(0);
    v___x_851_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_847_, v___x_850_, v_k_848_, v_v_849_);
    return v___x_851_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_852_: usize = 0;
    let mut v___x_853_: usize = 0;
    let mut v___x_854_: usize = 0;
    v___x_852_ = 5usize;
    v___x_853_ = 1usize;
    v___x_854_ = lean_usize_shift_left(v___x_853_, v___x_852_);
    return v___x_854_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_855_: usize = 0;
    let mut v___x_856_: usize = 0;
    let mut v___x_857_: usize = 0;
    v___x_855_ = 1usize;
    v___x_856_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_857_ = lean_usize_sub(v___x_856_, v___x_855_);
    return v___x_857_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_858_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(
    mut v_x_859_: *mut leanh::LeanObject,
    mut v_x_860_: usize,
    mut v_x_861_: usize,
    mut v_x_862_: *mut leanh::LeanObject,
    mut v_x_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: usize = 0;
    let mut v___x_866_: usize = 0;
    let mut v___x_867_: usize = 0;
    let mut v___x_868_: usize = 0;
    let mut v_j_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v_v_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_node_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_901_: usize = 0;
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_906_: u8 = 0;
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_919_: u8 = 0;
    let mut v_ks_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: u8 = 0;
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v_reuseFailAlloc_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_859_) == 0 {
                    v_es_864_ = leanh::lean_ctor_get(v_x_859_, 0);
                    v___x_865_ = 5usize;
                    v___x_866_ = 1usize;
                    v___x_867_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_868_ = lean_usize_land(v_x_860_, v___x_867_);
                    v_j_869_ = lean_usize_to_nat(v___x_868_);
                    v___x_870_ = lean_array_get_size(v_es_864_);
                    v___x_871_ = lean_nat_dec_lt(v_j_869_, v___x_870_);
                    if v___x_871_ == 0 {
                        leanh::lean_dec(v_j_869_);
                        leanh::lean_dec(v_x_863_);
                        leanh::lean_dec(v_x_862_);
                        return v_x_859_;
                    } else {
                        leanh::lean_inc_ref(v_es_864_);
                        v_isSharedCheck_908_ = (!leanh::lean_is_exclusive(v_x_859_)) as u8;
                        if v_isSharedCheck_908_ == 0 {
                            v_unused_909_ = leanh::lean_ctor_get(v_x_859_, 0);
                            leanh::lean_dec(v_unused_909_);
                            v___x_873_ = v_x_859_;
                            v_isShared_874_ = v_isSharedCheck_908_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_859_);
                            v___x_873_ = leanh::lean_box(0);
                            v_isShared_874_ = v_isSharedCheck_908_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_910_ = leanh::lean_ctor_get(v_x_859_, 0);
                    v_vs_911_ = leanh::lean_ctor_get(v_x_859_, 1);
                    v_isSharedCheck_931_ = (!leanh::lean_is_exclusive(v_x_859_)) as u8;
                    if v_isSharedCheck_931_ == 0 {
                        v___x_913_ = v_x_859_;
                        v_isShared_914_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_911_);
                        leanh::lean_inc(v_ks_910_);
                        leanh::lean_dec(v_x_859_);
                        v___x_913_ = leanh::lean_box(0);
                        v_isShared_914_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_875_ = lean_array_fget(v_es_864_, v_j_869_);
                v___x_876_ = leanh::lean_box(0);
                v_xs_x27_877_ = lean_array_fset(v_es_864_, v_j_869_, v___x_876_);
                match leanh::lean_obj_tag(v_v_875_) {
                    0 => {
                        v_key_884_ = leanh::lean_ctor_get(v_v_875_, 0);
                        v_val_885_ = leanh::lean_ctor_get(v_v_875_, 1);
                        v_isSharedCheck_895_ = (!leanh::lean_is_exclusive(v_v_875_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_887_ = v_v_875_;
                            v_isShared_888_ = v_isSharedCheck_895_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_885_);
                            leanh::lean_inc(v_key_884_);
                            leanh::lean_dec(v_v_875_);
                            v___x_887_ = leanh::lean_box(0);
                            v_isShared_888_ = v_isSharedCheck_895_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_896_ = leanh::lean_ctor_get(v_v_875_, 0);
                        v_isSharedCheck_906_ = (!leanh::lean_is_exclusive(v_v_875_)) as u8;
                        if v_isSharedCheck_906_ == 0 {
                            v___x_898_ = v_v_875_;
                            v_isShared_899_ = v_isSharedCheck_906_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_896_);
                            leanh::lean_dec(v_v_875_);
                            v___x_898_ = leanh::lean_box(0);
                            v_isShared_899_ = v_isSharedCheck_906_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_907_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_907_, 0, v_x_862_);
                        leanh::lean_ctor_set(v___x_907_, 1, v_x_863_);
                        v___y_879_ = v___x_907_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_880_ = lean_array_fset(v_xs_x27_877_, v_j_869_, v___y_879_);
                leanh::lean_dec(v_j_869_);
                if v_isShared_874_ == 0 {
                    leanh::lean_ctor_set(v___x_873_, 0, v___x_880_);
                    v___x_882_ = v___x_873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_882_;
            }
            4 => {
                v___x_889_ = l_Lean_instBEqMVarId_beq(v_x_862_, v_key_884_);
                if v___x_889_ == 0 {
                    leanh::lean_del_object(v___x_887_);
                    v___x_890_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_884_, v_val_885_, v_x_862_, v_x_863_,
                    );
                    v___x_891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_891_, 0, v___x_890_);
                    v___y_879_ = v___x_891_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_885_);
                    leanh::lean_dec(v_key_884_);
                    if v_isShared_888_ == 0 {
                        leanh::lean_ctor_set(v___x_887_, 1, v_x_863_);
                        leanh::lean_ctor_set(v___x_887_, 0, v_x_862_);
                        v___x_893_ = v___x_887_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_894_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_x_862_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_894_, 1, v_x_863_);
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
                v___x_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_node_896_, v___x_900_, v___x_901_, v_x_862_, v_x_863_);
                if v_isShared_899_ == 0 {
                    leanh::lean_ctor_set(v___x_898_, 0, v___x_902_);
                    v___x_904_ = v___x_898_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
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
                    v_reuseFailAlloc_930_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_930_, 0, v_ks_910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_930_, 1, v_vs_911_);
                    v___x_916_ = v_reuseFailAlloc_930_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_917_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_916_, v_x_862_, v_x_863_);
                v___x_925_ = 7usize;
                v___x_926_ = lean_usize_dec_le(v___x_925_, v_x_861_);
                if v___x_926_ == 0 {
                    v___x_927_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_917_);
                    v___x_928_ = leanh::lean_unsigned_to_nat(4);
                    v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
                    leanh::lean_dec(v___x_927_);
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
                    v_ks_920_ = leanh::lean_ctor_get(v_newNode_917_, 0);
                    leanh::lean_inc_ref(v_ks_920_);
                    v_vs_921_ = leanh::lean_ctor_get(v_newNode_917_, 1);
                    leanh::lean_inc_ref(v_vs_921_);
                    leanh::lean_dec_ref(v_newNode_917_);
                    v___x_922_ = leanh::lean_unsigned_to_nat(0);
                    v___x_923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2);
                    v___x_924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_861_, v_ks_920_, v_vs_921_, v___x_922_, v___x_923_);
                    leanh::lean_dec_ref(v_vs_921_);
                    leanh::lean_dec_ref(v_ks_920_);
                    return v___x_924_;
                } else {
                    return v_newNode_917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_depth_932_: usize,
    mut v_keys_933_: *mut leanh::LeanObject,
    mut v_vals_934_: *mut leanh::LeanObject,
    mut v_i_935_: *mut leanh::LeanObject,
    mut v_entries_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut v_k_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u64 = 0;
    let mut v_h_942_: usize = 0;
    let mut v___x_943_: usize = 0;
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: usize = 0;
    let mut v___x_946_: usize = 0;
    let mut v___x_947_: usize = 0;
    let mut v_h_948_: usize = 0;
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_937_ = lean_array_get_size(v_keys_933_);
                v___x_938_ = lean_nat_dec_lt(v_i_935_, v___x_937_);
                if v___x_938_ == 0 {
                    leanh::lean_dec(v_i_935_);
                    return v_entries_936_;
                } else {
                    v_k_939_ = lean_array_fget_borrowed(v_keys_933_, v_i_935_);
                    v_v_940_ = lean_array_fget_borrowed(v_vals_934_, v_i_935_);
                    v___x_941_ = l_Lean_instHashableMVarId_hash(v_k_939_);
                    v_h_942_ = lean_uint64_to_usize(v___x_941_);
                    v___x_943_ = 5usize;
                    v___x_944_ = leanh::lean_unsigned_to_nat(1);
                    v___x_945_ = 1usize;
                    v___x_946_ = lean_usize_sub(v_depth_932_, v___x_945_);
                    v___x_947_ = lean_usize_mul(v___x_943_, v___x_946_);
                    v_h_948_ = lean_usize_shift_right(v_h_942_, v___x_947_);
                    v___x_949_ = lean_nat_add(v_i_935_, v___x_944_);
                    leanh::lean_dec(v_i_935_);
                    leanh::lean_inc(v_v_940_);
                    leanh::lean_inc(v_k_939_);
                    v___x_950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_entries_936_, v_h_948_, v_depth_932_, v_k_939_, v_v_940_);
                    v_i_935_ = v___x_949_;
                    v_entries_936_ = v___x_950_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_depth_952_: *mut leanh::LeanObject,
    mut v_keys_953_: *mut leanh::LeanObject,
    mut v_vals_954_: *mut leanh::LeanObject,
    mut v_i_955_: *mut leanh::LeanObject,
    mut v_entries_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_957_: usize = 0;
    let mut v_res_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_957_ = leanh::lean_unbox_usize(v_depth_952_);
    leanh::lean_dec(v_depth_952_);
    v_res_958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_957_, v_keys_953_, v_vals_954_, v_i_955_, v_entries_956_);
    leanh::lean_dec_ref(v_vals_954_);
    leanh::lean_dec_ref(v_keys_953_);
    return v_res_958_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_959_: *mut leanh::LeanObject,
    mut v_x_960_: *mut leanh::LeanObject,
    mut v_x_961_: *mut leanh::LeanObject,
    mut v_x_962_: *mut leanh::LeanObject,
    mut v_x_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3572__boxed_964_: usize = 0;
    let mut v_x_3573__boxed_965_: usize = 0;
    let mut v_res_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3572__boxed_964_ = leanh::lean_unbox_usize(v_x_960_);
    leanh::lean_dec(v_x_960_);
    v_x_3573__boxed_965_ = leanh::lean_unbox_usize(v_x_961_);
    leanh::lean_dec(v_x_961_);
    v_res_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_959_, v_x_3572__boxed_964_, v_x_3573__boxed_965_, v_x_962_, v_x_963_);
    return v_res_966_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(
    mut v_x_967_: *mut leanh::LeanObject,
    mut v_x_968_: *mut leanh::LeanObject,
    mut v_x_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_970_: u64 = 0;
    let mut v___x_971_: usize = 0;
    let mut v___x_972_: usize = 0;
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_instHashableMVarId_hash(v_x_968_);
    v___x_971_ = lean_uint64_to_usize(v___x_970_);
    v___x_972_ = 1usize;
    v___x_973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_967_, v___x_971_, v___x_972_, v_x_968_, v_x_969_);
    return v___x_973_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(
    mut v_mvarId_974_: *mut leanh::LeanObject,
    mut v_val_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v_depth_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_978_ = lean_st_ref_take(v___y_976_);
                v_mctx_979_ = leanh::lean_ctor_get(v___x_978_, 0);
                v_cache_980_ = leanh::lean_ctor_get(v___x_978_, 1);
                v_zetaDeltaFVarIds_981_ = leanh::lean_ctor_get(v___x_978_, 2);
                v_postponed_982_ = leanh::lean_ctor_get(v___x_978_, 3);
                v_diag_983_ = leanh::lean_ctor_get(v___x_978_, 4);
                v_isSharedCheck_1011_ = (!leanh::lean_is_exclusive(v___x_978_)) as u8;
                if v_isSharedCheck_1011_ == 0 {
                    v___x_985_ = v___x_978_;
                    v_isShared_986_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_983_);
                    leanh::lean_inc(v_postponed_982_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_981_);
                    leanh::lean_inc(v_cache_980_);
                    leanh::lean_inc(v_mctx_979_);
                    leanh::lean_dec(v___x_978_);
                    v___x_985_ = leanh::lean_box(0);
                    v_isShared_986_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_987_ = leanh::lean_ctor_get(v_mctx_979_, 0);
                v_levelAssignDepth_988_ = leanh::lean_ctor_get(v_mctx_979_, 1);
                v_lmvarCounter_989_ = leanh::lean_ctor_get(v_mctx_979_, 2);
                v_mvarCounter_990_ = leanh::lean_ctor_get(v_mctx_979_, 3);
                v_lDecls_991_ = leanh::lean_ctor_get(v_mctx_979_, 4);
                v_decls_992_ = leanh::lean_ctor_get(v_mctx_979_, 5);
                v_userNames_993_ = leanh::lean_ctor_get(v_mctx_979_, 6);
                v_lAssignment_994_ = leanh::lean_ctor_get(v_mctx_979_, 7);
                v_eAssignment_995_ = leanh::lean_ctor_get(v_mctx_979_, 8);
                v_dAssignment_996_ = leanh::lean_ctor_get(v_mctx_979_, 9);
                v_isSharedCheck_1010_ = (!leanh::lean_is_exclusive(v_mctx_979_)) as u8;
                if v_isSharedCheck_1010_ == 0 {
                    v___x_998_ = v_mctx_979_;
                    v_isShared_999_ = v_isSharedCheck_1010_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_996_);
                    leanh::lean_inc(v_eAssignment_995_);
                    leanh::lean_inc(v_lAssignment_994_);
                    leanh::lean_inc(v_userNames_993_);
                    leanh::lean_inc(v_decls_992_);
                    leanh::lean_inc(v_lDecls_991_);
                    leanh::lean_inc(v_mvarCounter_990_);
                    leanh::lean_inc(v_lmvarCounter_989_);
                    leanh::lean_inc(v_levelAssignDepth_988_);
                    leanh::lean_inc(v_depth_987_);
                    leanh::lean_dec(v_mctx_979_);
                    v___x_998_ = leanh::lean_box(0);
                    v_isShared_999_ = v_isSharedCheck_1010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1000_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_eAssignment_995_, v_mvarId_974_, v_val_975_);
                if v_isShared_999_ == 0 {
                    leanh::lean_ctor_set(v___x_998_, 8, v___x_1000_);
                    v___x_1002_ = v___x_998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1009_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_depth_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_levelAssignDepth_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_lmvarCounter_989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_mvarCounter_990_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_lDecls_991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 5, v_decls_992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 6, v_userNames_993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 7, v_lAssignment_994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 8, v___x_1000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1009_, 9, v_dAssignment_996_);
                    v___x_1002_ = v_reuseFailAlloc_1009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_986_ == 0 {
                    leanh::lean_ctor_set(v___x_985_, 0, v___x_1002_);
                    v___x_1004_ = v___x_985_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_cache_980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_zetaDeltaFVarIds_981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_postponed_982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_diag_983_);
                    v___x_1004_ = v_reuseFailAlloc_1008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1005_ = lean_st_ref_set(v___y_976_, v___x_1004_);
                v___x_1006_ = leanh::lean_box(0);
                v___x_1007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1007_, 0, v___x_1006_);
                return v___x_1007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg___boxed(
    mut v_mvarId_1012_: *mut leanh::LeanObject,
    mut v_val_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1016_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(
            v_mvarId_1012_,
            v_val_1013_,
            v___y_1014_,
        );
    leanh::lean_dec(v___y_1014_);
    return v_res_1016_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(
    mut v_msgData_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = lean_st_ref_get(v___y_1021_);
    v_env_1024_ = leanh::lean_ctor_get(v___x_1023_, 0);
    leanh::lean_inc_ref(v_env_1024_);
    leanh::lean_dec(v___x_1023_);
    v___x_1025_ = lean_st_ref_get(v___y_1019_);
    v_mctx_1026_ = leanh::lean_ctor_get(v___x_1025_, 0);
    leanh::lean_inc_ref(v_mctx_1026_);
    leanh::lean_dec(v___x_1025_);
    v_lctx_1027_ = leanh::lean_ctor_get(v___y_1018_, 2);
    v_options_1028_ = leanh::lean_ctor_get(v___y_1020_, 2);
    leanh::lean_inc_ref(v_options_1028_);
    leanh::lean_inc_ref(v_lctx_1027_);
    v___x_1029_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1029_, 0, v_env_1024_);
    leanh::lean_ctor_set(v___x_1029_, 1, v_mctx_1026_);
    leanh::lean_ctor_set(v___x_1029_, 2, v_lctx_1027_);
    leanh::lean_ctor_set(v___x_1029_, 3, v_options_1028_);
    v___x_1030_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1030_, 0, v___x_1029_);
    leanh::lean_ctor_set(v___x_1030_, 1, v_msgData_1017_);
    v___x_1031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0___boxed(
    mut v_msgData_1032_: *mut leanh::LeanObject,
    mut v___y_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
    mut v___y_1036_: *mut leanh::LeanObject,
    mut v___y_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1038_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msgData_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
    leanh::lean_dec(v___y_1036_);
    leanh::lean_dec_ref(v___y_1035_);
    leanh::lean_dec(v___y_1034_);
    leanh::lean_dec_ref(v___y_1033_);
    return v_res_1038_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(
    mut v_msg_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
    mut v___y_1041_: *mut leanh::LeanObject,
    mut v___y_1042_: *mut leanh::LeanObject,
    mut v___y_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1045_ = leanh::lean_ctor_get(v___y_1042_, 5);
                v___x_1046_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
                v_a_1047_ = leanh::lean_ctor_get(v___x_1046_, 0);
                v_isSharedCheck_1055_ = (!leanh::lean_is_exclusive(v___x_1046_)) as u8;
                if v_isSharedCheck_1055_ == 0 {
                    v___x_1049_ = v___x_1046_;
                    v_isShared_1050_ = v_isSharedCheck_1055_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1047_);
                    leanh::lean_dec(v___x_1046_);
                    v___x_1049_ = leanh::lean_box(0);
                    v_isShared_1050_ = v_isSharedCheck_1055_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1045_);
                v___x_1051_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1051_, 0, v_ref_1045_);
                leanh::lean_ctor_set(v___x_1051_, 1, v_a_1047_);
                if v_isShared_1050_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1049_, 1);
                    leanh::lean_ctor_set(v___x_1049_, 0, v___x_1051_);
                    v___x_1053_ = v___x_1049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
                    v___x_1053_ = v_reuseFailAlloc_1054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg___boxed(
    mut v_msg_1056_: *mut leanh::LeanObject,
    mut v___y_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
    mut v___y_1059_: *mut leanh::LeanObject,
    mut v___y_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(
            v_msg_1056_,
            v___y_1057_,
            v___y_1058_,
            v___y_1059_,
            v___y_1060_,
        );
    leanh::lean_dec(v___y_1060_);
    leanh::lean_dec_ref(v___y_1059_);
    leanh::lean_dec(v___y_1058_);
    leanh::lean_dec_ref(v___y_1057_);
    return v_res_1062_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0;
    v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10;
    v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(
    mut v_right_1085_: u8,
    mut v_mvar_1086_: *mut leanh::LeanObject,
    mut v_a_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
    mut v_a_1089_: *mut leanh::LeanObject,
    mut v_a_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1118_: u8 = 0;
    let mut v_arg_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1142_: u8 = 0;
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_unused_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1156_: u8 = 0;
    let mut v_reuseFailAlloc_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: u8 = 0;
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v_unused_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1175_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvar_1086_);
                v___x_1099_ =
                    l_Lean_MVarId_getType(v_mvar_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
                if leanh::lean_obj_tag(v___x_1099_) == 0 {
                    v_a_1100_ = leanh::lean_ctor_get(v___x_1099_, 0);
                    leanh::lean_inc(v_a_1100_);
                    leanh::lean_dec_ref_known(v___x_1099_, 1);
                    v___x_1101_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_a_1100_, v_a_1088_);
                    v_a_1102_ = leanh::lean_ctor_get(v___x_1101_, 0);
                    leanh::lean_inc(v_a_1102_);
                    leanh::lean_dec_ref(v___x_1101_);
                    v___x_1103_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1102_);
                    leanh::lean_dec(v_a_1102_);
                    if leanh::lean_obj_tag(v___x_1103_) == 1 {
                        v_val_1104_ = leanh::lean_ctor_get(v___x_1103_, 0);
                        leanh::lean_inc(v_val_1104_);
                        leanh::lean_dec_ref_known(v___x_1103_, 1);
                        v_target_1105_ = leanh::lean_ctor_get(v_val_1104_, 3);
                        leanh::lean_inc_ref(v_target_1105_);
                        if leanh::lean_obj_tag(v_target_1105_) == 5 {
                            v_fn_1106_ = leanh::lean_ctor_get(v_target_1105_, 0);
                            leanh::lean_inc_ref(v_fn_1106_);
                            if leanh::lean_obj_tag(v_fn_1106_) == 5 {
                                v_fn_1107_ = leanh::lean_ctor_get(v_fn_1106_, 0);
                                leanh::lean_inc_ref(v_fn_1107_);
                                if leanh::lean_obj_tag(v_fn_1107_) == 5 {
                                    v_fn_1108_ = leanh::lean_ctor_get(v_fn_1107_, 0);
                                    if leanh::lean_obj_tag(v_fn_1108_) == 4 {
                                        v_declName_1109_ =
                                            leanh::lean_ctor_get(v_fn_1108_, 0);
                                        leanh::lean_inc(v_declName_1109_);
                                        if leanh::lean_obj_tag(v_declName_1109_) == 1 {
                                            v_pre_1110_ =
                                                leanh::lean_ctor_get(v_declName_1109_, 0);
                                            leanh::lean_inc(v_pre_1110_);
                                            if leanh::lean_obj_tag(v_pre_1110_) == 1 {
                                                v_pre_1111_ =
                                                    leanh::lean_ctor_get(v_pre_1110_, 0);
                                                leanh::lean_inc(v_pre_1111_);
                                                if leanh::lean_obj_tag(v_pre_1111_) == 1 {
                                                    v_pre_1112_ =
                                                        leanh::lean_ctor_get(v_pre_1111_, 0);
                                                    leanh::lean_inc(v_pre_1112_);
                                                    if leanh::lean_obj_tag(v_pre_1112_) == 1
                                                    {
                                                        v_u_1113_ = leanh::lean_ctor_get(
                                                            v_val_1104_,
                                                            0,
                                                        );
                                                        v_00_u03c3s_1114_ =
                                                            leanh::lean_ctor_get(
                                                                v_val_1104_,
                                                                1,
                                                            );
                                                        v_hyps_1115_ = leanh::lean_ctor_get(
                                                            v_val_1104_,
                                                            2,
                                                        );
                                                        v_isSharedCheck_1168_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v_val_1104_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1168_ == 0 {
                                                            v_unused_1169_ =
                                                                leanh::lean_ctor_get(
                                                                    v_val_1104_,
                                                                    3,
                                                                );
                                                            leanh::lean_dec(v_unused_1169_);
                                                            v___x_1117_ = v_val_1104_;
                                                            v_isShared_1118_ =
                                                                v_isSharedCheck_1168_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_hyps_1115_);
                                                            leanh::lean_inc(
                                                                v_00_u03c3s_1114_,
                                                            );
                                                            leanh::lean_inc(v_u_1113_);
                                                            leanh::lean_dec(v_val_1104_);
                                                            v___x_1117_ = leanh::lean_box(0);
                                                            v_isShared_1118_ =
                                                                v_isSharedCheck_1168_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref_known(
                                                            v_pre_1111_,
                                                            2,
                                                        );
                                                        leanh::lean_dec(v_pre_1112_);
                                                        leanh::lean_dec_ref_known(
                                                            v_pre_1110_,
                                                            2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_declName_1109_,
                                                            2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_fn_1107_, 2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_fn_1106_, 2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_target_1105_,
                                                            2,
                                                        );
                                                        leanh::lean_dec(v_val_1104_);
                                                        leanh::lean_dec(v_mvar_1086_);
                                                        v___y_1093_ = v_a_1087_;
                                                        v___y_1094_ = v_a_1088_;
                                                        v___y_1095_ = v_a_1089_;
                                                        v___y_1096_ = v_a_1090_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_pre_1111_);
                                                    leanh::lean_dec_ref_known(
                                                        v_pre_1110_,
                                                        2,
                                                    );
                                                    leanh::lean_dec_ref_known(
                                                        v_declName_1109_,
                                                        2,
                                                    );
                                                    leanh::lean_dec_ref_known(v_fn_1107_, 2);
                                                    leanh::lean_dec_ref_known(v_fn_1106_, 2);
                                                    leanh::lean_dec_ref_known(
                                                        v_target_1105_,
                                                        2,
                                                    );
                                                    leanh::lean_dec(v_val_1104_);
                                                    leanh::lean_dec(v_mvar_1086_);
                                                    v___y_1093_ = v_a_1087_;
                                                    v___y_1094_ = v_a_1088_;
                                                    v___y_1095_ = v_a_1089_;
                                                    v___y_1096_ = v_a_1090_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref_known(
                                                    v_declName_1109_,
                                                    2,
                                                );
                                                leanh::lean_dec(v_pre_1110_);
                                                leanh::lean_dec_ref_known(v_fn_1107_, 2);
                                                leanh::lean_dec_ref_known(v_fn_1106_, 2);
                                                leanh::lean_dec_ref_known(v_target_1105_, 2);
                                                leanh::lean_dec(v_val_1104_);
                                                leanh::lean_dec(v_mvar_1086_);
                                                v___y_1093_ = v_a_1087_;
                                                v___y_1094_ = v_a_1088_;
                                                v___y_1095_ = v_a_1089_;
                                                v___y_1096_ = v_a_1090_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_declName_1109_);
                                            leanh::lean_dec_ref_known(v_fn_1107_, 2);
                                            leanh::lean_dec_ref_known(v_fn_1106_, 2);
                                            leanh::lean_dec_ref_known(v_target_1105_, 2);
                                            leanh::lean_dec(v_val_1104_);
                                            leanh::lean_dec(v_mvar_1086_);
                                            v___y_1093_ = v_a_1087_;
                                            v___y_1094_ = v_a_1088_;
                                            v___y_1095_ = v_a_1089_;
                                            v___y_1096_ = v_a_1090_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_fn_1107_, 2);
                                        leanh::lean_dec_ref_known(v_fn_1106_, 2);
                                        leanh::lean_dec_ref_known(v_target_1105_, 2);
                                        leanh::lean_dec(v_val_1104_);
                                        leanh::lean_dec(v_mvar_1086_);
                                        v___y_1093_ = v_a_1087_;
                                        v___y_1094_ = v_a_1088_;
                                        v___y_1095_ = v_a_1089_;
                                        v___y_1096_ = v_a_1090_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_fn_1107_);
                                    leanh::lean_dec_ref_known(v_fn_1106_, 2);
                                    leanh::lean_dec_ref_known(v_target_1105_, 2);
                                    leanh::lean_dec(v_val_1104_);
                                    leanh::lean_dec(v_mvar_1086_);
                                    v___y_1093_ = v_a_1087_;
                                    v___y_1094_ = v_a_1088_;
                                    v___y_1095_ = v_a_1089_;
                                    v___y_1096_ = v_a_1090_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_fn_1106_);
                                leanh::lean_dec_ref_known(v_target_1105_, 2);
                                leanh::lean_dec(v_val_1104_);
                                leanh::lean_dec(v_mvar_1086_);
                                v___y_1093_ = v_a_1087_;
                                v___y_1094_ = v_a_1088_;
                                v___y_1095_ = v_a_1089_;
                                v___y_1096_ = v_a_1090_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_target_1105_);
                            leanh::lean_dec(v_val_1104_);
                            leanh::lean_dec(v_mvar_1086_);
                            v___y_1093_ = v_a_1087_;
                            v___y_1094_ = v_a_1088_;
                            v___y_1095_ = v_a_1089_;
                            v___y_1096_ = v_a_1090_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1103_);
                        leanh::lean_dec(v_mvar_1086_);
                        v___x_1170_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11,
                        );
                        v___x_1171_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_1170_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
                        return v___x_1171_;
                    }
                } else {
                    leanh::lean_dec(v_mvar_1086_);
                    v_a_1172_ = leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1179_ = (!leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1179_ == 0 {
                        v___x_1174_ = v___x_1099_;
                        v_isShared_1175_ = v_isSharedCheck_1179_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1172_);
                        leanh::lean_dec(v___x_1099_);
                        v___x_1174_ = leanh::lean_box(0);
                        v_isShared_1175_ = v_isSharedCheck_1179_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1097_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1,
                );
                v___x_1098_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_1097_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
                return v___x_1098_;
            }
            2 => {
                v_arg_1119_ = leanh::lean_ctor_get(v_target_1105_, 1);
                leanh::lean_inc_ref(v_arg_1119_);
                leanh::lean_dec_ref_known(v_target_1105_, 2);
                v_arg_1120_ = leanh::lean_ctor_get(v_fn_1106_, 1);
                leanh::lean_inc_ref(v_arg_1120_);
                leanh::lean_dec_ref_known(v_fn_1106_, 2);
                v_arg_1121_ = leanh::lean_ctor_get(v_fn_1107_, 1);
                leanh::lean_inc_ref(v_arg_1121_);
                leanh::lean_dec_ref_known(v_fn_1107_, 2);
                v_str_1122_ = leanh::lean_ctor_get(v_declName_1109_, 1);
                leanh::lean_inc_ref(v_str_1122_);
                leanh::lean_dec_ref_known(v_declName_1109_, 2);
                v_str_1123_ = leanh::lean_ctor_get(v_pre_1110_, 1);
                leanh::lean_inc_ref(v_str_1123_);
                leanh::lean_dec_ref_known(v_pre_1110_, 2);
                v_str_1124_ = leanh::lean_ctor_get(v_pre_1111_, 1);
                leanh::lean_inc_ref(v_str_1124_);
                leanh::lean_dec_ref_known(v_pre_1111_, 2);
                v_pre_1125_ = leanh::lean_ctor_get(v_pre_1112_, 0);
                leanh::lean_inc(v_pre_1125_);
                v_str_1126_ = leanh::lean_ctor_get(v_pre_1112_, 1);
                leanh::lean_inc_ref(v_str_1126_);
                leanh::lean_dec_ref_known(v_pre_1112_, 2);
                if leanh::lean_obj_tag(v_pre_1125_) == 0 {
                    v___x_1158_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2;
                    v___x_1159_ = lean_string_dec_eq(v_str_1126_, v___x_1158_);
                    leanh::lean_dec_ref(v_str_1126_);
                    if v___x_1159_ == 0 {
                        leanh::lean_dec_ref(v_str_1124_);
                        leanh::lean_dec_ref(v_str_1123_);
                        leanh::lean_dec_ref(v_str_1122_);
                        leanh::lean_dec_ref(v_arg_1121_);
                        leanh::lean_dec_ref(v_arg_1120_);
                        leanh::lean_dec_ref(v_arg_1119_);
                        leanh::lean_del_object(v___x_1117_);
                        leanh::lean_dec_ref(v_hyps_1115_);
                        leanh::lean_dec_ref(v_00_u03c3s_1114_);
                        leanh::lean_dec(v_u_1113_);
                        leanh::lean_dec(v_mvar_1086_);
                        v___y_1093_ = v_a_1087_;
                        v___y_1094_ = v_a_1088_;
                        v___y_1095_ = v_a_1089_;
                        v___y_1096_ = v_a_1090_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1160_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3;
                        v___x_1161_ = lean_string_dec_eq(v_str_1124_, v___x_1160_);
                        leanh::lean_dec_ref(v_str_1124_);
                        if v___x_1161_ == 0 {
                            leanh::lean_dec_ref(v_str_1123_);
                            leanh::lean_dec_ref(v_str_1122_);
                            leanh::lean_dec_ref(v_arg_1121_);
                            leanh::lean_dec_ref(v_arg_1120_);
                            leanh::lean_dec_ref(v_arg_1119_);
                            leanh::lean_del_object(v___x_1117_);
                            leanh::lean_dec_ref(v_hyps_1115_);
                            leanh::lean_dec_ref(v_00_u03c3s_1114_);
                            leanh::lean_dec(v_u_1113_);
                            leanh::lean_dec(v_mvar_1086_);
                            v___y_1093_ = v_a_1087_;
                            v___y_1094_ = v_a_1088_;
                            v___y_1095_ = v_a_1089_;
                            v___y_1096_ = v_a_1090_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1162_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4;
                            v___x_1163_ = lean_string_dec_eq(v_str_1123_, v___x_1162_);
                            leanh::lean_dec_ref(v_str_1123_);
                            if v___x_1163_ == 0 {
                                leanh::lean_dec_ref(v_str_1122_);
                                leanh::lean_dec_ref(v_arg_1121_);
                                leanh::lean_dec_ref(v_arg_1120_);
                                leanh::lean_dec_ref(v_arg_1119_);
                                leanh::lean_del_object(v___x_1117_);
                                leanh::lean_dec_ref(v_hyps_1115_);
                                leanh::lean_dec_ref(v_00_u03c3s_1114_);
                                leanh::lean_dec(v_u_1113_);
                                leanh::lean_dec(v_mvar_1086_);
                                v___y_1093_ = v_a_1087_;
                                v___y_1094_ = v_a_1088_;
                                v___y_1095_ = v_a_1089_;
                                v___y_1096_ = v_a_1090_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1164_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5;
                                v___x_1165_ = lean_string_dec_eq(v_str_1122_, v___x_1164_);
                                leanh::lean_dec_ref(v_str_1122_);
                                if v___x_1165_ == 0 {
                                    leanh::lean_dec_ref(v_arg_1121_);
                                    leanh::lean_dec_ref(v_arg_1120_);
                                    leanh::lean_dec_ref(v_arg_1119_);
                                    leanh::lean_del_object(v___x_1117_);
                                    leanh::lean_dec_ref(v_hyps_1115_);
                                    leanh::lean_dec_ref(v_00_u03c3s_1114_);
                                    leanh::lean_dec(v_u_1113_);
                                    leanh::lean_dec(v_mvar_1086_);
                                    v___y_1093_ = v_a_1087_;
                                    v___y_1094_ = v_a_1088_;
                                    v___y_1095_ = v_a_1089_;
                                    v___y_1096_ = v_a_1090_;
                                    state = 1;
                                    continue;
                                } else {
                                    if v_right_1085_ == 0 {
                                        v___x_1166_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7;
                                        leanh::lean_inc_ref(v_arg_1120_);
                                        v_fst_1128_ = v___x_1166_;
                                        v_snd_1129_ = v_arg_1120_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_1167_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9;
                                        leanh::lean_inc_ref(v_arg_1119_);
                                        v_fst_1128_ = v___x_1167_;
                                        v_snd_1129_ = v_arg_1119_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_1126_);
                    leanh::lean_dec(v_pre_1125_);
                    leanh::lean_dec_ref(v_str_1124_);
                    leanh::lean_dec_ref(v_str_1123_);
                    leanh::lean_dec_ref(v_str_1122_);
                    leanh::lean_dec_ref(v_arg_1121_);
                    leanh::lean_dec_ref(v_arg_1120_);
                    leanh::lean_dec_ref(v_arg_1119_);
                    leanh::lean_del_object(v___x_1117_);
                    leanh::lean_dec_ref(v_hyps_1115_);
                    leanh::lean_dec_ref(v_00_u03c3s_1114_);
                    leanh::lean_dec(v_u_1113_);
                    leanh::lean_dec(v_mvar_1086_);
                    v___y_1093_ = v_a_1087_;
                    v___y_1094_ = v_a_1088_;
                    v___y_1095_ = v_a_1089_;
                    v___y_1096_ = v_a_1090_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_hyps_1115_);
                leanh::lean_inc(v_u_1113_);
                if v_isShared_1118_ == 0 {
                    leanh::lean_ctor_set(v___x_1117_, 3, v_snd_1129_);
                    v___x_1131_ = v___x_1117_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_u_1113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_00_u03c3s_1114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_hyps_1115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_snd_1129_);
                    v___x_1131_ = v_reuseFailAlloc_1157_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1132_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1131_);
                v___x_1133_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1132_,
                    v_pre_1125_,
                    v_a_1087_,
                    v_a_1088_,
                    v_a_1089_,
                    v_a_1090_,
                );
                if leanh::lean_obj_tag(v___x_1133_) == 0 {
                    v_a_1134_ = leanh::lean_ctor_get(v___x_1133_, 0);
                    leanh::lean_inc_n(v_a_1134_, 2);
                    leanh::lean_dec_ref_known(v___x_1133_, 1);
                    v___x_1135_ = leanh::lean_box(0);
                    v___x_1136_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1136_, 0, v_u_1113_);
                    leanh::lean_ctor_set(v___x_1136_, 1, v___x_1135_);
                    leanh::lean_inc(v_fst_1128_);
                    v___x_1137_ = l_Lean_mkConst(v_fst_1128_, v___x_1136_);
                    v___x_1138_ = l_Lean_mkApp5(
                        v___x_1137_,
                        v_arg_1121_,
                        v_hyps_1115_,
                        v_arg_1120_,
                        v_arg_1119_,
                        v_a_1134_,
                    );
                    v___x_1139_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvar_1086_, v___x_1138_, v_a_1088_);
                    v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v_unused_1148_ = leanh::lean_ctor_get(v___x_1139_, 0);
                        leanh::lean_dec(v_unused_1148_);
                        v___x_1141_ = v___x_1139_;
                        v_isShared_1142_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1139_);
                        v___x_1141_ = leanh::lean_box(0);
                        v_isShared_1142_ = v_isSharedCheck_1147_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_1121_);
                    leanh::lean_dec_ref(v_arg_1120_);
                    leanh::lean_dec_ref(v_arg_1119_);
                    leanh::lean_dec_ref(v_hyps_1115_);
                    leanh::lean_dec(v_u_1113_);
                    leanh::lean_dec(v_mvar_1086_);
                    v_a_1149_ = leanh::lean_ctor_get(v___x_1133_, 0);
                    v_isSharedCheck_1156_ = (!leanh::lean_is_exclusive(v___x_1133_)) as u8;
                    if v_isSharedCheck_1156_ == 0 {
                        v___x_1151_ = v___x_1133_;
                        v_isShared_1152_ = v_isSharedCheck_1156_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1149_);
                        leanh::lean_dec(v___x_1133_);
                        v___x_1151_ = leanh::lean_box(0);
                        v_isShared_1152_ = v_isSharedCheck_1156_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1143_ = l_Lean_Expr_mvarId_x21(v_a_1134_);
                leanh::lean_dec(v_a_1134_);
                if v_isShared_1142_ == 0 {
                    leanh::lean_ctor_set(v___x_1141_, 0, v___x_1143_);
                    v___x_1145_ = v___x_1141_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1145_;
            }
            7 => {
                if v_isShared_1152_ == 0 {
                    v___x_1154_ = v___x_1151_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
                    v___x_1154_ = v_reuseFailAlloc_1155_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1154_;
            }
            9 => {
                if v_isShared_1175_ == 0 {
                    v___x_1177_ = v___x_1174_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
                    v___x_1177_ = v_reuseFailAlloc_1178_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___boxed(
    mut v_right_1180_: *mut leanh::LeanObject,
    mut v_mvar_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
    mut v_a_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_right_boxed_1187_: u8 = 0;
    let mut v_res_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_right_boxed_1187_ = (leanh::lean_unbox(v_right_1180_) as u8);
    v_res_1188_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(
        v_right_boxed_1187_,
        v_mvar_1181_,
        v_a_1182_,
        v_a_1183_,
        v_a_1184_,
        v_a_1185_,
    );
    leanh::lean_dec(v_a_1185_);
    leanh::lean_dec_ref(v_a_1184_);
    leanh::lean_dec(v_a_1183_);
    leanh::lean_dec_ref(v_a_1182_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(
    mut v_00_u03b1_1189_: *mut leanh::LeanObject,
    mut v_msg_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(
            v_msg_1190_,
            v___y_1191_,
            v___y_1192_,
            v___y_1193_,
            v___y_1194_,
        );
    return v___x_1196_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___boxed(
    mut v_00_u03b1_1197_: *mut leanh::LeanObject,
    mut v_msg_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(
        v_00_u03b1_1197_,
        v_msg_1198_,
        v___y_1199_,
        v___y_1200_,
        v___y_1201_,
        v___y_1202_,
    );
    leanh::lean_dec(v___y_1202_);
    leanh::lean_dec_ref(v___y_1201_);
    leanh::lean_dec(v___y_1200_);
    leanh::lean_dec_ref(v___y_1199_);
    return v_res_1204_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(
    mut v_mvarId_1205_: *mut leanh::LeanObject,
    mut v_val_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(
            v_mvarId_1205_,
            v_val_1206_,
            v___y_1208_,
        );
    return v___x_1212_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___boxed(
    mut v_mvarId_1213_: *mut leanh::LeanObject,
    mut v_val_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(
            v_mvarId_1213_,
            v_val_1214_,
            v___y_1215_,
            v___y_1216_,
            v___y_1217_,
            v___y_1218_,
        );
    leanh::lean_dec(v___y_1218_);
    leanh::lean_dec_ref(v___y_1217_);
    leanh::lean_dec(v___y_1216_);
    leanh::lean_dec_ref(v___y_1215_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3(
    mut v_00_u03b2_1221_: *mut leanh::LeanObject,
    mut v_x_1222_: *mut leanh::LeanObject,
    mut v_x_1223_: *mut leanh::LeanObject,
    mut v_x_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_x_1222_, v_x_1223_, v_x_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1226_: *mut leanh::LeanObject,
    mut v_x_1227_: *mut leanh::LeanObject,
    mut v_x_1228_: usize,
    mut v_x_1229_: usize,
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_x_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_1227_, v_x_1228_, v_x_1229_, v_x_1230_, v_x_1231_);
    return v___x_1232_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1233_: *mut leanh::LeanObject,
    mut v_x_1234_: *mut leanh::LeanObject,
    mut v_x_1235_: *mut leanh::LeanObject,
    mut v_x_1236_: *mut leanh::LeanObject,
    mut v_x_1237_: *mut leanh::LeanObject,
    mut v_x_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4135__boxed_1239_: usize = 0;
    let mut v_x_4136__boxed_1240_: usize = 0;
    let mut v_res_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4135__boxed_1239_ = leanh::lean_unbox_usize(v_x_1235_);
    leanh::lean_dec(v_x_1235_);
    v_x_4136__boxed_1240_ = leanh::lean_unbox_usize(v_x_1236_);
    leanh::lean_dec(v_x_1236_);
    v_res_1241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(v_00_u03b2_1233_, v_x_1234_, v_x_4135__boxed_1239_, v_x_4136__boxed_1240_, v_x_1237_, v_x_1238_);
    return v_res_1241_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1242_: *mut leanh::LeanObject,
    mut v_n_1243_: *mut leanh::LeanObject,
    mut v_k_1244_: *mut leanh::LeanObject,
    mut v_v_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1243_, v_k_1244_, v_v_1245_);
    return v___x_1246_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1247_: *mut leanh::LeanObject,
    mut v_depth_1248_: usize,
    mut v_keys_1249_: *mut leanh::LeanObject,
    mut v_vals_1250_: *mut leanh::LeanObject,
    mut v_heq_1251_: *mut leanh::LeanObject,
    mut v_i_1252_: *mut leanh::LeanObject,
    mut v_entries_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_1248_, v_keys_1249_, v_vals_1250_, v_i_1252_, v_entries_1253_);
    return v___x_1254_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_1255_: *mut leanh::LeanObject,
    mut v_depth_1256_: *mut leanh::LeanObject,
    mut v_keys_1257_: *mut leanh::LeanObject,
    mut v_vals_1258_: *mut leanh::LeanObject,
    mut v_heq_1259_: *mut leanh::LeanObject,
    mut v_i_1260_: *mut leanh::LeanObject,
    mut v_entries_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1262_: usize = 0;
    let mut v_res_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1262_ = leanh::lean_unbox_usize(v_depth_1256_);
    leanh::lean_dec(v_depth_1256_);
    v_res_1263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_1255_, v_depth_boxed_1262_, v_keys_1257_, v_vals_1258_, v_heq_1259_, v_i_1260_, v_entries_1261_);
    leanh::lean_dec_ref(v_vals_1258_);
    leanh::lean_dec_ref(v_keys_1257_);
    return v_res_1263_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1264_: *mut leanh::LeanObject,
    mut v_x_1265_: *mut leanh::LeanObject,
    mut v_x_1266_: *mut leanh::LeanObject,
    mut v_x_1267_: *mut leanh::LeanObject,
    mut v_x_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_1265_, v_x_1266_, v_x_1267_, v_x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(
    mut v_x_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1274_);
    leanh::lean_inc_ref(v___y_1273_);
    leanh::lean_inc(v___y_1272_);
    leanh::lean_inc_ref(v___y_1271_);
    v___x_1280_ = leanh::lean_apply_9(
        v_x_1270_,
        v___y_1271_,
        v___y_1272_,
        v___y_1273_,
        v___y_1274_,
        v___y_1275_,
        v___y_1276_,
        v___y_1277_,
        v___y_1278_,
        leanh::lean_box(0),
    );
    return v___x_1280_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed(
    mut v_x_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
    mut v___y_1288_: *mut leanh::LeanObject,
    mut v___y_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(v_x_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
    leanh::lean_dec(v___y_1285_);
    leanh::lean_dec_ref(v___y_1284_);
    leanh::lean_dec(v___y_1283_);
    leanh::lean_dec_ref(v___y_1282_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(
    mut v_mvarId_1292_: *mut leanh::LeanObject,
    mut v_x_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1297_);
                leanh::lean_inc_ref(v___y_1296_);
                leanh::lean_inc(v___y_1295_);
                leanh::lean_inc_ref(v___y_1294_);
                v___f_1303_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_1303_, 0, v_x_1293_);
                leanh::lean_closure_set(v___f_1303_, 1, v___y_1294_);
                leanh::lean_closure_set(v___f_1303_, 2, v___y_1295_);
                leanh::lean_closure_set(v___f_1303_, 3, v___y_1296_);
                leanh::lean_closure_set(v___f_1303_, 4, v___y_1297_);
                v___x_1304_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1292_,
                    v___f_1303_,
                    v___y_1298_,
                    v___y_1299_,
                    v___y_1300_,
                    v___y_1301_,
                );
                if leanh::lean_obj_tag(v___x_1304_) == 0 {
                    return v___x_1304_;
                } else {
                    v_a_1305_ = leanh::lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1312_ = (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1312_ == 0 {
                        v___x_1307_ = v___x_1304_;
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1305_);
                        leanh::lean_dec(v___x_1304_);
                        v___x_1307_ = leanh::lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1308_ == 0 {
                    v___x_1310_ = v___x_1307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
                    v___x_1310_ = v_reuseFailAlloc_1311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___boxed(
    mut v_mvarId_1313_: *mut leanh::LeanObject,
    mut v_x_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1324_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(
            v_mvarId_1313_,
            v_x_1314_,
            v___y_1315_,
            v___y_1316_,
            v___y_1317_,
            v___y_1318_,
            v___y_1319_,
            v___y_1320_,
            v___y_1321_,
            v___y_1322_,
        );
    leanh::lean_dec(v___y_1322_);
    leanh::lean_dec_ref(v___y_1321_);
    leanh::lean_dec(v___y_1320_);
    leanh::lean_dec_ref(v___y_1319_);
    leanh::lean_dec(v___y_1318_);
    leanh::lean_dec_ref(v___y_1317_);
    leanh::lean_dec(v___y_1316_);
    leanh::lean_dec_ref(v___y_1315_);
    return v_res_1324_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(
    mut v_00_u03b1_1325_: *mut leanh::LeanObject,
    mut v_mvarId_1326_: *mut leanh::LeanObject,
    mut v_x_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(
            v_mvarId_1326_,
            v_x_1327_,
            v___y_1328_,
            v___y_1329_,
            v___y_1330_,
            v___y_1331_,
            v___y_1332_,
            v___y_1333_,
            v___y_1334_,
            v___y_1335_,
        );
    return v___x_1337_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___boxed(
    mut v_00_u03b1_1338_: *mut leanh::LeanObject,
    mut v_mvarId_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
    mut v___y_1345_: *mut leanh::LeanObject,
    mut v___y_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
    mut v___y_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1350_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(
            v_00_u03b1_1338_,
            v_mvarId_1339_,
            v_x_1340_,
            v___y_1341_,
            v___y_1342_,
            v___y_1343_,
            v___y_1344_,
            v___y_1345_,
            v___y_1346_,
            v___y_1347_,
            v___y_1348_,
        );
    leanh::lean_dec(v___y_1348_);
    leanh::lean_dec_ref(v___y_1347_);
    leanh::lean_dec(v___y_1346_);
    leanh::lean_dec_ref(v___y_1345_);
    leanh::lean_dec(v___y_1344_);
    leanh::lean_dec_ref(v___y_1343_);
    leanh::lean_dec(v___y_1342_);
    leanh::lean_dec_ref(v___y_1341_);
    return v_res_1350_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(
    mut v___x_1351_: u8,
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(
                    v___x_1351_,
                    v_a_1352_,
                    v___y_1357_,
                    v___y_1358_,
                    v___y_1359_,
                    v___y_1360_,
                );
                if leanh::lean_obj_tag(v___x_1362_) == 0 {
                    v_a_1363_ = leanh::lean_ctor_get(v___x_1362_, 0);
                    leanh::lean_inc(v_a_1363_);
                    leanh::lean_dec_ref_known(v___x_1362_, 1);
                    v___x_1364_ = leanh::lean_box(0);
                    v___x_1365_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1365_, 0, v_a_1363_);
                    leanh::lean_ctor_set(v___x_1365_, 1, v___x_1364_);
                    v___x_1366_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1365_,
                        v___y_1354_,
                        v___y_1357_,
                        v___y_1358_,
                        v___y_1359_,
                        v___y_1360_,
                    );
                    return v___x_1366_;
                } else {
                    v_a_1367_ = leanh::lean_ctor_get(v___x_1362_, 0);
                    v_isSharedCheck_1374_ = (!leanh::lean_is_exclusive(v___x_1362_)) as u8;
                    if v_isSharedCheck_1374_ == 0 {
                        v___x_1369_ = v___x_1362_;
                        v_isShared_1370_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1367_);
                        leanh::lean_dec(v___x_1362_);
                        v___x_1369_ = leanh::lean_box(0);
                        v_isShared_1370_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1370_ == 0 {
                    v___x_1372_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed(
    mut v___x_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
    mut v___y_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1888__boxed_1386_: u8 = 0;
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1888__boxed_1386_ = (leanh::lean_unbox(v___x_1375_) as u8);
    v_res_1387_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(
        v___x_1888__boxed_1386_,
        v_a_1376_,
        v___y_1377_,
        v___y_1378_,
        v___y_1379_,
        v___y_1380_,
        v___y_1381_,
        v___y_1382_,
        v___y_1383_,
        v___y_1384_,
    );
    leanh::lean_dec(v___y_1384_);
    leanh::lean_dec_ref(v___y_1383_);
    leanh::lean_dec(v___y_1382_);
    leanh::lean_dec_ref(v___y_1381_);
    leanh::lean_dec(v___y_1380_);
    leanh::lean_dec_ref(v___y_1379_);
    leanh::lean_dec(v___y_1378_);
    leanh::lean_dec_ref(v___y_1377_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(
    mut v_a_1388_: *mut leanh::LeanObject,
    mut v_a_1389_: *mut leanh::LeanObject,
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
    mut v_a_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1397_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1389_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_,
                );
                if leanh::lean_obj_tag(v___x_1397_) == 0 {
                    v_a_1398_ = leanh::lean_ctor_get(v___x_1397_, 0);
                    leanh::lean_inc_n(v_a_1398_, 2);
                    leanh::lean_dec_ref_known(v___x_1397_, 1);
                    v___x_1399_ = 0;
                    v___x_1400_ = leanh::lean_box((v___x_1399_) as usize);
                    v___f_1401_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1401_, 0, v___x_1400_);
                    leanh::lean_closure_set(v___f_1401_, 1, v_a_1398_);
                    v___x_1402_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_1398_, v___f_1401_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
                    return v___x_1402_;
                } else {
                    v_a_1403_ = leanh::lean_ctor_get(v___x_1397_, 0);
                    v_isSharedCheck_1410_ = (!leanh::lean_is_exclusive(v___x_1397_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v___x_1405_ = v___x_1397_;
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1403_);
                        leanh::lean_dec(v___x_1397_);
                        v___x_1405_ = leanh::lean_box(0);
                        v_isShared_1406_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1406_ == 0 {
                    v___x_1408_ = v___x_1405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___boxed(
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
    mut v_a_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1420_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(
        v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_,
    );
    leanh::lean_dec(v_a_1418_);
    leanh::lean_dec_ref(v_a_1417_);
    leanh::lean_dec(v_a_1416_);
    leanh::lean_dec_ref(v_a_1415_);
    leanh::lean_dec(v_a_1414_);
    leanh::lean_dec_ref(v_a_1413_);
    leanh::lean_dec(v_a_1412_);
    leanh::lean_dec_ref(v_a_1411_);
    return v_res_1420_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(
    mut v_x_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_a_1426_: *mut leanh::LeanObject,
    mut v_a_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
    mut v_a_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(
        v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_,
    );
    return v___x_1431_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed(
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
    mut v_a_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(
        v_x_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_,
        v_a_1440_,
    );
    leanh::lean_dec(v_a_1440_);
    leanh::lean_dec_ref(v_a_1439_);
    leanh::lean_dec(v_a_1438_);
    leanh::lean_dec_ref(v_a_1437_);
    leanh::lean_dec(v_a_1436_);
    leanh::lean_dec_ref(v_a_1435_);
    leanh::lean_dec(v_a_1434_);
    leanh::lean_dec_ref(v_a_1433_);
    leanh::lean_dec(v_x_1432_);
    return v_res_1442_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1()
-> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1464_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4;
    v___x_1465_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8;
    v___x_1466_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1467_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1463_,
        v___x_1464_,
        v___x_1465_,
        v___x_1466_,
    );
    return v___x_1467_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(
    mut v_a_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1469_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
    return v_res_1469_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(
    mut v_a_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
    mut v_a_1472_: *mut leanh::LeanObject,
    mut v_a_1473_: *mut leanh::LeanObject,
    mut v_a_1474_: *mut leanh::LeanObject,
    mut v_a_1475_: *mut leanh::LeanObject,
    mut v_a_1476_: *mut leanh::LeanObject,
    mut v_a_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1471_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_,
                );
                if leanh::lean_obj_tag(v___x_1479_) == 0 {
                    v_a_1480_ = leanh::lean_ctor_get(v___x_1479_, 0);
                    leanh::lean_inc_n(v_a_1480_, 2);
                    leanh::lean_dec_ref_known(v___x_1479_, 1);
                    v___x_1481_ = 1;
                    v___x_1482_ = leanh::lean_box((v___x_1481_) as usize);
                    v___f_1483_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1483_, 0, v___x_1482_);
                    leanh::lean_closure_set(v___f_1483_, 1, v_a_1480_);
                    v___x_1484_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_1480_, v___f_1483_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
                    return v___x_1484_;
                } else {
                    v_a_1485_ = leanh::lean_ctor_get(v___x_1479_, 0);
                    v_isSharedCheck_1492_ = (!leanh::lean_is_exclusive(v___x_1479_)) as u8;
                    if v_isSharedCheck_1492_ == 0 {
                        v___x_1487_ = v___x_1479_;
                        v_isShared_1488_ = v_isSharedCheck_1492_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1485_);
                        leanh::lean_dec(v___x_1479_);
                        v___x_1487_ = leanh::lean_box(0);
                        v_isShared_1488_ = v_isSharedCheck_1492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1488_ == 0 {
                    v___x_1490_ = v___x_1487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(
    mut v_a_1493_: *mut leanh::LeanObject,
    mut v_a_1494_: *mut leanh::LeanObject,
    mut v_a_1495_: *mut leanh::LeanObject,
    mut v_a_1496_: *mut leanh::LeanObject,
    mut v_a_1497_: *mut leanh::LeanObject,
    mut v_a_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
    mut v_a_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(
        v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_,
    );
    leanh::lean_dec(v_a_1500_);
    leanh::lean_dec_ref(v_a_1499_);
    leanh::lean_dec(v_a_1498_);
    leanh::lean_dec_ref(v_a_1497_);
    leanh::lean_dec(v_a_1496_);
    leanh::lean_dec_ref(v_a_1495_);
    leanh::lean_dec(v_a_1494_);
    leanh::lean_dec_ref(v_a_1493_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(
    mut v_x_1503_: *mut leanh::LeanObject,
    mut v_a_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v_a_1509_: *mut leanh::LeanObject,
    mut v_a_1510_: *mut leanh::LeanObject,
    mut v_a_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(
        v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(
    mut v_x_1514_: *mut leanh::LeanObject,
    mut v_a_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
    mut v_a_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_a_1521_: *mut leanh::LeanObject,
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(
        v_x_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_,
        v_a_1522_,
    );
    leanh::lean_dec(v_a_1522_);
    leanh::lean_dec_ref(v_a_1521_);
    leanh::lean_dec(v_a_1520_);
    leanh::lean_dec_ref(v_a_1519_);
    leanh::lean_dec(v_a_1518_);
    leanh::lean_dec_ref(v_a_1517_);
    leanh::lean_dec(v_a_1516_);
    leanh::lean_dec_ref(v_a_1515_);
    leanh::lean_dec(v_x_1514_);
    return v_res_1524_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1()
-> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1541_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1;
    v___x_1542_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3;
    v___x_1543_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1544_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1540_,
        v___x_1541_,
        v___x_1542_,
        v___x_1543_,
    );
    return v___x_1544_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(
    mut v_a_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1546_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
    return v_res_1546_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
}