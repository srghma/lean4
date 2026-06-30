// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Basic
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_infer_type, lean_instantiate_level_mvars, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
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
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType,
    l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp, l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkConst, l_Lean_mkMVar,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_setType___redArg,
    l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkFreshLevelMVar,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value)
            as *mut leanh::LeanObject,
        2932917581903347504 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value:
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
    m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 116, 97, 114, 116, 95, 101, 110, 116, 97, 105, 108, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value)
            as *mut leanh::LeanObject,
        15990607923454282773 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value)
            as *mut leanh::LeanObject,
        2578581590150657327 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        84, 104, 101, 32, 103, 111, 97, 108, 32, 116, 121, 112, 101, 32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116,
        105, 111, 110, 46, 32, 73, 116, 32, 104, 97, 115, 32, 116, 121, 112, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value:
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
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 115, 116, 97, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value) as *mut leanh::LeanObject,11928792895960270860 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 83, 116, 97, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value) as *mut leanh::LeanObject,8722830812433448010 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 115, 116, 111, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value) as *mut leanh::LeanObject,12268960959217848762 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 83, 116, 111, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value) as *mut leanh::LeanObject,18431599668601016270 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
    mut v_l_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v_unused_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1195_ = lean_st_ref_get(v___y_1193_);
                v_mctx_1196_ = leanh::lean_ctor_get(v___x_1195_, 0);
                leanh::lean_inc_ref(v_mctx_1196_);
                leanh::lean_dec(v___x_1195_);
                v___x_1197_ = lean_instantiate_level_mvars(v_mctx_1196_, v_l_1192_);
                v_fst_1198_ = leanh::lean_ctor_get(v___x_1197_, 0);
                leanh::lean_inc(v_fst_1198_);
                v_snd_1199_ = leanh::lean_ctor_get(v___x_1197_, 1);
                leanh::lean_inc(v_snd_1199_);
                leanh::lean_dec_ref(v___x_1197_);
                v___x_1200_ = lean_st_ref_take(v___y_1193_);
                v_cache_1201_ = leanh::lean_ctor_get(v___x_1200_, 1);
                v_zetaDeltaFVarIds_1202_ = leanh::lean_ctor_get(v___x_1200_, 2);
                v_postponed_1203_ = leanh::lean_ctor_get(v___x_1200_, 3);
                v_diag_1204_ = leanh::lean_ctor_get(v___x_1200_, 4);
                v_isSharedCheck_1213_ = (!leanh::lean_is_exclusive(v___x_1200_)) as u8;
                if v_isSharedCheck_1213_ == 0 {
                    v_unused_1214_ = leanh::lean_ctor_get(v___x_1200_, 0);
                    leanh::lean_dec(v_unused_1214_);
                    v___x_1206_ = v___x_1200_;
                    v_isShared_1207_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1204_);
                    leanh::lean_inc(v_postponed_1203_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1202_);
                    leanh::lean_inc(v_cache_1201_);
                    leanh::lean_dec(v___x_1200_);
                    v___x_1206_ = leanh::lean_box(0);
                    v_isShared_1207_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1207_ == 0 {
                    leanh::lean_ctor_set(v___x_1206_, 0, v_fst_1198_);
                    v___x_1209_ = v___x_1206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_fst_1198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_cache_1201_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1212_,
                        2,
                        v_zetaDeltaFVarIds_1202_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_postponed_1203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_diag_1204_);
                    v___x_1209_ = v_reuseFailAlloc_1212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1210_ = lean_st_ref_set(v___y_1193_, v___x_1209_);
                v___x_1211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1211_, 0, v_snd_1199_);
                return v___x_1211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg___boxed(
    mut v_l_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1218_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
            v_l_1215_,
            v___y_1216_,
        );
    leanh::lean_dec(v___y_1216_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(
    mut v_l_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
            v_l_1219_,
            v___y_1221_,
        );
    return v___x_1225_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___boxed(
    mut v_l_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
    mut v___y_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(
            v_l_1226_,
            v___y_1227_,
            v___y_1228_,
            v___y_1229_,
            v___y_1230_,
        );
    leanh::lean_dec(v___y_1230_);
    leanh::lean_dec_ref(v___y_1229_);
    leanh::lean_dec(v___y_1228_);
    leanh::lean_dec_ref(v___y_1227_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
    mut v_e_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut v_unused_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1236_ = l_Lean_Expr_hasMVar(v_e_1233_);
                if v___x_1236_ == 0 {
                    v___x_1237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1237_, 0, v_e_1233_);
                    return v___x_1237_;
                } else {
                    v___x_1238_ = lean_st_ref_get(v___y_1234_);
                    v_mctx_1239_ = leanh::lean_ctor_get(v___x_1238_, 0);
                    leanh::lean_inc_ref(v_mctx_1239_);
                    leanh::lean_dec(v___x_1238_);
                    v___x_1240_ = l_Lean_instantiateMVarsCore(v_mctx_1239_, v_e_1233_);
                    v_fst_1241_ = leanh::lean_ctor_get(v___x_1240_, 0);
                    leanh::lean_inc(v_fst_1241_);
                    v_snd_1242_ = leanh::lean_ctor_get(v___x_1240_, 1);
                    leanh::lean_inc(v_snd_1242_);
                    leanh::lean_dec_ref(v___x_1240_);
                    v___x_1243_ = lean_st_ref_take(v___y_1234_);
                    v_cache_1244_ = leanh::lean_ctor_get(v___x_1243_, 1);
                    v_zetaDeltaFVarIds_1245_ = leanh::lean_ctor_get(v___x_1243_, 2);
                    v_postponed_1246_ = leanh::lean_ctor_get(v___x_1243_, 3);
                    v_diag_1247_ = leanh::lean_ctor_get(v___x_1243_, 4);
                    v_isSharedCheck_1256_ = (!leanh::lean_is_exclusive(v___x_1243_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v_unused_1257_ = leanh::lean_ctor_get(v___x_1243_, 0);
                        leanh::lean_dec(v_unused_1257_);
                        v___x_1249_ = v___x_1243_;
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1247_);
                        leanh::lean_inc(v_postponed_1246_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1245_);
                        leanh::lean_inc(v_cache_1244_);
                        leanh::lean_dec(v___x_1243_);
                        v___x_1249_ = leanh::lean_box(0);
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1250_ == 0 {
                    leanh::lean_ctor_set(v___x_1249_, 0, v_snd_1242_);
                    v___x_1252_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1255_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_snd_1242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_cache_1244_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1255_,
                        2,
                        v_zetaDeltaFVarIds_1245_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_postponed_1246_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_diag_1247_);
                    v___x_1252_ = v_reuseFailAlloc_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1253_ = lean_st_ref_set(v___y_1234_, v___x_1252_);
                v___x_1254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1254_, 0, v_fst_1241_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg___boxed(
    mut v_e_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
            v_e_1258_,
            v___y_1259_,
        );
    leanh::lean_dec(v___y_1259_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(
    mut v_e_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
            v_e_1262_,
            v___y_1264_,
        );
    return v___x_1268_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___boxed(
    mut v_e_1269_: *mut leanh::LeanObject,
    mut v___y_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(
        v_e_1269_,
        v___y_1270_,
        v___y_1271_,
        v___y_1272_,
        v___y_1273_,
    );
    leanh::lean_dec(v___y_1273_);
    leanh::lean_dec_ref(v___y_1272_);
    leanh::lean_dec(v___y_1271_);
    leanh::lean_dec_ref(v___y_1270_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStart(
    mut v_goal_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_a_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_a_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_a_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_a_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_a_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1306_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_goal_1300_);
                if leanh::lean_obj_tag(v___x_1306_) == 1 {
                    leanh::lean_dec_ref(v_goal_1300_);
                    v_val_1307_ = leanh::lean_ctor_get(v___x_1306_, 0);
                    v_isSharedCheck_1316_ = (!leanh::lean_is_exclusive(v___x_1306_)) as u8;
                    if v_isSharedCheck_1316_ == 0 {
                        v___x_1309_ = v___x_1306_;
                        v_isShared_1310_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1307_);
                        leanh::lean_dec(v___x_1306_);
                        v___x_1309_ = leanh::lean_box(0);
                        v_isShared_1310_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1306_);
                    v___x_1317_ =
                        l_Lean_Meta_mkFreshLevelMVar(v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
                    if leanh::lean_obj_tag(v___x_1317_) == 0 {
                        v_a_1318_ = leanh::lean_ctor_get(v___x_1317_, 0);
                        leanh::lean_inc_n(v_a_1318_, 2);
                        leanh::lean_dec_ref_known(v___x_1317_, 1);
                        v___x_1319_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(v_a_1318_);
                        v___x_1320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1320_, 0, v___x_1319_);
                        v___x_1321_ = 0;
                        v___x_1322_ = leanh::lean_box(0);
                        v___x_1323_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_1320_,
                            v___x_1321_,
                            v___x_1322_,
                            v_a_1301_,
                            v_a_1302_,
                            v_a_1303_,
                            v_a_1304_,
                        );
                        if leanh::lean_obj_tag(v___x_1323_) == 0 {
                            v_a_1324_ = leanh::lean_ctor_get(v___x_1323_, 0);
                            leanh::lean_inc_n(v_a_1324_, 2);
                            leanh::lean_dec_ref_known(v___x_1323_, 1);
                            v___x_1325_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3;
                            v___x_1326_ = leanh::lean_box(0);
                            leanh::lean_inc(v_a_1318_);
                            v___x_1327_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1327_, 0, v_a_1318_);
                            leanh::lean_ctor_set(v___x_1327_, 1, v___x_1326_);
                            leanh::lean_inc_ref(v___x_1327_);
                            v___x_1328_ = l_Lean_mkConst(v___x_1325_, v___x_1327_);
                            v___x_1329_ = l_Lean_Expr_app___override(v___x_1328_, v_a_1324_);
                            v___x_1330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1330_, 0, v___x_1329_);
                            v___x_1331_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_1330_,
                                v___x_1321_,
                                v___x_1322_,
                                v_a_1301_,
                                v_a_1302_,
                                v_a_1303_,
                                v_a_1304_,
                            );
                            if leanh::lean_obj_tag(v___x_1331_) == 0 {
                                v_a_1332_ = leanh::lean_ctor_get(v___x_1331_, 0);
                                leanh::lean_inc_n(v_a_1332_, 2);
                                leanh::lean_dec_ref_known(v___x_1331_, 1);
                                v___x_1333_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6;
                                v___x_1334_ = l_Lean_mkConst(v___x_1333_, v___x_1327_);
                                leanh::lean_inc(v_a_1324_);
                                leanh::lean_inc_ref(v_goal_1300_);
                                v___x_1335_ =
                                    l_Lean_mkApp3(v___x_1334_, v_goal_1300_, v_a_1324_, v_a_1332_);
                                v___x_1336_ = leanh::lean_box(0);
                                v___x_1337_ = l_Lean_Meta_synthInstance(
                                    v___x_1335_,
                                    v___x_1336_,
                                    v_a_1301_,
                                    v_a_1302_,
                                    v_a_1303_,
                                    v_a_1304_,
                                );
                                if leanh::lean_obj_tag(v___x_1337_) == 0 {
                                    v_a_1338_ = leanh::lean_ctor_get(v___x_1337_, 0);
                                    leanh::lean_inc(v_a_1338_);
                                    leanh::lean_dec_ref_known(v___x_1337_, 1);
                                    v___x_1339_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(v_a_1318_, v_a_1302_);
                                    v_a_1340_ = leanh::lean_ctor_get(v___x_1339_, 0);
                                    v_isSharedCheck_1363_ =
                                        (!leanh::lean_is_exclusive(v___x_1339_)) as u8;
                                    if v_isSharedCheck_1363_ == 0 {
                                        v___x_1342_ = v___x_1339_;
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1340_);
                                        leanh::lean_dec(v___x_1339_);
                                        v___x_1342_ = leanh::lean_box(0);
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1332_);
                                    leanh::lean_dec(v_a_1324_);
                                    leanh::lean_dec(v_a_1318_);
                                    leanh::lean_dec_ref(v_goal_1300_);
                                    v_a_1364_ = leanh::lean_ctor_get(v___x_1337_, 0);
                                    v_isSharedCheck_1371_ =
                                        (!leanh::lean_is_exclusive(v___x_1337_)) as u8;
                                    if v_isSharedCheck_1371_ == 0 {
                                        v___x_1366_ = v___x_1337_;
                                        v_isShared_1367_ = v_isSharedCheck_1371_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1364_);
                                        leanh::lean_dec(v___x_1337_);
                                        v___x_1366_ = leanh::lean_box(0);
                                        v_isShared_1367_ = v_isSharedCheck_1371_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref_known(v___x_1327_, 2);
                                leanh::lean_dec(v_a_1324_);
                                leanh::lean_dec(v_a_1318_);
                                leanh::lean_dec_ref(v_goal_1300_);
                                v_a_1372_ = leanh::lean_ctor_get(v___x_1331_, 0);
                                v_isSharedCheck_1379_ =
                                    (!leanh::lean_is_exclusive(v___x_1331_)) as u8;
                                if v_isSharedCheck_1379_ == 0 {
                                    v___x_1374_ = v___x_1331_;
                                    v_isShared_1375_ = v_isSharedCheck_1379_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1372_);
                                    leanh::lean_dec(v___x_1331_);
                                    v___x_1374_ = leanh::lean_box(0);
                                    v_isShared_1375_ = v_isSharedCheck_1379_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1318_);
                            leanh::lean_dec_ref(v_goal_1300_);
                            v_a_1380_ = leanh::lean_ctor_get(v___x_1323_, 0);
                            v_isSharedCheck_1387_ =
                                (!leanh::lean_is_exclusive(v___x_1323_)) as u8;
                            if v_isSharedCheck_1387_ == 0 {
                                v___x_1382_ = v___x_1323_;
                                v_isShared_1383_ = v_isSharedCheck_1387_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1380_);
                                leanh::lean_dec(v___x_1323_);
                                v___x_1382_ = leanh::lean_box(0);
                                v_isShared_1383_ = v_isSharedCheck_1387_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_goal_1300_);
                        v_a_1388_ = leanh::lean_ctor_get(v___x_1317_, 0);
                        v_isSharedCheck_1395_ =
                            (!leanh::lean_is_exclusive(v___x_1317_)) as u8;
                        if v_isSharedCheck_1395_ == 0 {
                            v___x_1390_ = v___x_1317_;
                            v_isShared_1391_ = v_isSharedCheck_1395_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1388_);
                            leanh::lean_dec(v___x_1317_);
                            v___x_1390_ = leanh::lean_box(0);
                            v_isShared_1391_ = v_isSharedCheck_1395_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1311_ = leanh::lean_box(0);
                v___x_1312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1312_, 0, v_val_1307_);
                leanh::lean_ctor_set(v___x_1312_, 1, v___x_1311_);
                if v_isShared_1310_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1309_, 0);
                    leanh::lean_ctor_set(v___x_1309_, 0, v___x_1312_);
                    v___x_1314_ = v___x_1309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
                    v___x_1314_ = v_reuseFailAlloc_1315_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1314_;
            }
            3 => {
                v___x_1344_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9;
                leanh::lean_inc(v_a_1340_);
                v___x_1345_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1345_, 0, v_a_1340_);
                leanh::lean_ctor_set(v___x_1345_, 1, v___x_1326_);
                v___x_1346_ = l_Lean_mkConst(v___x_1344_, v___x_1345_);
                leanh::lean_inc(v_a_1332_);
                leanh::lean_inc(v_a_1324_);
                v___x_1347_ =
                    l_Lean_mkApp4(v___x_1346_, v_a_1324_, v_a_1332_, v_goal_1300_, v_a_1338_);
                v___x_1348_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_1332_, v_a_1302_);
                v_a_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                v_isSharedCheck_1362_ = (!leanh::lean_is_exclusive(v___x_1348_)) as u8;
                if v_isSharedCheck_1362_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    v_isShared_1352_ = v_isSharedCheck_1362_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1349_);
                    leanh::lean_dec(v___x_1348_);
                    v___x_1351_ = leanh::lean_box(0);
                    v_isShared_1352_ = v_isSharedCheck_1362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_a_1324_);
                leanh::lean_inc(v_a_1340_);
                v___x_1353_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_a_1340_, v_a_1324_);
                v___x_1354_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1354_, 0, v_a_1340_);
                leanh::lean_ctor_set(v___x_1354_, 1, v_a_1324_);
                leanh::lean_ctor_set(v___x_1354_, 2, v___x_1353_);
                leanh::lean_ctor_set(v___x_1354_, 3, v_a_1349_);
                if v_isShared_1343_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1342_, 1);
                    leanh::lean_ctor_set(v___x_1342_, 0, v___x_1347_);
                    v___x_1356_ = v___x_1342_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1347_);
                    v___x_1356_ = v_reuseFailAlloc_1361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1357_, 0, v___x_1354_);
                leanh::lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                if v_isShared_1352_ == 0 {
                    leanh::lean_ctor_set(v___x_1351_, 0, v___x_1357_);
                    v___x_1359_ = v___x_1351_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
                    v___x_1359_ = v_reuseFailAlloc_1360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1359_;
            }
            7 => {
                if v_isShared_1367_ == 0 {
                    v___x_1369_ = v___x_1366_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
                    v___x_1369_ = v_reuseFailAlloc_1370_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1369_;
            }
            9 => {
                if v_isShared_1375_ == 0 {
                    v___x_1377_ = v___x_1374_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
                    v___x_1377_ = v_reuseFailAlloc_1378_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1377_;
            }
            11 => {
                if v_isShared_1383_ == 0 {
                    v___x_1385_ = v___x_1382_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1385_;
            }
            13 => {
                if v_isShared_1391_ == 0 {
                    v___x_1393_ = v___x_1390_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStart___boxed(
    mut v_goal_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(
        v_goal_1396_,
        v_a_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
    );
    leanh::lean_dec(v_a_1400_);
    leanh::lean_dec_ref(v_a_1399_);
    leanh::lean_dec(v_a_1398_);
    leanh::lean_dec_ref(v_a_1397_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(
    mut v_mvarId_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_a_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1422_: u8 = 0;
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1403_,
                    v_x_1404_,
                    v___y_1405_,
                    v___y_1406_,
                    v___y_1407_,
                    v___y_1408_,
                );
                if leanh::lean_obj_tag(v___x_1410_) == 0 {
                    v_a_1411_ = leanh::lean_ctor_get(v___x_1410_, 0);
                    v_isSharedCheck_1418_ = (!leanh::lean_is_exclusive(v___x_1410_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1410_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1411_);
                        leanh::lean_dec(v___x_1410_);
                        v___x_1413_ = leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1419_ = leanh::lean_ctor_get(v___x_1410_, 0);
                    v_isSharedCheck_1426_ = (!leanh::lean_is_exclusive(v___x_1410_)) as u8;
                    if v_isSharedCheck_1426_ == 0 {
                        v___x_1421_ = v___x_1410_;
                        v_isShared_1422_ = v_isSharedCheck_1426_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1419_);
                        leanh::lean_dec(v___x_1410_);
                        v___x_1421_ = leanh::lean_box(0);
                        v_isShared_1422_ = v_isSharedCheck_1426_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1414_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
                    v___x_1416_ = v_reuseFailAlloc_1417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1416_;
            }
            3 => {
                if v_isShared_1422_ == 0 {
                    v___x_1424_ = v___x_1421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
                    v___x_1424_ = v_reuseFailAlloc_1425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg___boxed(
    mut v_mvarId_1427_: *mut leanh::LeanObject,
    mut v_x_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_1427_, v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
    leanh::lean_dec(v___y_1432_);
    leanh::lean_dec_ref(v___y_1431_);
    leanh::lean_dec(v___y_1430_);
    leanh::lean_dec_ref(v___y_1429_);
    return v_res_1434_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(
    mut v_00_u03b1_1435_: *mut leanh::LeanObject,
    mut v_mvarId_1436_: *mut leanh::LeanObject,
    mut v_x_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_1436_, v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
    return v___x_1443_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___boxed(
    mut v_00_u03b1_1444_: *mut leanh::LeanObject,
    mut v_mvarId_1445_: *mut leanh::LeanObject,
    mut v_x_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(
            v_00_u03b1_1444_,
            v_mvarId_1445_,
            v_x_1446_,
            v___y_1447_,
            v___y_1448_,
            v___y_1449_,
            v___y_1450_,
        );
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    leanh::lean_dec(v___y_1448_);
    leanh::lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_x_1453_: *mut leanh::LeanObject,
    mut v_x_1454_: *mut leanh::LeanObject,
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_x_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1457_ = leanh::lean_ctor_get(v_x_1453_, 0);
                v_vs_1458_ = leanh::lean_ctor_get(v_x_1453_, 1);
                v_isSharedCheck_1482_ = (!leanh::lean_is_exclusive(v_x_1453_)) as u8;
                if v_isSharedCheck_1482_ == 0 {
                    v___x_1460_ = v_x_1453_;
                    v_isShared_1461_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1458_);
                    leanh::lean_inc(v_ks_1457_);
                    leanh::lean_dec(v_x_1453_);
                    v___x_1460_ = leanh::lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1462_ = lean_array_get_size(v_ks_1457_);
                v___x_1463_ = lean_nat_dec_lt(v_x_1454_, v___x_1462_);
                if v___x_1463_ == 0 {
                    leanh::lean_dec(v_x_1454_);
                    v___x_1464_ = lean_array_push(v_ks_1457_, v_x_1455_);
                    v___x_1465_ = lean_array_push(v_vs_1458_, v_x_1456_);
                    if v_isShared_1461_ == 0 {
                        leanh::lean_ctor_set(v___x_1460_, 1, v___x_1465_);
                        leanh::lean_ctor_set(v___x_1460_, 0, v___x_1464_);
                        v___x_1467_ = v___x_1460_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1464_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1465_);
                        v___x_1467_ = v_reuseFailAlloc_1468_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1469_ = lean_array_fget_borrowed(v_ks_1457_, v_x_1454_);
                    v___x_1470_ = l_Lean_instBEqMVarId_beq(v_x_1455_, v_k_x27_1469_);
                    if v___x_1470_ == 0 {
                        if v_isShared_1461_ == 0 {
                            v___x_1472_ = v___x_1460_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1476_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_ks_1457_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_vs_1458_);
                            v___x_1472_ = v_reuseFailAlloc_1476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1477_ = lean_array_fset(v_ks_1457_, v_x_1454_, v_x_1455_);
                        v___x_1478_ = lean_array_fset(v_vs_1458_, v_x_1454_, v_x_1456_);
                        leanh::lean_dec(v_x_1454_);
                        if v_isShared_1461_ == 0 {
                            leanh::lean_ctor_set(v___x_1460_, 1, v___x_1478_);
                            leanh::lean_ctor_set(v___x_1460_, 0, v___x_1477_);
                            v___x_1480_ = v___x_1460_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1481_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
                            v___x_1480_ = v_reuseFailAlloc_1481_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1467_;
            }
            3 => {
                v___x_1473_ = leanh::lean_unsigned_to_nat(1);
                v___x_1474_ = lean_nat_add(v_x_1454_, v___x_1473_);
                leanh::lean_dec(v_x_1454_);
                v_x_1453_ = v___x_1472_;
                v_x_1454_ = v___x_1474_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_n_1483_: *mut leanh::LeanObject,
    mut v_k_1484_: *mut leanh::LeanObject,
    mut v_v_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = leanh::lean_unsigned_to_nat(0);
    v___x_1487_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_1483_, v___x_1486_, v_k_1484_, v_v_1485_);
    return v___x_1487_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1488_: usize = 0;
    let mut v___x_1489_: usize = 0;
    let mut v___x_1490_: usize = 0;
    v___x_1488_ = 5usize;
    v___x_1489_ = 1usize;
    v___x_1490_ = lean_usize_shift_left(v___x_1489_, v___x_1488_);
    return v___x_1490_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    v___x_1491_ = 1usize;
    v___x_1492_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1493_ = lean_usize_sub(v___x_1492_, v___x_1491_);
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(
    mut v_x_1495_: *mut leanh::LeanObject,
    mut v_x_1496_: usize,
    mut v_x_1497_: usize,
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_x_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: usize = 0;
    let mut v___x_1502_: usize = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v_j_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v_v_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_node_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: u8 = 0;
    let mut v_ks_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1495_) == 0 {
                    v_es_1500_ = leanh::lean_ctor_get(v_x_1495_, 0);
                    v___x_1501_ = 5usize;
                    v___x_1502_ = 1usize;
                    v___x_1503_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_1504_ = lean_usize_land(v_x_1496_, v___x_1503_);
                    v_j_1505_ = lean_usize_to_nat(v___x_1504_);
                    v___x_1506_ = lean_array_get_size(v_es_1500_);
                    v___x_1507_ = lean_nat_dec_lt(v_j_1505_, v___x_1506_);
                    if v___x_1507_ == 0 {
                        leanh::lean_dec(v_j_1505_);
                        leanh::lean_dec(v_x_1499_);
                        leanh::lean_dec(v_x_1498_);
                        return v_x_1495_;
                    } else {
                        leanh::lean_inc_ref(v_es_1500_);
                        v_isSharedCheck_1544_ = (!leanh::lean_is_exclusive(v_x_1495_)) as u8;
                        if v_isSharedCheck_1544_ == 0 {
                            v_unused_1545_ = leanh::lean_ctor_get(v_x_1495_, 0);
                            leanh::lean_dec(v_unused_1545_);
                            v___x_1509_ = v_x_1495_;
                            v_isShared_1510_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1495_);
                            v___x_1509_ = leanh::lean_box(0);
                            v_isShared_1510_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1546_ = leanh::lean_ctor_get(v_x_1495_, 0);
                    v_vs_1547_ = leanh::lean_ctor_get(v_x_1495_, 1);
                    v_isSharedCheck_1567_ = (!leanh::lean_is_exclusive(v_x_1495_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1549_ = v_x_1495_;
                        v_isShared_1550_ = v_isSharedCheck_1567_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1547_);
                        leanh::lean_inc(v_ks_1546_);
                        leanh::lean_dec(v_x_1495_);
                        v___x_1549_ = leanh::lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1567_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1511_ = lean_array_fget(v_es_1500_, v_j_1505_);
                v___x_1512_ = leanh::lean_box(0);
                v_xs_x27_1513_ = lean_array_fset(v_es_1500_, v_j_1505_, v___x_1512_);
                match leanh::lean_obj_tag(v_v_1511_) {
                    0 => {
                        v_key_1520_ = leanh::lean_ctor_get(v_v_1511_, 0);
                        v_val_1521_ = leanh::lean_ctor_get(v_v_1511_, 1);
                        v_isSharedCheck_1531_ = (!leanh::lean_is_exclusive(v_v_1511_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1523_ = v_v_1511_;
                            v_isShared_1524_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1521_);
                            leanh::lean_inc(v_key_1520_);
                            leanh::lean_dec(v_v_1511_);
                            v___x_1523_ = leanh::lean_box(0);
                            v_isShared_1524_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1532_ = leanh::lean_ctor_get(v_v_1511_, 0);
                        v_isSharedCheck_1542_ = (!leanh::lean_is_exclusive(v_v_1511_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1534_ = v_v_1511_;
                            v_isShared_1535_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1532_);
                            leanh::lean_dec(v_v_1511_);
                            v___x_1534_ = leanh::lean_box(0);
                            v_isShared_1535_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1543_, 0, v_x_1498_);
                        leanh::lean_ctor_set(v___x_1543_, 1, v_x_1499_);
                        v___y_1515_ = v___x_1543_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1516_ = lean_array_fset(v_xs_x27_1513_, v_j_1505_, v___y_1515_);
                leanh::lean_dec(v_j_1505_);
                if v_isShared_1510_ == 0 {
                    leanh::lean_ctor_set(v___x_1509_, 0, v___x_1516_);
                    v___x_1518_ = v___x_1509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
                    v___x_1518_ = v_reuseFailAlloc_1519_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1518_;
            }
            4 => {
                v___x_1525_ = l_Lean_instBEqMVarId_beq(v_x_1498_, v_key_1520_);
                if v___x_1525_ == 0 {
                    leanh::lean_del_object(v___x_1523_);
                    v___x_1526_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1520_,
                        v_val_1521_,
                        v_x_1498_,
                        v_x_1499_,
                    );
                    v___x_1527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                    v___y_1515_ = v___x_1527_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1521_);
                    leanh::lean_dec(v_key_1520_);
                    if v_isShared_1524_ == 0 {
                        leanh::lean_ctor_set(v___x_1523_, 1, v_x_1499_);
                        leanh::lean_ctor_set(v___x_1523_, 0, v_x_1498_);
                        v___x_1529_ = v___x_1523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1530_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_x_1498_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_x_1499_);
                        v___x_1529_ = v_reuseFailAlloc_1530_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1515_ = v___x_1529_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1536_ = lean_usize_shift_right(v_x_1496_, v___x_1501_);
                v___x_1537_ = lean_usize_add(v_x_1497_, v___x_1502_);
                v___x_1538_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_node_1532_, v___x_1536_, v___x_1537_, v_x_1498_, v_x_1499_);
                if v_isShared_1535_ == 0 {
                    leanh::lean_ctor_set(v___x_1534_, 0, v___x_1538_);
                    v___x_1540_ = v___x_1534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1515_ = v___x_1540_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1550_ == 0 {
                    v___x_1552_ = v___x_1549_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_ks_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_vs_1547_);
                    v___x_1552_ = v_reuseFailAlloc_1566_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v___x_1552_, v_x_1498_, v_x_1499_);
                v___x_1561_ = 7usize;
                v___x_1562_ = lean_usize_dec_le(v___x_1561_, v_x_1497_);
                if v___x_1562_ == 0 {
                    v___x_1563_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1553_);
                    v___x_1564_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
                    leanh::lean_dec(v___x_1563_);
                    v___y_1555_ = v___x_1565_;
                    state = 10;
                    continue;
                } else {
                    v___y_1555_ = v___x_1562_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1555_ == 0 {
                    v_ks_1556_ = leanh::lean_ctor_get(v_newNode_1553_, 0);
                    leanh::lean_inc_ref(v_ks_1556_);
                    v_vs_1557_ = leanh::lean_ctor_get(v_newNode_1553_, 1);
                    leanh::lean_inc_ref(v_vs_1557_);
                    leanh::lean_dec_ref(v_newNode_1553_);
                    v___x_1558_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1559_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_1560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1497_, v_ks_1556_, v_vs_1557_, v___x_1558_, v___x_1559_);
                    leanh::lean_dec_ref(v_vs_1557_);
                    leanh::lean_dec_ref(v_ks_1556_);
                    return v___x_1560_;
                } else {
                    return v_newNode_1553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_depth_1568_: usize,
    mut v_keys_1569_: *mut leanh::LeanObject,
    mut v_vals_1570_: *mut leanh::LeanObject,
    mut v_i_1571_: *mut leanh::LeanObject,
    mut v_entries_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v_k_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u64 = 0;
    let mut v_h_1578_: usize = 0;
    let mut v___x_1579_: usize = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: usize = 0;
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v_h_1584_: usize = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1573_ = lean_array_get_size(v_keys_1569_);
                v___x_1574_ = lean_nat_dec_lt(v_i_1571_, v___x_1573_);
                if v___x_1574_ == 0 {
                    leanh::lean_dec(v_i_1571_);
                    return v_entries_1572_;
                } else {
                    v_k_1575_ = lean_array_fget_borrowed(v_keys_1569_, v_i_1571_);
                    v_v_1576_ = lean_array_fget_borrowed(v_vals_1570_, v_i_1571_);
                    v___x_1577_ = l_Lean_instHashableMVarId_hash(v_k_1575_);
                    v_h_1578_ = lean_uint64_to_usize(v___x_1577_);
                    v___x_1579_ = 5usize;
                    v___x_1580_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1581_ = 1usize;
                    v___x_1582_ = lean_usize_sub(v_depth_1568_, v___x_1581_);
                    v___x_1583_ = lean_usize_mul(v___x_1579_, v___x_1582_);
                    v_h_1584_ = lean_usize_shift_right(v_h_1578_, v___x_1583_);
                    v___x_1585_ = lean_nat_add(v_i_1571_, v___x_1580_);
                    leanh::lean_dec(v_i_1571_);
                    leanh::lean_inc(v_v_1576_);
                    leanh::lean_inc(v_k_1575_);
                    v___x_1586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_entries_1572_, v_h_1584_, v_depth_1568_, v_k_1575_, v_v_1576_);
                    v_i_1571_ = v___x_1585_;
                    v_entries_1572_ = v___x_1586_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_depth_1588_: *mut leanh::LeanObject,
    mut v_keys_1589_: *mut leanh::LeanObject,
    mut v_vals_1590_: *mut leanh::LeanObject,
    mut v_i_1591_: *mut leanh::LeanObject,
    mut v_entries_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1593_: usize = 0;
    let mut v_res_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1593_ = leanh::lean_unbox_usize(v_depth_1588_);
    leanh::lean_dec(v_depth_1588_);
    v_res_1594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_1593_, v_keys_1589_, v_vals_1590_, v_i_1591_, v_entries_1592_);
    leanh::lean_dec_ref(v_vals_1590_);
    leanh::lean_dec_ref(v_keys_1589_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_1595_: *mut leanh::LeanObject,
    mut v_x_1596_: *mut leanh::LeanObject,
    mut v_x_1597_: *mut leanh::LeanObject,
    mut v_x_1598_: *mut leanh::LeanObject,
    mut v_x_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3527__boxed_1600_: usize = 0;
    let mut v_x_3528__boxed_1601_: usize = 0;
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3527__boxed_1600_ = leanh::lean_unbox_usize(v_x_1596_);
    leanh::lean_dec(v_x_1596_);
    v_x_3528__boxed_1601_ = leanh::lean_unbox_usize(v_x_1597_);
    leanh::lean_dec(v_x_1597_);
    v_res_1602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1595_, v_x_3527__boxed_1600_, v_x_3528__boxed_1601_, v_x_1598_, v_x_1599_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(
    mut v_x_1603_: *mut leanh::LeanObject,
    mut v_x_1604_: *mut leanh::LeanObject,
    mut v_x_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: u64 = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_instHashableMVarId_hash(v_x_1604_);
    v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
    v___x_1608_ = 1usize;
    v___x_1609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1603_, v___x_1607_, v___x_1608_, v_x_1604_, v_x_1605_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
    mut v_mvarId_1610_: *mut leanh::LeanObject,
    mut v_val_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v_depth_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1614_ = lean_st_ref_take(v___y_1612_);
                v_mctx_1615_ = leanh::lean_ctor_get(v___x_1614_, 0);
                v_cache_1616_ = leanh::lean_ctor_get(v___x_1614_, 1);
                v_zetaDeltaFVarIds_1617_ = leanh::lean_ctor_get(v___x_1614_, 2);
                v_postponed_1618_ = leanh::lean_ctor_get(v___x_1614_, 3);
                v_diag_1619_ = leanh::lean_ctor_get(v___x_1614_, 4);
                v_isSharedCheck_1647_ = (!leanh::lean_is_exclusive(v___x_1614_)) as u8;
                if v_isSharedCheck_1647_ == 0 {
                    v___x_1621_ = v___x_1614_;
                    v_isShared_1622_ = v_isSharedCheck_1647_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1619_);
                    leanh::lean_inc(v_postponed_1618_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1617_);
                    leanh::lean_inc(v_cache_1616_);
                    leanh::lean_inc(v_mctx_1615_);
                    leanh::lean_dec(v___x_1614_);
                    v___x_1621_ = leanh::lean_box(0);
                    v_isShared_1622_ = v_isSharedCheck_1647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1623_ = leanh::lean_ctor_get(v_mctx_1615_, 0);
                v_levelAssignDepth_1624_ = leanh::lean_ctor_get(v_mctx_1615_, 1);
                v_lmvarCounter_1625_ = leanh::lean_ctor_get(v_mctx_1615_, 2);
                v_mvarCounter_1626_ = leanh::lean_ctor_get(v_mctx_1615_, 3);
                v_lDecls_1627_ = leanh::lean_ctor_get(v_mctx_1615_, 4);
                v_decls_1628_ = leanh::lean_ctor_get(v_mctx_1615_, 5);
                v_userNames_1629_ = leanh::lean_ctor_get(v_mctx_1615_, 6);
                v_lAssignment_1630_ = leanh::lean_ctor_get(v_mctx_1615_, 7);
                v_eAssignment_1631_ = leanh::lean_ctor_get(v_mctx_1615_, 8);
                v_dAssignment_1632_ = leanh::lean_ctor_get(v_mctx_1615_, 9);
                v_isSharedCheck_1646_ = (!leanh::lean_is_exclusive(v_mctx_1615_)) as u8;
                if v_isSharedCheck_1646_ == 0 {
                    v___x_1634_ = v_mctx_1615_;
                    v_isShared_1635_ = v_isSharedCheck_1646_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1632_);
                    leanh::lean_inc(v_eAssignment_1631_);
                    leanh::lean_inc(v_lAssignment_1630_);
                    leanh::lean_inc(v_userNames_1629_);
                    leanh::lean_inc(v_decls_1628_);
                    leanh::lean_inc(v_lDecls_1627_);
                    leanh::lean_inc(v_mvarCounter_1626_);
                    leanh::lean_inc(v_lmvarCounter_1625_);
                    leanh::lean_inc(v_levelAssignDepth_1624_);
                    leanh::lean_inc(v_depth_1623_);
                    leanh::lean_dec(v_mctx_1615_);
                    v___x_1634_ = leanh::lean_box(0);
                    v_isShared_1635_ = v_isSharedCheck_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_eAssignment_1631_, v_mvarId_1610_, v_val_1611_);
                if v_isShared_1635_ == 0 {
                    leanh::lean_ctor_set(v___x_1634_, 8, v___x_1636_);
                    v___x_1638_ = v___x_1634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_depth_1623_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1645_,
                        1,
                        v_levelAssignDepth_1624_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_lmvarCounter_1625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_mvarCounter_1626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_lDecls_1627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_decls_1628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_userNames_1629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_lAssignment_1630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 8, v___x_1636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 9, v_dAssignment_1632_);
                    v___x_1638_ = v_reuseFailAlloc_1645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1622_ == 0 {
                    leanh::lean_ctor_set(v___x_1621_, 0, v___x_1638_);
                    v___x_1640_ = v___x_1621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_cache_1616_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1644_,
                        2,
                        v_zetaDeltaFVarIds_1617_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_postponed_1618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_diag_1619_);
                    v___x_1640_ = v_reuseFailAlloc_1644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1641_ = lean_st_ref_set(v___y_1612_, v___x_1640_);
                v___x_1642_ = leanh::lean_box(0);
                v___x_1643_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1643_, 0, v___x_1642_);
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg___boxed(
    mut v_mvarId_1648_: *mut leanh::LeanObject,
    mut v_val_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
            v_mvarId_1648_,
            v_val_1649_,
            v___y_1650_,
        );
    leanh::lean_dec(v___y_1650_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(
    mut v_msgData_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_st_ref_get(v___y_1657_);
    v_env_1660_ = leanh::lean_ctor_get(v___x_1659_, 0);
    leanh::lean_inc_ref(v_env_1660_);
    leanh::lean_dec(v___x_1659_);
    v___x_1661_ = lean_st_ref_get(v___y_1655_);
    v_mctx_1662_ = leanh::lean_ctor_get(v___x_1661_, 0);
    leanh::lean_inc_ref(v_mctx_1662_);
    leanh::lean_dec(v___x_1661_);
    v_lctx_1663_ = leanh::lean_ctor_get(v___y_1654_, 2);
    v_options_1664_ = leanh::lean_ctor_get(v___y_1656_, 2);
    leanh::lean_inc_ref(v_options_1664_);
    leanh::lean_inc_ref(v_lctx_1663_);
    v___x_1665_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1665_, 0, v_env_1660_);
    leanh::lean_ctor_set(v___x_1665_, 1, v_mctx_1662_);
    leanh::lean_ctor_set(v___x_1665_, 2, v_lctx_1663_);
    leanh::lean_ctor_set(v___x_1665_, 3, v_options_1664_);
    v___x_1666_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
    leanh::lean_ctor_set(v___x_1666_, 1, v_msgData_1653_);
    v___x_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2___boxed(
    mut v_msgData_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msgData_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec_ref(v___y_1671_);
    leanh::lean_dec(v___y_1670_);
    leanh::lean_dec_ref(v___y_1669_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(
    mut v_msg_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1681_ = leanh::lean_ctor_get(v___y_1678_, 5);
                v___x_1682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
                v_a_1683_ = leanh::lean_ctor_get(v___x_1682_, 0);
                v_isSharedCheck_1691_ = (!leanh::lean_is_exclusive(v___x_1682_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1685_ = v___x_1682_;
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1683_);
                    leanh::lean_dec(v___x_1682_);
                    v___x_1685_ = leanh::lean_box(0);
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1681_);
                v___x_1687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1687_, 0, v_ref_1681_);
                leanh::lean_ctor_set(v___x_1687_, 1, v_a_1683_);
                if v_isShared_1686_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1685_, 1);
                    leanh::lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1689_ = v___x_1685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
                    v___x_1689_ = v_reuseFailAlloc_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg___boxed(
    mut v_msg_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(
            v_msg_1692_,
            v___y_1693_,
            v___y_1694_,
            v___y_1695_,
            v___y_1696_,
        );
    leanh::lean_dec(v___y_1696_);
    leanh::lean_dec_ref(v___y_1695_);
    leanh::lean_dec(v___y_1694_);
    leanh::lean_dec_ref(v___y_1693_);
    return v_res_1698_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0;
    v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2;
    v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4;
    v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(
    mut v_mvar_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v_proof_x3f_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v_val_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_unused_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_a_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_unused_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut v_unused_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_a_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_a_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_a_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v_a_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvar_1708_);
                v___x_1714_ = l_Lean_MVarId_getType(
                    v_mvar_1708_,
                    v___y_1709_,
                    v___y_1710_,
                    v___y_1711_,
                    v___y_1712_,
                );
                if leanh::lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    leanh::lean_inc(v_a_1715_);
                    leanh::lean_dec_ref_known(v___x_1714_, 1);
                    v___x_1716_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_1715_, v___y_1710_);
                    v_a_1717_ = leanh::lean_ctor_get(v___x_1716_, 0);
                    leanh::lean_inc_n(v_a_1717_, 2);
                    leanh::lean_dec_ref(v___x_1716_);
                    v___x_1792_ = l_Lean_Meta_isProp(
                        v_a_1717_,
                        v___y_1709_,
                        v___y_1710_,
                        v___y_1711_,
                        v___y_1712_,
                    );
                    if leanh::lean_obj_tag(v___x_1792_) == 0 {
                        v_a_1793_ = leanh::lean_ctor_get(v___x_1792_, 0);
                        leanh::lean_inc(v_a_1793_);
                        leanh::lean_dec_ref_known(v___x_1792_, 1);
                        v___x_1794_ = (leanh::lean_unbox(v_a_1793_) as u8);
                        leanh::lean_dec(v_a_1793_);
                        if v___x_1794_ == 0 {
                            leanh::lean_inc(v___y_1712_);
                            leanh::lean_inc_ref(v___y_1711_);
                            leanh::lean_inc(v___y_1710_);
                            leanh::lean_inc_ref(v___y_1709_);
                            v___x_1795_ = lean_infer_type(
                                v_a_1717_,
                                v___y_1709_,
                                v___y_1710_,
                                v___y_1711_,
                                v___y_1712_,
                            );
                            if leanh::lean_obj_tag(v___x_1795_) == 0 {
                                v_a_1796_ = leanh::lean_ctor_get(v___x_1795_, 0);
                                leanh::lean_inc(v_a_1796_);
                                leanh::lean_dec_ref_known(v___x_1795_, 1);
                                v___x_1797_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1);
                                v___x_1798_ = l_Lean_mkMVar(v_mvar_1708_);
                                v___x_1799_ = l_Lean_MessageData_ofExpr(v___x_1798_);
                                v___x_1800_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1800_, 0, v___x_1797_);
                                leanh::lean_ctor_set(v___x_1800_, 1, v___x_1799_);
                                v___x_1801_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3);
                                v___x_1802_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                                leanh::lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                                v___x_1803_ = l_Lean_MessageData_ofExpr(v_a_1796_);
                                v___x_1804_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1804_, 0, v___x_1802_);
                                leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
                                v___x_1805_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5);
                                v___x_1806_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1806_, 0, v___x_1804_);
                                leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
                                v___x_1807_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v___x_1806_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
                                leanh::lean_dec(v___y_1712_);
                                leanh::lean_dec_ref(v___y_1711_);
                                leanh::lean_dec(v___y_1710_);
                                leanh::lean_dec_ref(v___y_1709_);
                                v_a_1808_ = leanh::lean_ctor_get(v___x_1807_, 0);
                                v_isSharedCheck_1815_ =
                                    (!leanh::lean_is_exclusive(v___x_1807_)) as u8;
                                if v_isSharedCheck_1815_ == 0 {
                                    v___x_1810_ = v___x_1807_;
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1808_);
                                    leanh::lean_dec(v___x_1807_);
                                    v___x_1810_ = leanh::lean_box(0);
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___y_1712_);
                                leanh::lean_dec_ref(v___y_1711_);
                                leanh::lean_dec(v___y_1710_);
                                leanh::lean_dec_ref(v___y_1709_);
                                leanh::lean_dec(v_mvar_1708_);
                                v_a_1816_ = leanh::lean_ctor_get(v___x_1795_, 0);
                                v_isSharedCheck_1823_ =
                                    (!leanh::lean_is_exclusive(v___x_1795_)) as u8;
                                if v_isSharedCheck_1823_ == 0 {
                                    v___x_1818_ = v___x_1795_;
                                    v_isShared_1819_ = v_isSharedCheck_1823_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1816_);
                                    leanh::lean_dec(v___x_1795_);
                                    v___x_1818_ = leanh::lean_box(0);
                                    v_isShared_1819_ = v_isSharedCheck_1823_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            v___y_1719_ = v___y_1709_;
                            v___y_1720_ = v___y_1710_;
                            v___y_1721_ = v___y_1711_;
                            v___y_1722_ = v___y_1712_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1717_);
                        leanh::lean_dec(v___y_1712_);
                        leanh::lean_dec_ref(v___y_1711_);
                        leanh::lean_dec(v___y_1710_);
                        leanh::lean_dec_ref(v___y_1709_);
                        leanh::lean_dec(v_mvar_1708_);
                        v_a_1824_ = leanh::lean_ctor_get(v___x_1792_, 0);
                        v_isSharedCheck_1831_ =
                            (!leanh::lean_is_exclusive(v___x_1792_)) as u8;
                        if v_isSharedCheck_1831_ == 0 {
                            v___x_1826_ = v___x_1792_;
                            v_isShared_1827_ = v_isSharedCheck_1831_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1824_);
                            leanh::lean_dec(v___x_1792_);
                            v___x_1826_ = leanh::lean_box(0);
                            v_isShared_1827_ = v_isSharedCheck_1831_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1712_);
                    leanh::lean_dec_ref(v___y_1711_);
                    leanh::lean_dec(v___y_1710_);
                    leanh::lean_dec_ref(v___y_1709_);
                    leanh::lean_dec(v_mvar_1708_);
                    v_a_1832_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1839_ = (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1834_ = v___x_1714_;
                        v_isShared_1835_ = v_isSharedCheck_1839_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1832_);
                        leanh::lean_dec(v___x_1714_);
                        v___x_1834_ = leanh::lean_box(0);
                        v_isShared_1835_ = v_isSharedCheck_1839_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1723_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(
                    v_a_1717_,
                    v___y_1719_,
                    v___y_1720_,
                    v___y_1721_,
                    v___y_1722_,
                );
                if leanh::lean_obj_tag(v___x_1723_) == 0 {
                    v_a_1724_ = leanh::lean_ctor_get(v___x_1723_, 0);
                    v_isSharedCheck_1783_ = (!leanh::lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1726_ = v___x_1723_;
                        v_isShared_1727_ = v_isSharedCheck_1783_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1724_);
                        leanh::lean_dec(v___x_1723_);
                        v___x_1726_ = leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1783_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1722_);
                    leanh::lean_dec_ref(v___y_1721_);
                    leanh::lean_dec(v___y_1720_);
                    leanh::lean_dec_ref(v___y_1719_);
                    leanh::lean_dec(v_mvar_1708_);
                    v_a_1784_ = leanh::lean_ctor_get(v___x_1723_, 0);
                    v_isSharedCheck_1791_ = (!leanh::lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1786_ = v___x_1723_;
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1784_);
                        leanh::lean_dec(v___x_1723_);
                        v___x_1786_ = leanh::lean_box(0);
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_proof_x3f_1728_ = leanh::lean_ctor_get(v_a_1724_, 1);
                if leanh::lean_obj_tag(v_proof_x3f_1728_) == 1 {
                    leanh::lean_inc_ref(v_proof_x3f_1728_);
                    leanh::lean_del_object(v___x_1726_);
                    v_goal_1729_ = leanh::lean_ctor_get(v_a_1724_, 0);
                    v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v_a_1724_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v_unused_1770_ = leanh::lean_ctor_get(v_a_1724_, 1);
                        leanh::lean_dec(v_unused_1770_);
                        v___x_1731_ = v_a_1724_;
                        v_isShared_1732_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_goal_1729_);
                        leanh::lean_dec(v_a_1724_);
                        v___x_1731_ = leanh::lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1722_);
                    leanh::lean_dec_ref(v___y_1721_);
                    leanh::lean_dec(v___y_1720_);
                    leanh::lean_dec_ref(v___y_1719_);
                    v_goal_1771_ = leanh::lean_ctor_get(v_a_1724_, 0);
                    v_isSharedCheck_1781_ = (!leanh::lean_is_exclusive(v_a_1724_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v_unused_1782_ = leanh::lean_ctor_get(v_a_1724_, 1);
                        leanh::lean_dec(v_unused_1782_);
                        v___x_1773_ = v_a_1724_;
                        v_isShared_1774_ = v_isSharedCheck_1781_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_goal_1771_);
                        leanh::lean_dec(v_a_1724_);
                        v___x_1773_ = leanh::lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1781_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_val_1733_ = leanh::lean_ctor_get(v_proof_x3f_1728_, 0);
                leanh::lean_inc(v_val_1733_);
                leanh::lean_dec_ref_known(v_proof_x3f_1728_, 1);
                leanh::lean_inc(v_mvar_1708_);
                v___x_1734_ = l_Lean_MVarId_getTag(
                    v_mvar_1708_,
                    v___y_1719_,
                    v___y_1720_,
                    v___y_1721_,
                    v___y_1722_,
                );
                if leanh::lean_obj_tag(v___x_1734_) == 0 {
                    v_a_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
                    leanh::lean_inc(v_a_1735_);
                    leanh::lean_dec_ref_known(v___x_1734_, 1);
                    leanh::lean_inc_ref(v_goal_1729_);
                    v___x_1736_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1729_);
                    v___x_1737_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1736_,
                        v_a_1735_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                    );
                    leanh::lean_dec(v___y_1722_);
                    leanh::lean_dec_ref(v___y_1721_);
                    leanh::lean_dec_ref(v___y_1719_);
                    if leanh::lean_obj_tag(v___x_1737_) == 0 {
                        v_a_1738_ = leanh::lean_ctor_get(v___x_1737_, 0);
                        leanh::lean_inc_n(v_a_1738_, 2);
                        leanh::lean_dec_ref_known(v___x_1737_, 1);
                        v___x_1739_ = l_Lean_Expr_app___override(v_val_1733_, v_a_1738_);
                        v___x_1740_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvar_1708_, v___x_1739_, v___y_1720_);
                        leanh::lean_dec(v___y_1720_);
                        v_isSharedCheck_1751_ =
                            (!leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1751_ == 0 {
                            v_unused_1752_ = leanh::lean_ctor_get(v___x_1740_, 0);
                            leanh::lean_dec(v_unused_1752_);
                            v___x_1742_ = v___x_1740_;
                            v_isShared_1743_ = v_isSharedCheck_1751_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1740_);
                            v___x_1742_ = leanh::lean_box(0);
                            v_isShared_1743_ = v_isSharedCheck_1751_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_1733_);
                        leanh::lean_del_object(v___x_1731_);
                        leanh::lean_dec_ref(v_goal_1729_);
                        leanh::lean_dec(v___y_1720_);
                        leanh::lean_dec(v_mvar_1708_);
                        v_a_1753_ = leanh::lean_ctor_get(v___x_1737_, 0);
                        v_isSharedCheck_1760_ =
                            (!leanh::lean_is_exclusive(v___x_1737_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1755_ = v___x_1737_;
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1753_);
                            leanh::lean_dec(v___x_1737_);
                            v___x_1755_ = leanh::lean_box(0);
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_1733_);
                    leanh::lean_del_object(v___x_1731_);
                    leanh::lean_dec_ref(v_goal_1729_);
                    leanh::lean_dec(v___y_1722_);
                    leanh::lean_dec_ref(v___y_1721_);
                    leanh::lean_dec(v___y_1720_);
                    leanh::lean_dec_ref(v___y_1719_);
                    leanh::lean_dec(v_mvar_1708_);
                    v_a_1761_ = leanh::lean_ctor_get(v___x_1734_, 0);
                    v_isSharedCheck_1768_ = (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1768_ == 0 {
                        v___x_1763_ = v___x_1734_;
                        v_isShared_1764_ = v_isSharedCheck_1768_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1761_);
                        leanh::lean_dec(v___x_1734_);
                        v___x_1763_ = leanh::lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1768_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1744_ = l_Lean_Expr_mvarId_x21(v_a_1738_);
                leanh::lean_dec(v_a_1738_);
                if v_isShared_1732_ == 0 {
                    leanh::lean_ctor_set(v___x_1731_, 1, v_goal_1729_);
                    leanh::lean_ctor_set(v___x_1731_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1731_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_goal_1729_);
                    v___x_1746_ = v_reuseFailAlloc_1750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1743_ == 0 {
                    leanh::lean_ctor_set(v___x_1742_, 0, v___x_1746_);
                    v___x_1748_ = v___x_1742_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1748_;
            }
            7 => {
                if v_isShared_1756_ == 0 {
                    v___x_1758_ = v___x_1755_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
                    v___x_1758_ = v_reuseFailAlloc_1759_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1758_;
            }
            9 => {
                if v_isShared_1764_ == 0 {
                    v___x_1766_ = v___x_1763_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
                    v___x_1766_ = v_reuseFailAlloc_1767_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1766_;
            }
            11 => {
                if v_isShared_1774_ == 0 {
                    leanh::lean_ctor_set(v___x_1773_, 1, v_goal_1771_);
                    leanh::lean_ctor_set(v___x_1773_, 0, v_mvar_1708_);
                    v___x_1776_ = v___x_1773_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1780_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_mvar_1708_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_goal_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1780_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1727_ == 0 {
                    leanh::lean_ctor_set(v___x_1726_, 0, v___x_1776_);
                    v___x_1778_ = v___x_1726_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1778_;
            }
            14 => {
                if v_isShared_1787_ == 0 {
                    v___x_1789_ = v___x_1786_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
                    v___x_1789_ = v_reuseFailAlloc_1790_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1789_;
            }
            16 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1813_;
            }
            18 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1821_;
            }
            20 => {
                if v_isShared_1827_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1829_;
            }
            22 => {
                if v_isShared_1835_ == 0 {
                    v___x_1837_ = v___x_1834_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed(
    mut v_mvar_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(
        v_mvar_1840_,
        v___y_1841_,
        v___y_1842_,
        v___y_1843_,
        v___y_1844_,
    );
    return v_res_1846_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(
    mut v_mvar_1847_: *mut leanh::LeanObject,
    mut v_a_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvar_1847_);
    v___f_1853_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1853_, 0, v_mvar_1847_);
    v___x_1854_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvar_1847_, v___f_1853_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
    return v___x_1854_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___boxed(
    mut v_mvar_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(
        v_mvar_1855_,
        v_a_1856_,
        v_a_1857_,
        v_a_1858_,
        v_a_1859_,
    );
    leanh::lean_dec(v_a_1859_);
    leanh::lean_dec_ref(v_a_1858_);
    leanh::lean_dec(v_a_1857_);
    leanh::lean_dec_ref(v_a_1856_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(
    mut v_mvarId_1862_: *mut leanh::LeanObject,
    mut v_val_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
            v_mvarId_1862_,
            v_val_1863_,
            v___y_1865_,
        );
    return v___x_1869_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___boxed(
    mut v_mvarId_1870_: *mut leanh::LeanObject,
    mut v_val_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
    mut v___y_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(
        v_mvarId_1870_,
        v_val_1871_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
    );
    leanh::lean_dec(v___y_1875_);
    leanh::lean_dec_ref(v___y_1874_);
    leanh::lean_dec(v___y_1873_);
    leanh::lean_dec_ref(v___y_1872_);
    return v_res_1877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(
    mut v_00_u03b1_1878_: *mut leanh::LeanObject,
    mut v_msg_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(
            v_msg_1879_,
            v___y_1880_,
            v___y_1881_,
            v___y_1882_,
            v___y_1883_,
        );
    return v___x_1885_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___boxed(
    mut v_00_u03b1_1886_: *mut leanh::LeanObject,
    mut v_msg_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(
        v_00_u03b1_1886_,
        v_msg_1887_,
        v___y_1888_,
        v___y_1889_,
        v___y_1890_,
        v___y_1891_,
    );
    leanh::lean_dec(v___y_1891_);
    leanh::lean_dec_ref(v___y_1890_);
    leanh::lean_dec(v___y_1889_);
    leanh::lean_dec_ref(v___y_1888_);
    return v_res_1893_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0(
    mut v_00_u03b2_1894_: *mut leanh::LeanObject,
    mut v_x_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
    mut v_x_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_x_1895_, v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1899_: *mut leanh::LeanObject,
    mut v_x_1900_: *mut leanh::LeanObject,
    mut v_x_1901_: usize,
    mut v_x_1902_: usize,
    mut v_x_1903_: *mut leanh::LeanObject,
    mut v_x_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1900_, v_x_1901_, v_x_1902_, v_x_1903_, v_x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1906_: *mut leanh::LeanObject,
    mut v_x_1907_: *mut leanh::LeanObject,
    mut v_x_1908_: *mut leanh::LeanObject,
    mut v_x_1909_: *mut leanh::LeanObject,
    mut v_x_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4149__boxed_1912_: usize = 0;
    let mut v_x_4150__boxed_1913_: usize = 0;
    let mut v_res_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4149__boxed_1912_ = leanh::lean_unbox_usize(v_x_1908_);
    leanh::lean_dec(v_x_1908_);
    v_x_4150__boxed_1913_ = leanh::lean_unbox_usize(v_x_1909_);
    leanh::lean_dec(v_x_1909_);
    v_res_1914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(v_00_u03b2_1906_, v_x_1907_, v_x_4149__boxed_1912_, v_x_4150__boxed_1913_, v_x_1910_, v_x_1911_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_1915_: *mut leanh::LeanObject,
    mut v_n_1916_: *mut leanh::LeanObject,
    mut v_k_1917_: *mut leanh::LeanObject,
    mut v_v_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1916_, v_k_1917_, v_v_1918_);
    return v___x_1919_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1920_: *mut leanh::LeanObject,
    mut v_depth_1921_: usize,
    mut v_keys_1922_: *mut leanh::LeanObject,
    mut v_vals_1923_: *mut leanh::LeanObject,
    mut v_heq_1924_: *mut leanh::LeanObject,
    mut v_i_1925_: *mut leanh::LeanObject,
    mut v_entries_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1921_, v_keys_1922_, v_vals_1923_, v_i_1925_, v_entries_1926_);
    return v___x_1927_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1928_: *mut leanh::LeanObject,
    mut v_depth_1929_: *mut leanh::LeanObject,
    mut v_keys_1930_: *mut leanh::LeanObject,
    mut v_vals_1931_: *mut leanh::LeanObject,
    mut v_heq_1932_: *mut leanh::LeanObject,
    mut v_i_1933_: *mut leanh::LeanObject,
    mut v_entries_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1935_: usize = 0;
    let mut v_res_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1935_ = leanh::lean_unbox_usize(v_depth_1929_);
    leanh::lean_dec(v_depth_1929_);
    v_res_1936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1928_, v_depth_boxed_1935_, v_keys_1930_, v_vals_1931_, v_heq_1932_, v_i_1933_, v_entries_1934_);
    leanh::lean_dec_ref(v_vals_1931_);
    leanh::lean_dec_ref(v_keys_1930_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_1937_: *mut leanh::LeanObject,
    mut v_x_1938_: *mut leanh::LeanObject,
    mut v_x_1939_: *mut leanh::LeanObject,
    mut v_x_1940_: *mut leanh::LeanObject,
    mut v_x_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1938_, v_x_1939_, v_x_1940_, v_x_1941_);
    return v___x_1942_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
    mut v_a_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_a_1945_: *mut leanh::LeanObject,
    mut v_a_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut v_unused_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut v_a_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1949_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_,
                );
                if leanh::lean_obj_tag(v___x_1949_) == 0 {
                    v_a_1950_ = leanh::lean_ctor_get(v___x_1949_, 0);
                    leanh::lean_inc(v_a_1950_);
                    leanh::lean_dec_ref_known(v___x_1949_, 1);
                    v___x_1951_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(
                        v_a_1950_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_,
                    );
                    if leanh::lean_obj_tag(v___x_1951_) == 0 {
                        v_a_1952_ = leanh::lean_ctor_get(v___x_1951_, 0);
                        leanh::lean_inc(v_a_1952_);
                        leanh::lean_dec_ref_known(v___x_1951_, 1);
                        v_fst_1953_ = leanh::lean_ctor_get(v_a_1952_, 0);
                        v___x_1954_ = leanh::lean_box(0);
                        leanh::lean_inc(v_fst_1953_);
                        v___x_1955_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1955_, 0, v_fst_1953_);
                        leanh::lean_ctor_set(v___x_1955_, 1, v___x_1954_);
                        v___x_1956_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1955_,
                            v_a_1943_,
                            v_a_1944_,
                            v_a_1945_,
                            v_a_1946_,
                            v_a_1947_,
                        );
                        if leanh::lean_obj_tag(v___x_1956_) == 0 {
                            v_isSharedCheck_1963_ =
                                (!leanh::lean_is_exclusive(v___x_1956_)) as u8;
                            if v_isSharedCheck_1963_ == 0 {
                                v_unused_1964_ = leanh::lean_ctor_get(v___x_1956_, 0);
                                leanh::lean_dec(v_unused_1964_);
                                v___x_1958_ = v___x_1956_;
                                v_isShared_1959_ = v_isSharedCheck_1963_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1956_);
                                v___x_1958_ = leanh::lean_box(0);
                                v_isShared_1959_ = v_isSharedCheck_1963_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1952_);
                            v_a_1965_ = leanh::lean_ctor_get(v___x_1956_, 0);
                            v_isSharedCheck_1972_ =
                                (!leanh::lean_is_exclusive(v___x_1956_)) as u8;
                            if v_isSharedCheck_1972_ == 0 {
                                v___x_1967_ = v___x_1956_;
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1965_);
                                leanh::lean_dec(v___x_1956_);
                                v___x_1967_ = leanh::lean_box(0);
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1951_;
                    }
                } else {
                    v_a_1973_ = leanh::lean_ctor_get(v___x_1949_, 0);
                    v_isSharedCheck_1980_ = (!leanh::lean_is_exclusive(v___x_1949_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1975_ = v___x_1949_;
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1973_);
                        leanh::lean_dec(v___x_1949_);
                        v___x_1975_ = leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1959_ == 0 {
                    leanh::lean_ctor_set(v___x_1958_, 0, v_a_1952_);
                    v___x_1961_ = v___x_1958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1952_);
                    v___x_1961_ = v_reuseFailAlloc_1962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1961_;
            }
            3 => {
                if v_isShared_1968_ == 0 {
                    v___x_1970_ = v___x_1967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
                    v___x_1970_ = v_reuseFailAlloc_1971_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1970_;
            }
            5 => {
                if v_isShared_1976_ == 0 {
                    v___x_1978_ = v___x_1975_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1979_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg___boxed(
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
    mut v_a_1983_: *mut leanh::LeanObject,
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
    mut v_a_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
        v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_,
    );
    leanh::lean_dec(v_a_1985_);
    leanh::lean_dec_ref(v_a_1984_);
    leanh::lean_dec(v_a_1983_);
    leanh::lean_dec_ref(v_a_1982_);
    leanh::lean_dec(v_a_1981_);
    return v_res_1987_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(
    mut v_a_1988_: *mut leanh::LeanObject,
    mut v_a_1989_: *mut leanh::LeanObject,
    mut v_a_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
    mut v_a_1993_: *mut leanh::LeanObject,
    mut v_a_1994_: *mut leanh::LeanObject,
    mut v_a_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
        v_a_1989_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_,
    );
    return v___x_1997_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___boxed(
    mut v_a_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
    mut v_a_2000_: *mut leanh::LeanObject,
    mut v_a_2001_: *mut leanh::LeanObject,
    mut v_a_2002_: *mut leanh::LeanObject,
    mut v_a_2003_: *mut leanh::LeanObject,
    mut v_a_2004_: *mut leanh::LeanObject,
    mut v_a_2005_: *mut leanh::LeanObject,
    mut v_a_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(
        v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_,
    );
    leanh::lean_dec(v_a_2005_);
    leanh::lean_dec_ref(v_a_2004_);
    leanh::lean_dec(v_a_2003_);
    leanh::lean_dec_ref(v_a_2002_);
    leanh::lean_dec(v_a_2001_);
    leanh::lean_dec_ref(v_a_2000_);
    leanh::lean_dec(v_a_1999_);
    leanh::lean_dec_ref(v_a_1998_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
    mut v_a_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_a_2010_: *mut leanh::LeanObject,
    mut v_a_2011_: *mut leanh::LeanObject,
    mut v_a_2012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut v_unused_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2014_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                    v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_,
                );
                if leanh::lean_obj_tag(v___x_2014_) == 0 {
                    v_isSharedCheck_2022_ = (!leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2022_ == 0 {
                        v_unused_2023_ = leanh::lean_ctor_get(v___x_2014_, 0);
                        leanh::lean_dec(v_unused_2023_);
                        v___x_2016_ = v___x_2014_;
                        v_isShared_2017_ = v_isSharedCheck_2022_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2014_);
                        v___x_2016_ = leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2022_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2024_ = leanh::lean_ctor_get(v___x_2014_, 0);
                    v_isSharedCheck_2031_ = (!leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v___x_2026_ = v___x_2014_;
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2024_);
                        leanh::lean_dec(v___x_2014_);
                        v___x_2026_ = leanh::lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2018_ = leanh::lean_box(0);
                if v_isShared_2017_ == 0 {
                    leanh::lean_ctor_set(v___x_2016_, 0, v___x_2018_);
                    v___x_2020_ = v___x_2016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
                    v___x_2020_ = v_reuseFailAlloc_2021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2020_;
            }
            3 => {
                if v_isShared_2027_ == 0 {
                    v___x_2029_ = v___x_2026_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
                    v___x_2029_ = v_reuseFailAlloc_2030_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg___boxed(
    mut v_a_2032_: *mut leanh::LeanObject,
    mut v_a_2033_: *mut leanh::LeanObject,
    mut v_a_2034_: *mut leanh::LeanObject,
    mut v_a_2035_: *mut leanh::LeanObject,
    mut v_a_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
        v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_,
    );
    leanh::lean_dec(v_a_2036_);
    leanh::lean_dec_ref(v_a_2035_);
    leanh::lean_dec(v_a_2034_);
    leanh::lean_dec_ref(v_a_2033_);
    leanh::lean_dec(v_a_2032_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(
    mut v_x_2039_: *mut leanh::LeanObject,
    mut v_a_2040_: *mut leanh::LeanObject,
    mut v_a_2041_: *mut leanh::LeanObject,
    mut v_a_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_a_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
        v_a_2041_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed(
    mut v_x_2050_: *mut leanh::LeanObject,
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
    mut v_a_2053_: *mut leanh::LeanObject,
    mut v_a_2054_: *mut leanh::LeanObject,
    mut v_a_2055_: *mut leanh::LeanObject,
    mut v_a_2056_: *mut leanh::LeanObject,
    mut v_a_2057_: *mut leanh::LeanObject,
    mut v_a_2058_: *mut leanh::LeanObject,
    mut v_a_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(
        v_x_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_,
        v_a_2058_,
    );
    leanh::lean_dec(v_a_2058_);
    leanh::lean_dec_ref(v_a_2057_);
    leanh::lean_dec(v_a_2056_);
    leanh::lean_dec_ref(v_a_2055_);
    leanh::lean_dec(v_a_2054_);
    leanh::lean_dec_ref(v_a_2053_);
    leanh::lean_dec(v_a_2052_);
    leanh::lean_dec_ref(v_a_2051_);
    leanh::lean_dec(v_x_2050_);
    return v_res_2060_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1()
-> *mut leanh::LeanObject {
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2080_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3;
    v___x_2081_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6;
    v___x_2082_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2079_,
        v___x_2080_,
        v___x_2081_,
        v___x_2082_,
    );
    return v___x_2083_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___boxed(
    mut v_a_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
    return v_res_2085_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
    mut v_e_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = l_Lean_Expr_hasMVar(v_e_2086_);
                if v___x_2089_ == 0 {
                    v___x_2090_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2090_, 0, v_e_2086_);
                    return v___x_2090_;
                } else {
                    v___x_2091_ = lean_st_ref_get(v___y_2087_);
                    v_mctx_2092_ = leanh::lean_ctor_get(v___x_2091_, 0);
                    leanh::lean_inc_ref(v_mctx_2092_);
                    leanh::lean_dec(v___x_2091_);
                    v___x_2093_ = l_Lean_instantiateMVarsCore(v_mctx_2092_, v_e_2086_);
                    v_fst_2094_ = leanh::lean_ctor_get(v___x_2093_, 0);
                    leanh::lean_inc(v_fst_2094_);
                    v_snd_2095_ = leanh::lean_ctor_get(v___x_2093_, 1);
                    leanh::lean_inc(v_snd_2095_);
                    leanh::lean_dec_ref(v___x_2093_);
                    v___x_2096_ = lean_st_ref_take(v___y_2087_);
                    v_cache_2097_ = leanh::lean_ctor_get(v___x_2096_, 1);
                    v_zetaDeltaFVarIds_2098_ = leanh::lean_ctor_get(v___x_2096_, 2);
                    v_postponed_2099_ = leanh::lean_ctor_get(v___x_2096_, 3);
                    v_diag_2100_ = leanh::lean_ctor_get(v___x_2096_, 4);
                    v_isSharedCheck_2109_ = (!leanh::lean_is_exclusive(v___x_2096_)) as u8;
                    if v_isSharedCheck_2109_ == 0 {
                        v_unused_2110_ = leanh::lean_ctor_get(v___x_2096_, 0);
                        leanh::lean_dec(v_unused_2110_);
                        v___x_2102_ = v___x_2096_;
                        v_isShared_2103_ = v_isSharedCheck_2109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2100_);
                        leanh::lean_inc(v_postponed_2099_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2098_);
                        leanh::lean_inc(v_cache_2097_);
                        leanh::lean_dec(v___x_2096_);
                        v___x_2102_ = leanh::lean_box(0);
                        v_isShared_2103_ = v_isSharedCheck_2109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2103_ == 0 {
                    leanh::lean_ctor_set(v___x_2102_, 0, v_snd_2095_);
                    v___x_2105_ = v___x_2102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_snd_2095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_cache_2097_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2108_,
                        2,
                        v_zetaDeltaFVarIds_2098_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_postponed_2099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_diag_2100_);
                    v___x_2105_ = v_reuseFailAlloc_2108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2106_ = lean_st_ref_set(v___y_2087_, v___x_2105_);
                v___x_2107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2107_, 0, v_fst_2094_);
                return v___x_2107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg___boxed(
    mut v_e_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
            v_e_2111_,
            v___y_2112_,
        );
    leanh::lean_dec(v___y_2112_);
    return v_res_2114_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(
    mut v_e_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
            v_e_2115_,
            v___y_2121_,
        );
    return v___x_2125_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___boxed(
    mut v_e_2126_: *mut leanh::LeanObject,
    mut v___y_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
    mut v___y_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2136_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(
        v_e_2126_,
        v___y_2127_,
        v___y_2128_,
        v___y_2129_,
        v___y_2130_,
        v___y_2131_,
        v___y_2132_,
        v___y_2133_,
        v___y_2134_,
    );
    leanh::lean_dec(v___y_2134_);
    leanh::lean_dec_ref(v___y_2133_);
    leanh::lean_dec(v___y_2132_);
    leanh::lean_dec_ref(v___y_2131_);
    leanh::lean_dec(v___y_2130_);
    leanh::lean_dec_ref(v___y_2129_);
    leanh::lean_dec(v___y_2128_);
    leanh::lean_dec_ref(v___y_2127_);
    return v_res_2136_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(
    mut v_x_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2141_);
    leanh::lean_inc_ref(v___y_2140_);
    leanh::lean_inc(v___y_2139_);
    leanh::lean_inc_ref(v___y_2138_);
    v___x_2147_ = leanh::lean_apply_9(
        v_x_2137_,
        v___y_2138_,
        v___y_2139_,
        v___y_2140_,
        v___y_2141_,
        v___y_2142_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
        leanh::lean_box(0),
    );
    return v___x_2147_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed(
    mut v_x_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
    mut v___y_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(v_x_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
    leanh::lean_dec(v___y_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    leanh::lean_dec(v___y_2150_);
    leanh::lean_dec_ref(v___y_2149_);
    return v_res_2158_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(
    mut v_mvarId_2159_: *mut leanh::LeanObject,
    mut v_x_2160_: *mut leanh::LeanObject,
    mut v___y_2161_: *mut leanh::LeanObject,
    mut v___y_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2164_);
                leanh::lean_inc_ref(v___y_2163_);
                leanh::lean_inc(v___y_2162_);
                leanh::lean_inc_ref(v___y_2161_);
                v___f_2170_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_2170_, 0, v_x_2160_);
                leanh::lean_closure_set(v___f_2170_, 1, v___y_2161_);
                leanh::lean_closure_set(v___f_2170_, 2, v___y_2162_);
                leanh::lean_closure_set(v___f_2170_, 3, v___y_2163_);
                leanh::lean_closure_set(v___f_2170_, 4, v___y_2164_);
                v___x_2171_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2159_,
                    v___f_2170_,
                    v___y_2165_,
                    v___y_2166_,
                    v___y_2167_,
                    v___y_2168_,
                );
                if leanh::lean_obj_tag(v___x_2171_) == 0 {
                    return v___x_2171_;
                } else {
                    v_a_2172_ = leanh::lean_ctor_get(v___x_2171_, 0);
                    v_isSharedCheck_2179_ = (!leanh::lean_is_exclusive(v___x_2171_)) as u8;
                    if v_isSharedCheck_2179_ == 0 {
                        v___x_2174_ = v___x_2171_;
                        v_isShared_2175_ = v_isSharedCheck_2179_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2172_);
                        leanh::lean_dec(v___x_2171_);
                        v___x_2174_ = leanh::lean_box(0);
                        v_isShared_2175_ = v_isSharedCheck_2179_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2175_ == 0 {
                    v___x_2177_ = v___x_2174_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
                    v___x_2177_ = v_reuseFailAlloc_2178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___boxed(
    mut v_mvarId_2180_: *mut leanh::LeanObject,
    mut v_x_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v___y_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2191_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(
            v_mvarId_2180_,
            v_x_2181_,
            v___y_2182_,
            v___y_2183_,
            v___y_2184_,
            v___y_2185_,
            v___y_2186_,
            v___y_2187_,
            v___y_2188_,
            v___y_2189_,
        );
    leanh::lean_dec(v___y_2189_);
    leanh::lean_dec_ref(v___y_2188_);
    leanh::lean_dec(v___y_2187_);
    leanh::lean_dec_ref(v___y_2186_);
    leanh::lean_dec(v___y_2185_);
    leanh::lean_dec_ref(v___y_2184_);
    leanh::lean_dec(v___y_2183_);
    leanh::lean_dec_ref(v___y_2182_);
    return v_res_2191_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(
    mut v_00_u03b1_2192_: *mut leanh::LeanObject,
    mut v_mvarId_2193_: *mut leanh::LeanObject,
    mut v_x_2194_: *mut leanh::LeanObject,
    mut v___y_2195_: *mut leanh::LeanObject,
    mut v___y_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
    mut v___y_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
    mut v___y_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(
            v_mvarId_2193_,
            v_x_2194_,
            v___y_2195_,
            v___y_2196_,
            v___y_2197_,
            v___y_2198_,
            v___y_2199_,
            v___y_2200_,
            v___y_2201_,
            v___y_2202_,
        );
    return v___x_2204_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___boxed(
    mut v_00_u03b1_2205_: *mut leanh::LeanObject,
    mut v_mvarId_2206_: *mut leanh::LeanObject,
    mut v_x_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
    mut v___y_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
    mut v___y_2213_: *mut leanh::LeanObject,
    mut v___y_2214_: *mut leanh::LeanObject,
    mut v___y_2215_: *mut leanh::LeanObject,
    mut v___y_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(
            v_00_u03b1_2205_,
            v_mvarId_2206_,
            v_x_2207_,
            v___y_2208_,
            v___y_2209_,
            v___y_2210_,
            v___y_2211_,
            v___y_2212_,
            v___y_2213_,
            v___y_2214_,
            v___y_2215_,
        );
    leanh::lean_dec(v___y_2215_);
    leanh::lean_dec_ref(v___y_2214_);
    leanh::lean_dec(v___y_2213_);
    leanh::lean_dec_ref(v___y_2212_);
    leanh::lean_dec(v___y_2211_);
    leanh::lean_dec_ref(v___y_2210_);
    leanh::lean_dec(v___y_2209_);
    leanh::lean_dec_ref(v___y_2208_);
    return v_res_2217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(
    mut v_msg_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
    mut v___y_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2224_ = leanh::lean_ctor_get(v___y_2221_, 5);
                v___x_2225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
                v_a_2226_ = leanh::lean_ctor_get(v___x_2225_, 0);
                v_isSharedCheck_2234_ = (!leanh::lean_is_exclusive(v___x_2225_)) as u8;
                if v_isSharedCheck_2234_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    v_isShared_2229_ = v_isSharedCheck_2234_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2226_);
                    leanh::lean_dec(v___x_2225_);
                    v___x_2228_ = leanh::lean_box(0);
                    v_isShared_2229_ = v_isSharedCheck_2234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2224_);
                v___x_2230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2230_, 0, v_ref_2224_);
                leanh::lean_ctor_set(v___x_2230_, 1, v_a_2226_);
                if v_isShared_2229_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2228_, 1);
                    leanh::lean_ctor_set(v___x_2228_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
                    v___x_2232_ = v_reuseFailAlloc_2233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg___boxed(
    mut v_msg_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
    mut v___y_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2241_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(
            v_msg_2235_,
            v___y_2236_,
            v___y_2237_,
            v___y_2238_,
            v___y_2239_,
        );
    leanh::lean_dec(v___y_2239_);
    leanh::lean_dec_ref(v___y_2238_);
    leanh::lean_dec(v___y_2237_);
    leanh::lean_dec_ref(v___y_2236_);
    return v_res_2241_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0;
    v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
    return v___x_2244_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(
    mut v_a_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_2245_);
                v___x_2255_ = l_Lean_MVarId_getType(
                    v_a_2245_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                    v___y_2253_,
                );
                if leanh::lean_obj_tag(v___x_2255_) == 0 {
                    v_a_2256_ = leanh::lean_ctor_get(v___x_2255_, 0);
                    leanh::lean_inc(v_a_2256_);
                    leanh::lean_dec_ref_known(v___x_2255_, 1);
                    v___x_2257_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_a_2256_, v___y_2251_);
                    v_a_2258_ = leanh::lean_ctor_get(v___x_2257_, 0);
                    leanh::lean_inc(v_a_2258_);
                    leanh::lean_dec_ref(v___x_2257_);
                    v___x_2259_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2258_);
                    leanh::lean_dec(v_a_2258_);
                    if leanh::lean_obj_tag(v___x_2259_) == 1 {
                        v_val_2260_ = leanh::lean_ctor_get(v___x_2259_, 0);
                        leanh::lean_inc(v_val_2260_);
                        leanh::lean_dec_ref_known(v___x_2259_, 1);
                        v___x_2261_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(v_val_2260_);
                        v___x_2262_ =
                            l_Lean_MVarId_setType___redArg(v_a_2245_, v___x_2261_, v___y_2251_);
                        return v___x_2262_;
                    } else {
                        leanh::lean_dec(v___x_2259_);
                        leanh::lean_dec(v_a_2245_);
                        v___x_2263_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1);
                        v___x_2264_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v___x_2263_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
                        return v___x_2264_;
                    }
                } else {
                    leanh::lean_dec(v_a_2245_);
                    v_a_2265_ = leanh::lean_ctor_get(v___x_2255_, 0);
                    v_isSharedCheck_2272_ = (!leanh::lean_is_exclusive(v___x_2255_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2255_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2265_);
                        leanh::lean_dec(v___x_2255_);
                        v___x_2267_ = leanh::lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2268_ == 0 {
                    v___x_2270_ = v___x_2267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed(
    mut v_a_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(
        v_a_2273_,
        v___y_2274_,
        v___y_2275_,
        v___y_2276_,
        v___y_2277_,
        v___y_2278_,
        v___y_2279_,
        v___y_2280_,
        v___y_2281_,
    );
    leanh::lean_dec(v___y_2281_);
    leanh::lean_dec_ref(v___y_2280_);
    leanh::lean_dec(v___y_2279_);
    leanh::lean_dec_ref(v___y_2278_);
    leanh::lean_dec(v___y_2277_);
    leanh::lean_dec_ref(v___y_2276_);
    leanh::lean_dec(v___y_2275_);
    leanh::lean_dec_ref(v___y_2274_);
    return v_res_2283_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
    mut v_a_2288_: *mut leanh::LeanObject,
    mut v_a_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2293_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_2285_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_,
                );
                if leanh::lean_obj_tag(v___x_2293_) == 0 {
                    v_a_2294_ = leanh::lean_ctor_get(v___x_2293_, 0);
                    leanh::lean_inc_n(v_a_2294_, 2);
                    leanh::lean_dec_ref_known(v___x_2293_, 1);
                    v___f_2295_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2295_, 0, v_a_2294_);
                    v___x_2296_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_a_2294_, v___f_2295_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
                    return v___x_2296_;
                } else {
                    v_a_2297_ = leanh::lean_ctor_get(v___x_2293_, 0);
                    v_isSharedCheck_2304_ = (!leanh::lean_is_exclusive(v___x_2293_)) as u8;
                    if v_isSharedCheck_2304_ == 0 {
                        v___x_2299_ = v___x_2293_;
                        v_isShared_2300_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2297_);
                        leanh::lean_dec(v___x_2293_);
                        v___x_2299_ = leanh::lean_box(0);
                        v_isShared_2300_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2300_ == 0 {
                    v___x_2302_ = v___x_2299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2303_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
                    v___x_2302_ = v_reuseFailAlloc_2303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___boxed(
    mut v_a_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v_a_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
    mut v_a_2309_: *mut leanh::LeanObject,
    mut v_a_2310_: *mut leanh::LeanObject,
    mut v_a_2311_: *mut leanh::LeanObject,
    mut v_a_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
        v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_,
    );
    leanh::lean_dec(v_a_2312_);
    leanh::lean_dec_ref(v_a_2311_);
    leanh::lean_dec(v_a_2310_);
    leanh::lean_dec_ref(v_a_2309_);
    leanh::lean_dec(v_a_2308_);
    leanh::lean_dec_ref(v_a_2307_);
    leanh::lean_dec(v_a_2306_);
    leanh::lean_dec_ref(v_a_2305_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(
    mut v_x_2315_: *mut leanh::LeanObject,
    mut v_a_2316_: *mut leanh::LeanObject,
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_a_2318_: *mut leanh::LeanObject,
    mut v_a_2319_: *mut leanh::LeanObject,
    mut v_a_2320_: *mut leanh::LeanObject,
    mut v_a_2321_: *mut leanh::LeanObject,
    mut v_a_2322_: *mut leanh::LeanObject,
    mut v_a_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
        v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_,
    );
    return v___x_2325_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed(
    mut v_x_2326_: *mut leanh::LeanObject,
    mut v_a_2327_: *mut leanh::LeanObject,
    mut v_a_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v_a_2330_: *mut leanh::LeanObject,
    mut v_a_2331_: *mut leanh::LeanObject,
    mut v_a_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2336_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(
        v_x_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_,
        v_a_2334_,
    );
    leanh::lean_dec(v_a_2334_);
    leanh::lean_dec_ref(v_a_2333_);
    leanh::lean_dec(v_a_2332_);
    leanh::lean_dec_ref(v_a_2331_);
    leanh::lean_dec(v_a_2330_);
    leanh::lean_dec_ref(v_a_2329_);
    leanh::lean_dec(v_a_2328_);
    leanh::lean_dec_ref(v_a_2327_);
    leanh::lean_dec(v_x_2326_);
    return v_res_2336_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(
    mut v_00_u03b1_2337_: *mut leanh::LeanObject,
    mut v_msg_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(
            v_msg_2338_,
            v___y_2343_,
            v___y_2344_,
            v___y_2345_,
            v___y_2346_,
        );
    return v___x_2348_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___boxed(
    mut v_00_u03b1_2349_: *mut leanh::LeanObject,
    mut v_msg_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(
        v_00_u03b1_2349_,
        v_msg_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
        v___y_2354_,
        v___y_2355_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
    );
    leanh::lean_dec(v___y_2358_);
    leanh::lean_dec_ref(v___y_2357_);
    leanh::lean_dec(v___y_2356_);
    leanh::lean_dec_ref(v___y_2355_);
    leanh::lean_dec(v___y_2354_);
    leanh::lean_dec_ref(v___y_2353_);
    leanh::lean_dec(v___y_2352_);
    leanh::lean_dec_ref(v___y_2351_);
    return v_res_2360_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1()
-> *mut leanh::LeanObject {
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2377_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1;
    v___x_2378_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3;
    v___x_2379_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2380_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2376_,
        v___x_2377_,
        v___x_2378_,
        v___x_2379_,
    );
    return v___x_2380_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___boxed(
    mut v_a_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
    return v_res_2382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
}