// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Basic
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
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
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::MetavarContext::lean_instantiate_level_mvars;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value)
            as *mut crate::leanh::LeanObject,
        2932917581903347504 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value:
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
    m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value)
            as *mut crate::leanh::LeanObject,
        15990607923454282773 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value)
            as *mut crate::leanh::LeanObject,
        2578581590150657327 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value:
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
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 115, 116, 97, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value) as *mut crate::leanh::LeanObject,11928792895960270860 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 83, 116, 97, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value) as *mut crate::leanh::LeanObject,8722830812433448010 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 115, 116, 111, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value) as *mut crate::leanh::LeanObject,12268960959217848762 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 83, 116, 111, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value) as *mut crate::leanh::LeanObject,18431599668601016270 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
    mut v_l_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v_unused_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1195_ = lean_st_ref_get(v___y_1193_);
                v_mctx_1196_ = crate::leanh::lean_ctor_get(v___x_1195_, 0);
                crate::leanh::lean_inc_ref(v_mctx_1196_);
                crate::leanh::lean_dec(v___x_1195_);
                v___x_1197_ = lean_instantiate_level_mvars(v_mctx_1196_, v_l_1192_);
                v_fst_1198_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
                crate::leanh::lean_inc(v_fst_1198_);
                v_snd_1199_ = crate::leanh::lean_ctor_get(v___x_1197_, 1);
                crate::leanh::lean_inc(v_snd_1199_);
                crate::leanh::lean_dec_ref(v___x_1197_);
                v___x_1200_ = lean_st_ref_take(v___y_1193_);
                v_cache_1201_ = crate::leanh::lean_ctor_get(v___x_1200_, 1);
                v_zetaDeltaFVarIds_1202_ = crate::leanh::lean_ctor_get(v___x_1200_, 2);
                v_postponed_1203_ = crate::leanh::lean_ctor_get(v___x_1200_, 3);
                v_diag_1204_ = crate::leanh::lean_ctor_get(v___x_1200_, 4);
                v_isSharedCheck_1213_ = (!crate::leanh::lean_is_exclusive(v___x_1200_)) as u8;
                if v_isSharedCheck_1213_ == 0 {
                    v_unused_1214_ = crate::leanh::lean_ctor_get(v___x_1200_, 0);
                    crate::leanh::lean_dec(v_unused_1214_);
                    v___x_1206_ = v___x_1200_;
                    v_isShared_1207_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1204_);
                    crate::leanh::lean_inc(v_postponed_1203_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1202_);
                    crate::leanh::lean_inc(v_cache_1201_);
                    crate::leanh::lean_dec(v___x_1200_);
                    v___x_1206_ = crate::leanh::lean_box(0);
                    v_isShared_1207_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1206_, 0, v_fst_1198_);
                    v___x_1209_ = v___x_1206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_fst_1198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_cache_1201_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1212_,
                        2,
                        v_zetaDeltaFVarIds_1202_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_postponed_1203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_diag_1204_);
                    v___x_1209_ = v_reuseFailAlloc_1212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1210_ = lean_st_ref_set(v___y_1193_, v___x_1209_);
                v___x_1211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1211_, 0, v_snd_1199_);
                return v___x_1211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg___boxed(
    mut v_l_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1218_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
            v_l_1215_,
            v___y_1216_,
        );
    crate::leanh::lean_dec(v___y_1216_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(
    mut v_l_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(
            v_l_1219_,
            v___y_1221_,
        );
    return v___x_1225_;
}
pub unsafe fn l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___boxed(
    mut v_l_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ =
        l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(
            v_l_1226_,
            v___y_1227_,
            v___y_1228_,
            v___y_1229_,
            v___y_1230_,
        );
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec_ref(v___y_1229_);
    crate::leanh::lean_dec(v___y_1228_);
    crate::leanh::lean_dec_ref(v___y_1227_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
    mut v_e_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut v_unused_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1236_ = l_Lean_Expr_hasMVar(v_e_1233_);
                if v___x_1236_ == 0 {
                    v___x_1237_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1237_, 0, v_e_1233_);
                    return v___x_1237_;
                } else {
                    v___x_1238_ = lean_st_ref_get(v___y_1234_);
                    v_mctx_1239_ = crate::leanh::lean_ctor_get(v___x_1238_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1239_);
                    crate::leanh::lean_dec(v___x_1238_);
                    v___x_1240_ = l_Lean_instantiateMVarsCore(v_mctx_1239_, v_e_1233_);
                    v_fst_1241_ = crate::leanh::lean_ctor_get(v___x_1240_, 0);
                    crate::leanh::lean_inc(v_fst_1241_);
                    v_snd_1242_ = crate::leanh::lean_ctor_get(v___x_1240_, 1);
                    crate::leanh::lean_inc(v_snd_1242_);
                    crate::leanh::lean_dec_ref(v___x_1240_);
                    v___x_1243_ = lean_st_ref_take(v___y_1234_);
                    v_cache_1244_ = crate::leanh::lean_ctor_get(v___x_1243_, 1);
                    v_zetaDeltaFVarIds_1245_ = crate::leanh::lean_ctor_get(v___x_1243_, 2);
                    v_postponed_1246_ = crate::leanh::lean_ctor_get(v___x_1243_, 3);
                    v_diag_1247_ = crate::leanh::lean_ctor_get(v___x_1243_, 4);
                    v_isSharedCheck_1256_ = (!crate::leanh::lean_is_exclusive(v___x_1243_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v_unused_1257_ = crate::leanh::lean_ctor_get(v___x_1243_, 0);
                        crate::leanh::lean_dec(v_unused_1257_);
                        v___x_1249_ = v___x_1243_;
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1247_);
                        crate::leanh::lean_inc(v_postponed_1246_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1245_);
                        crate::leanh::lean_inc(v_cache_1244_);
                        crate::leanh::lean_dec(v___x_1243_);
                        v___x_1249_ = crate::leanh::lean_box(0);
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v_snd_1242_);
                    v___x_1252_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1255_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_snd_1242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_cache_1244_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1255_,
                        2,
                        v_zetaDeltaFVarIds_1245_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_postponed_1246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_diag_1247_);
                    v___x_1252_ = v_reuseFailAlloc_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1253_ = lean_st_ref_set(v___y_1234_, v___x_1252_);
                v___x_1254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1254_, 0, v_fst_1241_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg___boxed(
    mut v_e_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
            v_e_1258_,
            v___y_1259_,
        );
    crate::leanh::lean_dec(v___y_1259_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(
    mut v_e_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(
            v_e_1262_,
            v___y_1264_,
        );
    return v___x_1268_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___boxed(
    mut v_e_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(
        v_e_1269_,
        v___y_1270_,
        v___y_1271_,
        v___y_1272_,
        v___y_1273_,
    );
    crate::leanh::lean_dec(v___y_1273_);
    crate::leanh::lean_dec_ref(v___y_1272_);
    crate::leanh::lean_dec(v___y_1271_);
    crate::leanh::lean_dec_ref(v___y_1270_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStart(
    mut v_goal_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_a_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_a_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1306_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_goal_1300_);
                if crate::leanh::lean_obj_tag(v___x_1306_) == 1 {
                    crate::leanh::lean_dec_ref(v_goal_1300_);
                    v_val_1307_ = crate::leanh::lean_ctor_get(v___x_1306_, 0);
                    v_isSharedCheck_1316_ = (!crate::leanh::lean_is_exclusive(v___x_1306_)) as u8;
                    if v_isSharedCheck_1316_ == 0 {
                        v___x_1309_ = v___x_1306_;
                        v_isShared_1310_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1307_);
                        crate::leanh::lean_dec(v___x_1306_);
                        v___x_1309_ = crate::leanh::lean_box(0);
                        v_isShared_1310_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1306_);
                    v___x_1317_ =
                        l_Lean_Meta_mkFreshLevelMVar(v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
                    if crate::leanh::lean_obj_tag(v___x_1317_) == 0 {
                        v_a_1318_ = crate::leanh::lean_ctor_get(v___x_1317_, 0);
                        crate::leanh::lean_inc_n(v_a_1318_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1317_, 1);
                        v___x_1319_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(v_a_1318_);
                        v___x_1320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1319_);
                        v___x_1321_ = 0;
                        v___x_1322_ = crate::leanh::lean_box(0);
                        v___x_1323_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_1320_,
                            v___x_1321_,
                            v___x_1322_,
                            v_a_1301_,
                            v_a_1302_,
                            v_a_1303_,
                            v_a_1304_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1323_) == 0 {
                            v_a_1324_ = crate::leanh::lean_ctor_get(v___x_1323_, 0);
                            crate::leanh::lean_inc_n(v_a_1324_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1323_, 1);
                            v___x_1325_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3;
                            v___x_1326_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_a_1318_);
                            v___x_1327_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1327_, 0, v_a_1318_);
                            crate::leanh::lean_ctor_set(v___x_1327_, 1, v___x_1326_);
                            crate::leanh::lean_inc_ref(v___x_1327_);
                            v___x_1328_ = l_Lean_mkConst(v___x_1325_, v___x_1327_);
                            v___x_1329_ = l_Lean_Expr_app___override(v___x_1328_, v_a_1324_);
                            v___x_1330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1329_);
                            v___x_1331_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_1330_,
                                v___x_1321_,
                                v___x_1322_,
                                v_a_1301_,
                                v_a_1302_,
                                v_a_1303_,
                                v_a_1304_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1331_) == 0 {
                                v_a_1332_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                                crate::leanh::lean_inc_n(v_a_1332_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1331_, 1);
                                v___x_1333_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6;
                                v___x_1334_ = l_Lean_mkConst(v___x_1333_, v___x_1327_);
                                crate::leanh::lean_inc(v_a_1324_);
                                crate::leanh::lean_inc_ref(v_goal_1300_);
                                v___x_1335_ =
                                    l_Lean_mkApp3(v___x_1334_, v_goal_1300_, v_a_1324_, v_a_1332_);
                                v___x_1336_ = crate::leanh::lean_box(0);
                                v___x_1337_ = l_Lean_Meta_synthInstance(
                                    v___x_1335_,
                                    v___x_1336_,
                                    v_a_1301_,
                                    v_a_1302_,
                                    v_a_1303_,
                                    v_a_1304_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1337_) == 0 {
                                    v_a_1338_ = crate::leanh::lean_ctor_get(v___x_1337_, 0);
                                    crate::leanh::lean_inc(v_a_1338_);
                                    crate::leanh::lean_dec_ref_known(v___x_1337_, 1);
                                    v___x_1339_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(v_a_1318_, v_a_1302_);
                                    v_a_1340_ = crate::leanh::lean_ctor_get(v___x_1339_, 0);
                                    v_isSharedCheck_1363_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1339_)) as u8;
                                    if v_isSharedCheck_1363_ == 0 {
                                        v___x_1342_ = v___x_1339_;
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1340_);
                                        crate::leanh::lean_dec(v___x_1339_);
                                        v___x_1342_ = crate::leanh::lean_box(0);
                                        v_isShared_1343_ = v_isSharedCheck_1363_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1332_);
                                    crate::leanh::lean_dec(v_a_1324_);
                                    crate::leanh::lean_dec(v_a_1318_);
                                    crate::leanh::lean_dec_ref(v_goal_1300_);
                                    v_a_1364_ = crate::leanh::lean_ctor_get(v___x_1337_, 0);
                                    v_isSharedCheck_1371_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1337_)) as u8;
                                    if v_isSharedCheck_1371_ == 0 {
                                        v___x_1366_ = v___x_1337_;
                                        v_isShared_1367_ = v_isSharedCheck_1371_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1364_);
                                        crate::leanh::lean_dec(v___x_1337_);
                                        v___x_1366_ = crate::leanh::lean_box(0);
                                        v_isShared_1367_ = v_isSharedCheck_1371_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_1327_, 2);
                                crate::leanh::lean_dec(v_a_1324_);
                                crate::leanh::lean_dec(v_a_1318_);
                                crate::leanh::lean_dec_ref(v_goal_1300_);
                                v_a_1372_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                                v_isSharedCheck_1379_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                                if v_isSharedCheck_1379_ == 0 {
                                    v___x_1374_ = v___x_1331_;
                                    v_isShared_1375_ = v_isSharedCheck_1379_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1372_);
                                    crate::leanh::lean_dec(v___x_1331_);
                                    v___x_1374_ = crate::leanh::lean_box(0);
                                    v_isShared_1375_ = v_isSharedCheck_1379_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1318_);
                            crate::leanh::lean_dec_ref(v_goal_1300_);
                            v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1323_, 0);
                            v_isSharedCheck_1387_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1323_)) as u8;
                            if v_isSharedCheck_1387_ == 0 {
                                v___x_1382_ = v___x_1323_;
                                v_isShared_1383_ = v_isSharedCheck_1387_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1380_);
                                crate::leanh::lean_dec(v___x_1323_);
                                v___x_1382_ = crate::leanh::lean_box(0);
                                v_isShared_1383_ = v_isSharedCheck_1387_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_goal_1300_);
                        v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1317_, 0);
                        v_isSharedCheck_1395_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1317_)) as u8;
                        if v_isSharedCheck_1395_ == 0 {
                            v___x_1390_ = v___x_1317_;
                            v_isShared_1391_ = v_isSharedCheck_1395_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1388_);
                            crate::leanh::lean_dec(v___x_1317_);
                            v___x_1390_ = crate::leanh::lean_box(0);
                            v_isShared_1391_ = v_isSharedCheck_1395_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1311_ = crate::leanh::lean_box(0);
                v___x_1312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1312_, 0, v_val_1307_);
                crate::leanh::lean_ctor_set(v___x_1312_, 1, v___x_1311_);
                if v_isShared_1310_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1309_, 0);
                    crate::leanh::lean_ctor_set(v___x_1309_, 0, v___x_1312_);
                    v___x_1314_ = v___x_1309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
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
                crate::leanh::lean_inc(v_a_1340_);
                v___x_1345_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1345_, 0, v_a_1340_);
                crate::leanh::lean_ctor_set(v___x_1345_, 1, v___x_1326_);
                v___x_1346_ = l_Lean_mkConst(v___x_1344_, v___x_1345_);
                crate::leanh::lean_inc(v_a_1332_);
                crate::leanh::lean_inc(v_a_1324_);
                v___x_1347_ =
                    l_Lean_mkApp4(v___x_1346_, v_a_1324_, v_a_1332_, v_goal_1300_, v_a_1338_);
                v___x_1348_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_1332_, v_a_1302_);
                v_a_1349_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                v_isSharedCheck_1362_ = (!crate::leanh::lean_is_exclusive(v___x_1348_)) as u8;
                if v_isSharedCheck_1362_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    v_isShared_1352_ = v_isSharedCheck_1362_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1349_);
                    crate::leanh::lean_dec(v___x_1348_);
                    v___x_1351_ = crate::leanh::lean_box(0);
                    v_isShared_1352_ = v_isSharedCheck_1362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1324_);
                crate::leanh::lean_inc(v_a_1340_);
                v___x_1353_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_a_1340_, v_a_1324_);
                v___x_1354_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1354_, 0, v_a_1340_);
                crate::leanh::lean_ctor_set(v___x_1354_, 1, v_a_1324_);
                crate::leanh::lean_ctor_set(v___x_1354_, 2, v___x_1353_);
                crate::leanh::lean_ctor_set(v___x_1354_, 3, v_a_1349_);
                if v_isShared_1343_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1342_, 1);
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1347_);
                    v___x_1356_ = v___x_1342_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1347_);
                    v___x_1356_ = v_reuseFailAlloc_1361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1354_);
                crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                if v_isShared_1352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1357_);
                    v___x_1359_ = v___x_1351_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
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
                    v_reuseFailAlloc_1370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
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
                    v_reuseFailAlloc_1378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
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
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
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
                    v_reuseFailAlloc_1394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
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
    mut v_goal_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(
        v_goal_1396_,
        v_a_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
    );
    crate::leanh::lean_dec(v_a_1400_);
    crate::leanh::lean_dec_ref(v_a_1399_);
    crate::leanh::lean_dec(v_a_1398_);
    crate::leanh::lean_dec_ref(v_a_1397_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(
    mut v_mvarId_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_a_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1422_: u8 = 0;
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1403_,
                    v_x_1404_,
                    v___y_1405_,
                    v___y_1406_,
                    v___y_1407_,
                    v___y_1408_,
                );
                if crate::leanh::lean_obj_tag(v___x_1410_) == 0 {
                    v_a_1411_ = crate::leanh::lean_ctor_get(v___x_1410_, 0);
                    v_isSharedCheck_1418_ = (!crate::leanh::lean_is_exclusive(v___x_1410_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1410_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1411_);
                        crate::leanh::lean_dec(v___x_1410_);
                        v___x_1413_ = crate::leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1419_ = crate::leanh::lean_ctor_get(v___x_1410_, 0);
                    v_isSharedCheck_1426_ = (!crate::leanh::lean_is_exclusive(v___x_1410_)) as u8;
                    if v_isSharedCheck_1426_ == 0 {
                        v___x_1421_ = v___x_1410_;
                        v_isShared_1422_ = v_isSharedCheck_1426_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1419_);
                        crate::leanh::lean_dec(v___x_1410_);
                        v___x_1421_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
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
                    v_reuseFailAlloc_1425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
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
    mut v_mvarId_1427_: *mut crate::leanh::LeanObject,
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_1427_, v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
    crate::leanh::lean_dec(v___y_1432_);
    crate::leanh::lean_dec_ref(v___y_1431_);
    crate::leanh::lean_dec(v___y_1430_);
    crate::leanh::lean_dec_ref(v___y_1429_);
    return v_res_1434_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(
    mut v_00_u03b1_1435_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_1436_, v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
    return v___x_1443_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___boxed(
    mut v_00_u03b1_1444_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1445_: *mut crate::leanh::LeanObject,
    mut v_x_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_x_1453_: *mut crate::leanh::LeanObject,
    mut v_x_1454_: *mut crate::leanh::LeanObject,
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1457_ = crate::leanh::lean_ctor_get(v_x_1453_, 0);
                v_vs_1458_ = crate::leanh::lean_ctor_get(v_x_1453_, 1);
                v_isSharedCheck_1482_ = (!crate::leanh::lean_is_exclusive(v_x_1453_)) as u8;
                if v_isSharedCheck_1482_ == 0 {
                    v___x_1460_ = v_x_1453_;
                    v_isShared_1461_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1458_);
                    crate::leanh::lean_inc(v_ks_1457_);
                    crate::leanh::lean_dec(v_x_1453_);
                    v___x_1460_ = crate::leanh::lean_box(0);
                    v_isShared_1461_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1462_ = lean_array_get_size(v_ks_1457_);
                v___x_1463_ = lean_nat_dec_lt(v_x_1454_, v___x_1462_);
                if v___x_1463_ == 0 {
                    crate::leanh::lean_dec(v_x_1454_);
                    v___x_1464_ = lean_array_push(v_ks_1457_, v_x_1455_);
                    v___x_1465_ = lean_array_push(v_vs_1458_, v_x_1456_);
                    if v_isShared_1461_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1465_);
                        crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1464_);
                        v___x_1467_ = v___x_1460_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1468_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1464_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1465_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_ks_1457_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_vs_1458_);
                            v___x_1472_ = v_reuseFailAlloc_1476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1477_ = lean_array_fset(v_ks_1457_, v_x_1454_, v_x_1455_);
                        v___x_1478_ = lean_array_fset(v_vs_1458_, v_x_1454_, v_x_1456_);
                        crate::leanh::lean_dec(v_x_1454_);
                        if v_isShared_1461_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1478_);
                            crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1477_);
                            v___x_1480_ = v___x_1460_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1481_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
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
                v___x_1473_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1474_ = lean_nat_add(v_x_1454_, v___x_1473_);
                crate::leanh::lean_dec(v_x_1454_);
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
    mut v_n_1483_: *mut crate::leanh::LeanObject,
    mut v_k_1484_: *mut crate::leanh::LeanObject,
    mut v_v_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_1492_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1493_ = lean_usize_sub(v___x_1492_, v___x_1491_);
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(
    mut v_x_1495_: *mut crate::leanh::LeanObject,
    mut v_x_1496_: usize,
    mut v_x_1497_: usize,
    mut v_x_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: usize = 0;
    let mut v___x_1502_: usize = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: usize = 0;
    let mut v_j_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v_v_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_node_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_unused_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: u8 = 0;
    let mut v_ks_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v_reuseFailAlloc_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1495_) == 0 {
                    v_es_1500_ = crate::leanh::lean_ctor_get(v_x_1495_, 0);
                    v___x_1501_ = 5usize;
                    v___x_1502_ = 1usize;
                    v___x_1503_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_1504_ = lean_usize_land(v_x_1496_, v___x_1503_);
                    v_j_1505_ = lean_usize_to_nat(v___x_1504_);
                    v___x_1506_ = lean_array_get_size(v_es_1500_);
                    v___x_1507_ = lean_nat_dec_lt(v_j_1505_, v___x_1506_);
                    if v___x_1507_ == 0 {
                        crate::leanh::lean_dec(v_j_1505_);
                        crate::leanh::lean_dec(v_x_1499_);
                        crate::leanh::lean_dec(v_x_1498_);
                        return v_x_1495_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1500_);
                        v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v_x_1495_)) as u8;
                        if v_isSharedCheck_1544_ == 0 {
                            v_unused_1545_ = crate::leanh::lean_ctor_get(v_x_1495_, 0);
                            crate::leanh::lean_dec(v_unused_1545_);
                            v___x_1509_ = v_x_1495_;
                            v_isShared_1510_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1495_);
                            v___x_1509_ = crate::leanh::lean_box(0);
                            v_isShared_1510_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1546_ = crate::leanh::lean_ctor_get(v_x_1495_, 0);
                    v_vs_1547_ = crate::leanh::lean_ctor_get(v_x_1495_, 1);
                    v_isSharedCheck_1567_ = (!crate::leanh::lean_is_exclusive(v_x_1495_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1549_ = v_x_1495_;
                        v_isShared_1550_ = v_isSharedCheck_1567_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1547_);
                        crate::leanh::lean_inc(v_ks_1546_);
                        crate::leanh::lean_dec(v_x_1495_);
                        v___x_1549_ = crate::leanh::lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1567_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1511_ = lean_array_fget(v_es_1500_, v_j_1505_);
                v___x_1512_ = crate::leanh::lean_box(0);
                v_xs_x27_1513_ = lean_array_fset(v_es_1500_, v_j_1505_, v___x_1512_);
                match crate::leanh::lean_obj_tag(v_v_1511_) {
                    0 => {
                        v_key_1520_ = crate::leanh::lean_ctor_get(v_v_1511_, 0);
                        v_val_1521_ = crate::leanh::lean_ctor_get(v_v_1511_, 1);
                        v_isSharedCheck_1531_ = (!crate::leanh::lean_is_exclusive(v_v_1511_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1523_ = v_v_1511_;
                            v_isShared_1524_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1521_);
                            crate::leanh::lean_inc(v_key_1520_);
                            crate::leanh::lean_dec(v_v_1511_);
                            v___x_1523_ = crate::leanh::lean_box(0);
                            v_isShared_1524_ = v_isSharedCheck_1531_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1532_ = crate::leanh::lean_ctor_get(v_v_1511_, 0);
                        v_isSharedCheck_1542_ = (!crate::leanh::lean_is_exclusive(v_v_1511_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1534_ = v_v_1511_;
                            v_isShared_1535_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1532_);
                            crate::leanh::lean_dec(v_v_1511_);
                            v___x_1534_ = crate::leanh::lean_box(0);
                            v_isShared_1535_ = v_isSharedCheck_1542_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1543_, 0, v_x_1498_);
                        crate::leanh::lean_ctor_set(v___x_1543_, 1, v_x_1499_);
                        v___y_1515_ = v___x_1543_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1516_ = lean_array_fset(v_xs_x27_1513_, v_j_1505_, v___y_1515_);
                crate::leanh::lean_dec(v_j_1505_);
                if v_isShared_1510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1516_);
                    v___x_1518_ = v___x_1509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
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
                    crate::leanh::lean_del_object(v___x_1523_);
                    v___x_1526_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1520_,
                        v_val_1521_,
                        v_x_1498_,
                        v_x_1499_,
                    );
                    v___x_1527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                    v___y_1515_ = v___x_1527_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1521_);
                    crate::leanh::lean_dec(v_key_1520_);
                    if v_isShared_1524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1523_, 1, v_x_1499_);
                        crate::leanh::lean_ctor_set(v___x_1523_, 0, v_x_1498_);
                        v___x_1529_ = v___x_1523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_x_1498_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_x_1499_);
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
                    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1538_);
                    v___x_1540_ = v___x_1534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
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
                    v_reuseFailAlloc_1566_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_ks_1546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_vs_1547_);
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
                    v___x_1564_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
                    crate::leanh::lean_dec(v___x_1563_);
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
                    v_ks_1556_ = crate::leanh::lean_ctor_get(v_newNode_1553_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1556_);
                    v_vs_1557_ = crate::leanh::lean_ctor_get(v_newNode_1553_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1557_);
                    crate::leanh::lean_dec_ref(v_newNode_1553_);
                    v___x_1558_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1559_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_1560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1497_, v_ks_1556_, v_vs_1557_, v___x_1558_, v___x_1559_);
                    crate::leanh::lean_dec_ref(v_vs_1557_);
                    crate::leanh::lean_dec_ref(v_ks_1556_);
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
    mut v_keys_1569_: *mut crate::leanh::LeanObject,
    mut v_vals_1570_: *mut crate::leanh::LeanObject,
    mut v_i_1571_: *mut crate::leanh::LeanObject,
    mut v_entries_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v_k_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u64 = 0;
    let mut v_h_1578_: usize = 0;
    let mut v___x_1579_: usize = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: usize = 0;
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v_h_1584_: usize = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1573_ = lean_array_get_size(v_keys_1569_);
                v___x_1574_ = lean_nat_dec_lt(v_i_1571_, v___x_1573_);
                if v___x_1574_ == 0 {
                    crate::leanh::lean_dec(v_i_1571_);
                    return v_entries_1572_;
                } else {
                    v_k_1575_ = lean_array_fget_borrowed(v_keys_1569_, v_i_1571_);
                    v_v_1576_ = lean_array_fget_borrowed(v_vals_1570_, v_i_1571_);
                    v___x_1577_ = l_Lean_instHashableMVarId_hash(v_k_1575_);
                    v_h_1578_ = lean_uint64_to_usize(v___x_1577_);
                    v___x_1579_ = 5usize;
                    v___x_1580_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1581_ = 1usize;
                    v___x_1582_ = lean_usize_sub(v_depth_1568_, v___x_1581_);
                    v___x_1583_ = lean_usize_mul(v___x_1579_, v___x_1582_);
                    v_h_1584_ = lean_usize_shift_right(v_h_1578_, v___x_1583_);
                    v___x_1585_ = lean_nat_add(v_i_1571_, v___x_1580_);
                    crate::leanh::lean_dec(v_i_1571_);
                    crate::leanh::lean_inc(v_v_1576_);
                    crate::leanh::lean_inc(v_k_1575_);
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
    mut v_depth_1588_: *mut crate::leanh::LeanObject,
    mut v_keys_1589_: *mut crate::leanh::LeanObject,
    mut v_vals_1590_: *mut crate::leanh::LeanObject,
    mut v_i_1591_: *mut crate::leanh::LeanObject,
    mut v_entries_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1593_: usize = 0;
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1593_ = crate::leanh::lean_unbox_usize(v_depth_1588_);
    crate::leanh::lean_dec(v_depth_1588_);
    v_res_1594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_1593_, v_keys_1589_, v_vals_1590_, v_i_1591_, v_entries_1592_);
    crate::leanh::lean_dec_ref(v_vals_1590_);
    crate::leanh::lean_dec_ref(v_keys_1589_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_1595_: *mut crate::leanh::LeanObject,
    mut v_x_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3527__boxed_1600_: usize = 0;
    let mut v_x_3528__boxed_1601_: usize = 0;
    let mut v_res_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3527__boxed_1600_ = crate::leanh::lean_unbox_usize(v_x_1596_);
    crate::leanh::lean_dec(v_x_1596_);
    v_x_3528__boxed_1601_ = crate::leanh::lean_unbox_usize(v_x_1597_);
    crate::leanh::lean_dec(v_x_1597_);
    v_res_1602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1595_, v_x_3527__boxed_1600_, v_x_3528__boxed_1601_, v_x_1598_, v_x_1599_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(
    mut v_x_1603_: *mut crate::leanh::LeanObject,
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_x_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: u64 = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_instHashableMVarId_hash(v_x_1604_);
    v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
    v___x_1608_ = 1usize;
    v___x_1609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1603_, v___x_1607_, v___x_1608_, v_x_1604_, v_x_1605_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
    mut v_mvarId_1610_: *mut crate::leanh::LeanObject,
    mut v_val_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v_depth_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1614_ = lean_st_ref_take(v___y_1612_);
                v_mctx_1615_ = crate::leanh::lean_ctor_get(v___x_1614_, 0);
                v_cache_1616_ = crate::leanh::lean_ctor_get(v___x_1614_, 1);
                v_zetaDeltaFVarIds_1617_ = crate::leanh::lean_ctor_get(v___x_1614_, 2);
                v_postponed_1618_ = crate::leanh::lean_ctor_get(v___x_1614_, 3);
                v_diag_1619_ = crate::leanh::lean_ctor_get(v___x_1614_, 4);
                v_isSharedCheck_1647_ = (!crate::leanh::lean_is_exclusive(v___x_1614_)) as u8;
                if v_isSharedCheck_1647_ == 0 {
                    v___x_1621_ = v___x_1614_;
                    v_isShared_1622_ = v_isSharedCheck_1647_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1619_);
                    crate::leanh::lean_inc(v_postponed_1618_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1617_);
                    crate::leanh::lean_inc(v_cache_1616_);
                    crate::leanh::lean_inc(v_mctx_1615_);
                    crate::leanh::lean_dec(v___x_1614_);
                    v___x_1621_ = crate::leanh::lean_box(0);
                    v_isShared_1622_ = v_isSharedCheck_1647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1623_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 0);
                v_levelAssignDepth_1624_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 1);
                v_lmvarCounter_1625_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 2);
                v_mvarCounter_1626_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 3);
                v_lDecls_1627_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 4);
                v_decls_1628_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 5);
                v_userNames_1629_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 6);
                v_lAssignment_1630_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 7);
                v_eAssignment_1631_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 8);
                v_dAssignment_1632_ = crate::leanh::lean_ctor_get(v_mctx_1615_, 9);
                v_isSharedCheck_1646_ = (!crate::leanh::lean_is_exclusive(v_mctx_1615_)) as u8;
                if v_isSharedCheck_1646_ == 0 {
                    v___x_1634_ = v_mctx_1615_;
                    v_isShared_1635_ = v_isSharedCheck_1646_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1632_);
                    crate::leanh::lean_inc(v_eAssignment_1631_);
                    crate::leanh::lean_inc(v_lAssignment_1630_);
                    crate::leanh::lean_inc(v_userNames_1629_);
                    crate::leanh::lean_inc(v_decls_1628_);
                    crate::leanh::lean_inc(v_lDecls_1627_);
                    crate::leanh::lean_inc(v_mvarCounter_1626_);
                    crate::leanh::lean_inc(v_lmvarCounter_1625_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1624_);
                    crate::leanh::lean_inc(v_depth_1623_);
                    crate::leanh::lean_dec(v_mctx_1615_);
                    v___x_1634_ = crate::leanh::lean_box(0);
                    v_isShared_1635_ = v_isSharedCheck_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_eAssignment_1631_, v_mvarId_1610_, v_val_1611_);
                if v_isShared_1635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1634_, 8, v___x_1636_);
                    v___x_1638_ = v___x_1634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_depth_1623_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1645_,
                        1,
                        v_levelAssignDepth_1624_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_lmvarCounter_1625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_mvarCounter_1626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_lDecls_1627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_decls_1628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_userNames_1629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_lAssignment_1630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 8, v___x_1636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 9, v_dAssignment_1632_);
                    v___x_1638_ = v_reuseFailAlloc_1645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1621_, 0, v___x_1638_);
                    v___x_1640_ = v___x_1621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_cache_1616_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1644_,
                        2,
                        v_zetaDeltaFVarIds_1617_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_postponed_1618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_diag_1619_);
                    v___x_1640_ = v_reuseFailAlloc_1644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1641_ = lean_st_ref_set(v___y_1612_, v___x_1640_);
                v___x_1642_ = crate::leanh::lean_box(0);
                v___x_1643_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1642_);
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg___boxed(
    mut v_mvarId_1648_: *mut crate::leanh::LeanObject,
    mut v_val_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
            v_mvarId_1648_,
            v_val_1649_,
            v___y_1650_,
        );
    crate::leanh::lean_dec(v___y_1650_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(
    mut v_msgData_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_st_ref_get(v___y_1657_);
    v_env_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
    crate::leanh::lean_inc_ref(v_env_1660_);
    crate::leanh::lean_dec(v___x_1659_);
    v___x_1661_ = lean_st_ref_get(v___y_1655_);
    v_mctx_1662_ = crate::leanh::lean_ctor_get(v___x_1661_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1662_);
    crate::leanh::lean_dec(v___x_1661_);
    v_lctx_1663_ = crate::leanh::lean_ctor_get(v___y_1654_, 2);
    v_options_1664_ = crate::leanh::lean_ctor_get(v___y_1656_, 2);
    crate::leanh::lean_inc_ref(v_options_1664_);
    crate::leanh::lean_inc_ref(v_lctx_1663_);
    v___x_1665_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1665_, 0, v_env_1660_);
    crate::leanh::lean_ctor_set(v___x_1665_, 1, v_mctx_1662_);
    crate::leanh::lean_ctor_set(v___x_1665_, 2, v_lctx_1663_);
    crate::leanh::lean_ctor_set(v___x_1665_, 3, v_options_1664_);
    v___x_1666_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
    crate::leanh::lean_ctor_set(v___x_1666_, 1, v_msgData_1653_);
    v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2___boxed(
    mut v_msgData_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msgData_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    crate::leanh::lean_dec(v___y_1672_);
    crate::leanh::lean_dec_ref(v___y_1671_);
    crate::leanh::lean_dec(v___y_1670_);
    crate::leanh::lean_dec_ref(v___y_1669_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(
    mut v_msg_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1681_ = crate::leanh::lean_ctor_get(v___y_1678_, 5);
                v___x_1682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
                v_a_1683_ = crate::leanh::lean_ctor_get(v___x_1682_, 0);
                v_isSharedCheck_1691_ = (!crate::leanh::lean_is_exclusive(v___x_1682_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1685_ = v___x_1682_;
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1683_);
                    crate::leanh::lean_dec(v___x_1682_);
                    v___x_1685_ = crate::leanh::lean_box(0);
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1681_);
                v___x_1687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1687_, 0, v_ref_1681_);
                crate::leanh::lean_ctor_set(v___x_1687_, 1, v_a_1683_);
                if v_isShared_1686_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1685_, 1);
                    crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1689_ = v___x_1685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
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
    mut v_msg_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(
            v_msg_1692_,
            v___y_1693_,
            v___y_1694_,
            v___y_1695_,
            v___y_1696_,
        );
    crate::leanh::lean_dec(v___y_1696_);
    crate::leanh::lean_dec_ref(v___y_1695_);
    crate::leanh::lean_dec(v___y_1694_);
    crate::leanh::lean_dec_ref(v___y_1693_);
    return v_res_1698_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0;
    v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2;
    v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4;
    v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(
    mut v_mvar_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v_proof_x3f_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v_val_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_unused_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_unused_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut v_unused_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut v_a_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_a_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_a_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v_a_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvar_1708_);
                v___x_1714_ = l_Lean_MVarId_getType(
                    v_mvar_1708_,
                    v___y_1709_,
                    v___y_1710_,
                    v___y_1711_,
                    v___y_1712_,
                );
                if crate::leanh::lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                    crate::leanh::lean_inc(v_a_1715_);
                    crate::leanh::lean_dec_ref_known(v___x_1714_, 1);
                    v___x_1716_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_1715_, v___y_1710_);
                    v_a_1717_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                    crate::leanh::lean_inc_n(v_a_1717_, 2);
                    crate::leanh::lean_dec_ref(v___x_1716_);
                    v___x_1792_ = l_Lean_Meta_isProp(
                        v_a_1717_,
                        v___y_1709_,
                        v___y_1710_,
                        v___y_1711_,
                        v___y_1712_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1792_) == 0 {
                        v_a_1793_ = crate::leanh::lean_ctor_get(v___x_1792_, 0);
                        crate::leanh::lean_inc(v_a_1793_);
                        crate::leanh::lean_dec_ref_known(v___x_1792_, 1);
                        v___x_1794_ = (crate::leanh::lean_unbox(v_a_1793_) as u8);
                        crate::leanh::lean_dec(v_a_1793_);
                        if v___x_1794_ == 0 {
                            crate::leanh::lean_inc(v___y_1712_);
                            crate::leanh::lean_inc_ref(v___y_1711_);
                            crate::leanh::lean_inc(v___y_1710_);
                            crate::leanh::lean_inc_ref(v___y_1709_);
                            v___x_1795_ = lean_infer_type(
                                v_a_1717_,
                                v___y_1709_,
                                v___y_1710_,
                                v___y_1711_,
                                v___y_1712_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1795_) == 0 {
                                v_a_1796_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
                                crate::leanh::lean_inc(v_a_1796_);
                                crate::leanh::lean_dec_ref_known(v___x_1795_, 1);
                                v___x_1797_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1);
                                v___x_1798_ = l_Lean_mkMVar(v_mvar_1708_);
                                v___x_1799_ = l_Lean_MessageData_ofExpr(v___x_1798_);
                                v___x_1800_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1800_, 0, v___x_1797_);
                                crate::leanh::lean_ctor_set(v___x_1800_, 1, v___x_1799_);
                                v___x_1801_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3);
                                v___x_1802_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                                crate::leanh::lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                                v___x_1803_ = l_Lean_MessageData_ofExpr(v_a_1796_);
                                v___x_1804_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1802_);
                                crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
                                v___x_1805_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5);
                                v___x_1806_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1804_);
                                crate::leanh::lean_ctor_set(v___x_1806_, 1, v___x_1805_);
                                v___x_1807_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v___x_1806_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
                                crate::leanh::lean_dec(v___y_1712_);
                                crate::leanh::lean_dec_ref(v___y_1711_);
                                crate::leanh::lean_dec(v___y_1710_);
                                crate::leanh::lean_dec_ref(v___y_1709_);
                                v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                                v_isSharedCheck_1815_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                                if v_isSharedCheck_1815_ == 0 {
                                    v___x_1810_ = v___x_1807_;
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1808_);
                                    crate::leanh::lean_dec(v___x_1807_);
                                    v___x_1810_ = crate::leanh::lean_box(0);
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___y_1712_);
                                crate::leanh::lean_dec_ref(v___y_1711_);
                                crate::leanh::lean_dec(v___y_1710_);
                                crate::leanh::lean_dec_ref(v___y_1709_);
                                crate::leanh::lean_dec(v_mvar_1708_);
                                v_a_1816_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
                                v_isSharedCheck_1823_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1795_)) as u8;
                                if v_isSharedCheck_1823_ == 0 {
                                    v___x_1818_ = v___x_1795_;
                                    v_isShared_1819_ = v_isSharedCheck_1823_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1816_);
                                    crate::leanh::lean_dec(v___x_1795_);
                                    v___x_1818_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v_a_1717_);
                        crate::leanh::lean_dec(v___y_1712_);
                        crate::leanh::lean_dec_ref(v___y_1711_);
                        crate::leanh::lean_dec(v___y_1710_);
                        crate::leanh::lean_dec_ref(v___y_1709_);
                        crate::leanh::lean_dec(v_mvar_1708_);
                        v_a_1824_ = crate::leanh::lean_ctor_get(v___x_1792_, 0);
                        v_isSharedCheck_1831_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1792_)) as u8;
                        if v_isSharedCheck_1831_ == 0 {
                            v___x_1826_ = v___x_1792_;
                            v_isShared_1827_ = v_isSharedCheck_1831_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1824_);
                            crate::leanh::lean_dec(v___x_1792_);
                            v___x_1826_ = crate::leanh::lean_box(0);
                            v_isShared_1827_ = v_isSharedCheck_1831_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1712_);
                    crate::leanh::lean_dec_ref(v___y_1711_);
                    crate::leanh::lean_dec(v___y_1710_);
                    crate::leanh::lean_dec_ref(v___y_1709_);
                    crate::leanh::lean_dec(v_mvar_1708_);
                    v_a_1832_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1839_ = (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1834_ = v___x_1714_;
                        v_isShared_1835_ = v_isSharedCheck_1839_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1832_);
                        crate::leanh::lean_dec(v___x_1714_);
                        v___x_1834_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_1723_) == 0 {
                    v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1723_, 0);
                    v_isSharedCheck_1783_ = (!crate::leanh::lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1726_ = v___x_1723_;
                        v_isShared_1727_ = v_isSharedCheck_1783_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1724_);
                        crate::leanh::lean_dec(v___x_1723_);
                        v___x_1726_ = crate::leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1783_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1722_);
                    crate::leanh::lean_dec_ref(v___y_1721_);
                    crate::leanh::lean_dec(v___y_1720_);
                    crate::leanh::lean_dec_ref(v___y_1719_);
                    crate::leanh::lean_dec(v_mvar_1708_);
                    v_a_1784_ = crate::leanh::lean_ctor_get(v___x_1723_, 0);
                    v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1786_ = v___x_1723_;
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1784_);
                        crate::leanh::lean_dec(v___x_1723_);
                        v___x_1786_ = crate::leanh::lean_box(0);
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_proof_x3f_1728_ = crate::leanh::lean_ctor_get(v_a_1724_, 1);
                if crate::leanh::lean_obj_tag(v_proof_x3f_1728_) == 1 {
                    crate::leanh::lean_inc_ref(v_proof_x3f_1728_);
                    crate::leanh::lean_del_object(v___x_1726_);
                    v_goal_1729_ = crate::leanh::lean_ctor_get(v_a_1724_, 0);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v_a_1724_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v_unused_1770_ = crate::leanh::lean_ctor_get(v_a_1724_, 1);
                        crate::leanh::lean_dec(v_unused_1770_);
                        v___x_1731_ = v_a_1724_;
                        v_isShared_1732_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_goal_1729_);
                        crate::leanh::lean_dec(v_a_1724_);
                        v___x_1731_ = crate::leanh::lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1722_);
                    crate::leanh::lean_dec_ref(v___y_1721_);
                    crate::leanh::lean_dec(v___y_1720_);
                    crate::leanh::lean_dec_ref(v___y_1719_);
                    v_goal_1771_ = crate::leanh::lean_ctor_get(v_a_1724_, 0);
                    v_isSharedCheck_1781_ = (!crate::leanh::lean_is_exclusive(v_a_1724_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v_unused_1782_ = crate::leanh::lean_ctor_get(v_a_1724_, 1);
                        crate::leanh::lean_dec(v_unused_1782_);
                        v___x_1773_ = v_a_1724_;
                        v_isShared_1774_ = v_isSharedCheck_1781_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_goal_1771_);
                        crate::leanh::lean_dec(v_a_1724_);
                        v___x_1773_ = crate::leanh::lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1781_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_val_1733_ = crate::leanh::lean_ctor_get(v_proof_x3f_1728_, 0);
                crate::leanh::lean_inc(v_val_1733_);
                crate::leanh::lean_dec_ref_known(v_proof_x3f_1728_, 1);
                crate::leanh::lean_inc(v_mvar_1708_);
                v___x_1734_ = l_Lean_MVarId_getTag(
                    v_mvar_1708_,
                    v___y_1719_,
                    v___y_1720_,
                    v___y_1721_,
                    v___y_1722_,
                );
                if crate::leanh::lean_obj_tag(v___x_1734_) == 0 {
                    v_a_1735_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                    crate::leanh::lean_inc(v_a_1735_);
                    crate::leanh::lean_dec_ref_known(v___x_1734_, 1);
                    crate::leanh::lean_inc_ref(v_goal_1729_);
                    v___x_1736_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1729_);
                    v___x_1737_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1736_,
                        v_a_1735_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                    );
                    crate::leanh::lean_dec(v___y_1722_);
                    crate::leanh::lean_dec_ref(v___y_1721_);
                    crate::leanh::lean_dec_ref(v___y_1719_);
                    if crate::leanh::lean_obj_tag(v___x_1737_) == 0 {
                        v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                        crate::leanh::lean_inc_n(v_a_1738_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1737_, 1);
                        v___x_1739_ = l_Lean_Expr_app___override(v_val_1733_, v_a_1738_);
                        v___x_1740_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvar_1708_, v___x_1739_, v___y_1720_);
                        crate::leanh::lean_dec(v___y_1720_);
                        v_isSharedCheck_1751_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1751_ == 0 {
                            v_unused_1752_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                            crate::leanh::lean_dec(v_unused_1752_);
                            v___x_1742_ = v___x_1740_;
                            v_isShared_1743_ = v_isSharedCheck_1751_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1740_);
                            v___x_1742_ = crate::leanh::lean_box(0);
                            v_isShared_1743_ = v_isSharedCheck_1751_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1733_);
                        crate::leanh::lean_del_object(v___x_1731_);
                        crate::leanh::lean_dec_ref(v_goal_1729_);
                        crate::leanh::lean_dec(v___y_1720_);
                        crate::leanh::lean_dec(v_mvar_1708_);
                        v_a_1753_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                        v_isSharedCheck_1760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                        if v_isSharedCheck_1760_ == 0 {
                            v___x_1755_ = v___x_1737_;
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1753_);
                            crate::leanh::lean_dec(v___x_1737_);
                            v___x_1755_ = crate::leanh::lean_box(0);
                            v_isShared_1756_ = v_isSharedCheck_1760_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_1733_);
                    crate::leanh::lean_del_object(v___x_1731_);
                    crate::leanh::lean_dec_ref(v_goal_1729_);
                    crate::leanh::lean_dec(v___y_1722_);
                    crate::leanh::lean_dec_ref(v___y_1721_);
                    crate::leanh::lean_dec(v___y_1720_);
                    crate::leanh::lean_dec_ref(v___y_1719_);
                    crate::leanh::lean_dec(v_mvar_1708_);
                    v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                    v_isSharedCheck_1768_ = (!crate::leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1768_ == 0 {
                        v___x_1763_ = v___x_1734_;
                        v_isShared_1764_ = v_isSharedCheck_1768_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1761_);
                        crate::leanh::lean_dec(v___x_1734_);
                        v___x_1763_ = crate::leanh::lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1768_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1744_ = l_Lean_Expr_mvarId_x21(v_a_1738_);
                crate::leanh::lean_dec(v_a_1738_);
                if v_isShared_1732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1731_, 1, v_goal_1729_);
                    crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1731_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_goal_1729_);
                    v___x_1746_ = v_reuseFailAlloc_1750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1746_);
                    v___x_1748_ = v___x_1742_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
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
                    v_reuseFailAlloc_1759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
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
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
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
                    crate::leanh::lean_ctor_set(v___x_1773_, 1, v_goal_1771_);
                    crate::leanh::lean_ctor_set(v___x_1773_, 0, v_mvar_1708_);
                    v___x_1776_ = v___x_1773_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1780_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_mvar_1708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_goal_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1780_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1726_, 0, v___x_1776_);
                    v___x_1778_ = v___x_1726_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
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
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
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
                    v_reuseFailAlloc_1814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
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
                    v_reuseFailAlloc_1822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
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
                    v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
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
                    v_reuseFailAlloc_1838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
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
    mut v_mvar_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvar_1847_: *mut crate::leanh::LeanObject,
    mut v_a_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvar_1847_);
    v___f_1853_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1853_, 0, v_mvar_1847_);
    v___x_1854_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvar_1847_, v___f_1853_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
    return v___x_1854_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___boxed(
    mut v_mvar_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
    mut v_a_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(
        v_mvar_1855_,
        v_a_1856_,
        v_a_1857_,
        v_a_1858_,
        v_a_1859_,
    );
    crate::leanh::lean_dec(v_a_1859_);
    crate::leanh::lean_dec_ref(v_a_1858_);
    crate::leanh::lean_dec(v_a_1857_);
    crate::leanh::lean_dec_ref(v_a_1856_);
    return v_res_1861_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(
    mut v_mvarId_1862_: *mut crate::leanh::LeanObject,
    mut v_val_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(
            v_mvarId_1862_,
            v_val_1863_,
            v___y_1865_,
        );
    return v___x_1869_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___boxed(
    mut v_mvarId_1870_: *mut crate::leanh::LeanObject,
    mut v_val_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(
        v_mvarId_1870_,
        v_val_1871_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
    );
    crate::leanh::lean_dec(v___y_1875_);
    crate::leanh::lean_dec_ref(v___y_1874_);
    crate::leanh::lean_dec(v___y_1873_);
    crate::leanh::lean_dec_ref(v___y_1872_);
    return v_res_1877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(
    mut v_00_u03b1_1878_: *mut crate::leanh::LeanObject,
    mut v_msg_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1886_: *mut crate::leanh::LeanObject,
    mut v_msg_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(
        v_00_u03b1_1886_,
        v_msg_1887_,
        v___y_1888_,
        v___y_1889_,
        v___y_1890_,
        v___y_1891_,
    );
    crate::leanh::lean_dec(v___y_1891_);
    crate::leanh::lean_dec_ref(v___y_1890_);
    crate::leanh::lean_dec(v___y_1889_);
    crate::leanh::lean_dec_ref(v___y_1888_);
    return v_res_1893_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0(
    mut v_00_u03b2_1894_: *mut crate::leanh::LeanObject,
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_x_1895_, v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
    mut v_x_1901_: usize,
    mut v_x_1902_: usize,
    mut v_x_1903_: *mut crate::leanh::LeanObject,
    mut v_x_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_1900_, v_x_1901_, v_x_1902_, v_x_1903_, v_x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1906_: *mut crate::leanh::LeanObject,
    mut v_x_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
    mut v_x_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4149__boxed_1912_: usize = 0;
    let mut v_x_4150__boxed_1913_: usize = 0;
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4149__boxed_1912_ = crate::leanh::lean_unbox_usize(v_x_1908_);
    crate::leanh::lean_dec(v_x_1908_);
    v_x_4150__boxed_1913_ = crate::leanh::lean_unbox_usize(v_x_1909_);
    crate::leanh::lean_dec(v_x_1909_);
    v_res_1914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(v_00_u03b2_1906_, v_x_1907_, v_x_4149__boxed_1912_, v_x_4150__boxed_1913_, v_x_1910_, v_x_1911_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_1915_: *mut crate::leanh::LeanObject,
    mut v_n_1916_: *mut crate::leanh::LeanObject,
    mut v_k_1917_: *mut crate::leanh::LeanObject,
    mut v_v_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v_n_1916_, v_k_1917_, v_v_1918_);
    return v___x_1919_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1920_: *mut crate::leanh::LeanObject,
    mut v_depth_1921_: usize,
    mut v_keys_1922_: *mut crate::leanh::LeanObject,
    mut v_vals_1923_: *mut crate::leanh::LeanObject,
    mut v_heq_1924_: *mut crate::leanh::LeanObject,
    mut v_i_1925_: *mut crate::leanh::LeanObject,
    mut v_entries_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_1921_, v_keys_1922_, v_vals_1923_, v_i_1925_, v_entries_1926_);
    return v___x_1927_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1928_: *mut crate::leanh::LeanObject,
    mut v_depth_1929_: *mut crate::leanh::LeanObject,
    mut v_keys_1930_: *mut crate::leanh::LeanObject,
    mut v_vals_1931_: *mut crate::leanh::LeanObject,
    mut v_heq_1932_: *mut crate::leanh::LeanObject,
    mut v_i_1933_: *mut crate::leanh::LeanObject,
    mut v_entries_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1935_: usize = 0;
    let mut v_res_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1935_ = crate::leanh::lean_unbox_usize(v_depth_1929_);
    crate::leanh::lean_dec(v_depth_1929_);
    v_res_1936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1928_, v_depth_boxed_1935_, v_keys_1930_, v_vals_1931_, v_heq_1932_, v_i_1933_, v_entries_1934_);
    crate::leanh::lean_dec_ref(v_vals_1931_);
    crate::leanh::lean_dec_ref(v_keys_1930_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_1938_, v_x_1939_, v_x_1940_, v_x_1941_);
    return v___x_1942_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
    mut v_a_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut v_unused_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut v_a_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1949_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_,
                );
                if crate::leanh::lean_obj_tag(v___x_1949_) == 0 {
                    v_a_1950_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                    crate::leanh::lean_inc(v_a_1950_);
                    crate::leanh::lean_dec_ref_known(v___x_1949_, 1);
                    v___x_1951_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(
                        v_a_1950_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1951_) == 0 {
                        v_a_1952_ = crate::leanh::lean_ctor_get(v___x_1951_, 0);
                        crate::leanh::lean_inc(v_a_1952_);
                        crate::leanh::lean_dec_ref_known(v___x_1951_, 1);
                        v_fst_1953_ = crate::leanh::lean_ctor_get(v_a_1952_, 0);
                        v___x_1954_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_fst_1953_);
                        v___x_1955_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1955_, 0, v_fst_1953_);
                        crate::leanh::lean_ctor_set(v___x_1955_, 1, v___x_1954_);
                        v___x_1956_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1955_,
                            v_a_1943_,
                            v_a_1944_,
                            v_a_1945_,
                            v_a_1946_,
                            v_a_1947_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1956_) == 0 {
                            v_isSharedCheck_1963_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1956_)) as u8;
                            if v_isSharedCheck_1963_ == 0 {
                                v_unused_1964_ = crate::leanh::lean_ctor_get(v___x_1956_, 0);
                                crate::leanh::lean_dec(v_unused_1964_);
                                v___x_1958_ = v___x_1956_;
                                v_isShared_1959_ = v_isSharedCheck_1963_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1956_);
                                v___x_1958_ = crate::leanh::lean_box(0);
                                v_isShared_1959_ = v_isSharedCheck_1963_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1952_);
                            v_a_1965_ = crate::leanh::lean_ctor_get(v___x_1956_, 0);
                            v_isSharedCheck_1972_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1956_)) as u8;
                            if v_isSharedCheck_1972_ == 0 {
                                v___x_1967_ = v___x_1956_;
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1965_);
                                crate::leanh::lean_dec(v___x_1956_);
                                v___x_1967_ = crate::leanh::lean_box(0);
                                v_isShared_1968_ = v_isSharedCheck_1972_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1951_;
                    }
                } else {
                    v_a_1973_ = crate::leanh::lean_ctor_get(v___x_1949_, 0);
                    v_isSharedCheck_1980_ = (!crate::leanh::lean_is_exclusive(v___x_1949_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1975_ = v___x_1949_;
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1973_);
                        crate::leanh::lean_dec(v___x_1949_);
                        v___x_1975_ = crate::leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1958_, 0, v_a_1952_);
                    v___x_1961_ = v___x_1958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1952_);
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
                    v_reuseFailAlloc_1971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
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
                    v_reuseFailAlloc_1979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
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
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
        v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_,
    );
    crate::leanh::lean_dec(v_a_1985_);
    crate::leanh::lean_dec_ref(v_a_1984_);
    crate::leanh::lean_dec(v_a_1983_);
    crate::leanh::lean_dec_ref(v_a_1982_);
    crate::leanh::lean_dec(v_a_1981_);
    return v_res_1987_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(
    mut v_a_1988_: *mut crate::leanh::LeanObject,
    mut v_a_1989_: *mut crate::leanh::LeanObject,
    mut v_a_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
    mut v_a_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
        v_a_1989_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_,
    );
    return v___x_1997_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___boxed(
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(
        v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_,
    );
    crate::leanh::lean_dec(v_a_2005_);
    crate::leanh::lean_dec_ref(v_a_2004_);
    crate::leanh::lean_dec(v_a_2003_);
    crate::leanh::lean_dec_ref(v_a_2002_);
    crate::leanh::lean_dec(v_a_2001_);
    crate::leanh::lean_dec_ref(v_a_2000_);
    crate::leanh::lean_dec(v_a_1999_);
    crate::leanh::lean_dec_ref(v_a_1998_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
    mut v_a_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut v_unused_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2014_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                    v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_,
                );
                if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
                    v_isSharedCheck_2022_ = (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2022_ == 0 {
                        v_unused_2023_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                        crate::leanh::lean_dec(v_unused_2023_);
                        v___x_2016_ = v___x_2014_;
                        v_isShared_2017_ = v_isSharedCheck_2022_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2014_);
                        v___x_2016_ = crate::leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2022_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2024_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                    v_isSharedCheck_2031_ = (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v___x_2026_ = v___x_2014_;
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2024_);
                        crate::leanh::lean_dec(v___x_2014_);
                        v___x_2026_ = crate::leanh::lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2018_ = crate::leanh::lean_box(0);
                if v_isShared_2017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2016_, 0, v___x_2018_);
                    v___x_2020_ = v___x_2016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
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
                    v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
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
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
        v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_,
    );
    crate::leanh::lean_dec(v_a_2036_);
    crate::leanh::lean_dec_ref(v_a_2035_);
    crate::leanh::lean_dec(v_a_2034_);
    crate::leanh::lean_dec_ref(v_a_2033_);
    crate::leanh::lean_dec(v_a_2032_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(
    mut v_x_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(
        v_a_2041_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed(
    mut v_x_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
    mut v_a_2054_: *mut crate::leanh::LeanObject,
    mut v_a_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(
        v_x_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_,
        v_a_2058_,
    );
    crate::leanh::lean_dec(v_a_2058_);
    crate::leanh::lean_dec_ref(v_a_2057_);
    crate::leanh::lean_dec(v_a_2056_);
    crate::leanh::lean_dec_ref(v_a_2055_);
    crate::leanh::lean_dec(v_a_2054_);
    crate::leanh::lean_dec_ref(v_a_2053_);
    crate::leanh::lean_dec(v_a_2052_);
    crate::leanh::lean_dec_ref(v_a_2051_);
    crate::leanh::lean_dec(v_x_2050_);
    return v_res_2060_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2080_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3;
    v___x_2081_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6;
    v___x_2082_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
    return v_res_2085_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
    mut v_e_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = l_Lean_Expr_hasMVar(v_e_2086_);
                if v___x_2089_ == 0 {
                    v___x_2090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2090_, 0, v_e_2086_);
                    return v___x_2090_;
                } else {
                    v___x_2091_ = lean_st_ref_get(v___y_2087_);
                    v_mctx_2092_ = crate::leanh::lean_ctor_get(v___x_2091_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2092_);
                    crate::leanh::lean_dec(v___x_2091_);
                    v___x_2093_ = l_Lean_instantiateMVarsCore(v_mctx_2092_, v_e_2086_);
                    v_fst_2094_ = crate::leanh::lean_ctor_get(v___x_2093_, 0);
                    crate::leanh::lean_inc(v_fst_2094_);
                    v_snd_2095_ = crate::leanh::lean_ctor_get(v___x_2093_, 1);
                    crate::leanh::lean_inc(v_snd_2095_);
                    crate::leanh::lean_dec_ref(v___x_2093_);
                    v___x_2096_ = lean_st_ref_take(v___y_2087_);
                    v_cache_2097_ = crate::leanh::lean_ctor_get(v___x_2096_, 1);
                    v_zetaDeltaFVarIds_2098_ = crate::leanh::lean_ctor_get(v___x_2096_, 2);
                    v_postponed_2099_ = crate::leanh::lean_ctor_get(v___x_2096_, 3);
                    v_diag_2100_ = crate::leanh::lean_ctor_get(v___x_2096_, 4);
                    v_isSharedCheck_2109_ = (!crate::leanh::lean_is_exclusive(v___x_2096_)) as u8;
                    if v_isSharedCheck_2109_ == 0 {
                        v_unused_2110_ = crate::leanh::lean_ctor_get(v___x_2096_, 0);
                        crate::leanh::lean_dec(v_unused_2110_);
                        v___x_2102_ = v___x_2096_;
                        v_isShared_2103_ = v_isSharedCheck_2109_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2100_);
                        crate::leanh::lean_inc(v_postponed_2099_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2098_);
                        crate::leanh::lean_inc(v_cache_2097_);
                        crate::leanh::lean_dec(v___x_2096_);
                        v___x_2102_ = crate::leanh::lean_box(0);
                        v_isShared_2103_ = v_isSharedCheck_2109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v_snd_2095_);
                    v___x_2105_ = v___x_2102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_snd_2095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_cache_2097_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2108_,
                        2,
                        v_zetaDeltaFVarIds_2098_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_postponed_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_diag_2100_);
                    v___x_2105_ = v_reuseFailAlloc_2108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2106_ = lean_st_ref_set(v___y_2087_, v___x_2105_);
                v___x_2107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2107_, 0, v_fst_2094_);
                return v___x_2107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg___boxed(
    mut v_e_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
            v_e_2111_,
            v___y_2112_,
        );
    crate::leanh::lean_dec(v___y_2112_);
    return v_res_2114_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(
    mut v_e_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(
            v_e_2115_,
            v___y_2121_,
        );
    return v___x_2125_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___boxed(
    mut v_e_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2134_);
    crate::leanh::lean_dec_ref(v___y_2133_);
    crate::leanh::lean_dec(v___y_2132_);
    crate::leanh::lean_dec_ref(v___y_2131_);
    crate::leanh::lean_dec(v___y_2130_);
    crate::leanh::lean_dec_ref(v___y_2129_);
    crate::leanh::lean_dec(v___y_2128_);
    crate::leanh::lean_dec_ref(v___y_2127_);
    return v_res_2136_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(
    mut v_x_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2141_);
    crate::leanh::lean_inc_ref(v___y_2140_);
    crate::leanh::lean_inc(v___y_2139_);
    crate::leanh::lean_inc_ref(v___y_2138_);
    v___x_2147_ = crate::leanh::lean_apply_9(
        v_x_2137_,
        v___y_2138_,
        v___y_2139_,
        v___y_2140_,
        v___y_2141_,
        v___y_2142_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
        crate::leanh::lean_box(0),
    );
    return v___x_2147_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed(
    mut v_x_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(v_x_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
    crate::leanh::lean_dec(v___y_2152_);
    crate::leanh::lean_dec_ref(v___y_2151_);
    crate::leanh::lean_dec(v___y_2150_);
    crate::leanh::lean_dec_ref(v___y_2149_);
    return v_res_2158_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(
    mut v_mvarId_2159_: *mut crate::leanh::LeanObject,
    mut v_x_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2164_);
                crate::leanh::lean_inc_ref(v___y_2163_);
                crate::leanh::lean_inc(v___y_2162_);
                crate::leanh::lean_inc_ref(v___y_2161_);
                v___f_2170_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_2170_, 0, v_x_2160_);
                crate::leanh::lean_closure_set(v___f_2170_, 1, v___y_2161_);
                crate::leanh::lean_closure_set(v___f_2170_, 2, v___y_2162_);
                crate::leanh::lean_closure_set(v___f_2170_, 3, v___y_2163_);
                crate::leanh::lean_closure_set(v___f_2170_, 4, v___y_2164_);
                v___x_2171_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2159_,
                    v___f_2170_,
                    v___y_2165_,
                    v___y_2166_,
                    v___y_2167_,
                    v___y_2168_,
                );
                if crate::leanh::lean_obj_tag(v___x_2171_) == 0 {
                    return v___x_2171_;
                } else {
                    v_a_2172_ = crate::leanh::lean_ctor_get(v___x_2171_, 0);
                    v_isSharedCheck_2179_ = (!crate::leanh::lean_is_exclusive(v___x_2171_)) as u8;
                    if v_isSharedCheck_2179_ == 0 {
                        v___x_2174_ = v___x_2171_;
                        v_isShared_2175_ = v_isSharedCheck_2179_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2172_);
                        crate::leanh::lean_dec(v___x_2171_);
                        v___x_2174_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
    mut v_mvarId_2180_: *mut crate::leanh::LeanObject,
    mut v_x_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2189_);
    crate::leanh::lean_dec_ref(v___y_2188_);
    crate::leanh::lean_dec(v___y_2187_);
    crate::leanh::lean_dec_ref(v___y_2186_);
    crate::leanh::lean_dec(v___y_2185_);
    crate::leanh::lean_dec_ref(v___y_2184_);
    crate::leanh::lean_dec(v___y_2183_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    return v_res_2191_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(
    mut v_00_u03b1_2192_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2193_: *mut crate::leanh::LeanObject,
    mut v_x_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2205_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2206_: *mut crate::leanh::LeanObject,
    mut v_x_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2215_);
    crate::leanh::lean_dec_ref(v___y_2214_);
    crate::leanh::lean_dec(v___y_2213_);
    crate::leanh::lean_dec_ref(v___y_2212_);
    crate::leanh::lean_dec(v___y_2211_);
    crate::leanh::lean_dec_ref(v___y_2210_);
    crate::leanh::lean_dec(v___y_2209_);
    crate::leanh::lean_dec_ref(v___y_2208_);
    return v_res_2217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(
    mut v_msg_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2224_ = crate::leanh::lean_ctor_get(v___y_2221_, 5);
                v___x_2225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
                v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2225_, 0);
                v_isSharedCheck_2234_ = (!crate::leanh::lean_is_exclusive(v___x_2225_)) as u8;
                if v_isSharedCheck_2234_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    v_isShared_2229_ = v_isSharedCheck_2234_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2226_);
                    crate::leanh::lean_dec(v___x_2225_);
                    v___x_2228_ = crate::leanh::lean_box(0);
                    v_isShared_2229_ = v_isSharedCheck_2234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2224_);
                v___x_2230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2230_, 0, v_ref_2224_);
                crate::leanh::lean_ctor_set(v___x_2230_, 1, v_a_2226_);
                if v_isShared_2229_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2228_, 1);
                    crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
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
    mut v_msg_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2241_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(
            v_msg_2235_,
            v___y_2236_,
            v___y_2237_,
            v___y_2238_,
            v___y_2239_,
        );
    crate::leanh::lean_dec(v___y_2239_);
    crate::leanh::lean_dec_ref(v___y_2238_);
    crate::leanh::lean_dec(v___y_2237_);
    crate::leanh::lean_dec_ref(v___y_2236_);
    return v_res_2241_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0;
    v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
    return v___x_2244_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2245_);
                v___x_2255_ = l_Lean_MVarId_getType(
                    v_a_2245_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                    v___y_2253_,
                );
                if crate::leanh::lean_obj_tag(v___x_2255_) == 0 {
                    v_a_2256_ = crate::leanh::lean_ctor_get(v___x_2255_, 0);
                    crate::leanh::lean_inc(v_a_2256_);
                    crate::leanh::lean_dec_ref_known(v___x_2255_, 1);
                    v___x_2257_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_a_2256_, v___y_2251_);
                    v_a_2258_ = crate::leanh::lean_ctor_get(v___x_2257_, 0);
                    crate::leanh::lean_inc(v_a_2258_);
                    crate::leanh::lean_dec_ref(v___x_2257_);
                    v___x_2259_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2258_);
                    crate::leanh::lean_dec(v_a_2258_);
                    if crate::leanh::lean_obj_tag(v___x_2259_) == 1 {
                        v_val_2260_ = crate::leanh::lean_ctor_get(v___x_2259_, 0);
                        crate::leanh::lean_inc(v_val_2260_);
                        crate::leanh::lean_dec_ref_known(v___x_2259_, 1);
                        v___x_2261_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(v_val_2260_);
                        v___x_2262_ =
                            l_Lean_MVarId_setType___redArg(v_a_2245_, v___x_2261_, v___y_2251_);
                        return v___x_2262_;
                    } else {
                        crate::leanh::lean_dec(v___x_2259_);
                        crate::leanh::lean_dec(v_a_2245_);
                        v___x_2263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1);
                        v___x_2264_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v___x_2263_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
                        return v___x_2264_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2245_);
                    v_a_2265_ = crate::leanh::lean_ctor_get(v___x_2255_, 0);
                    v_isSharedCheck_2272_ = (!crate::leanh::lean_is_exclusive(v___x_2255_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2255_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2265_);
                        crate::leanh::lean_dec(v___x_2255_);
                        v___x_2267_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
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
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2281_);
    crate::leanh::lean_dec_ref(v___y_2280_);
    crate::leanh::lean_dec(v___y_2279_);
    crate::leanh::lean_dec_ref(v___y_2278_);
    crate::leanh::lean_dec(v___y_2277_);
    crate::leanh::lean_dec_ref(v___y_2276_);
    crate::leanh::lean_dec(v___y_2275_);
    crate::leanh::lean_dec_ref(v___y_2274_);
    return v_res_2283_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
    mut v_a_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2293_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_2285_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_,
                );
                if crate::leanh::lean_obj_tag(v___x_2293_) == 0 {
                    v_a_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                    crate::leanh::lean_inc_n(v_a_2294_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2293_, 1);
                    v___f_2295_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2295_, 0, v_a_2294_);
                    v___x_2296_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_a_2294_, v___f_2295_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
                    return v___x_2296_;
                } else {
                    v_a_2297_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                    v_isSharedCheck_2304_ = (!crate::leanh::lean_is_exclusive(v___x_2293_)) as u8;
                    if v_isSharedCheck_2304_ == 0 {
                        v___x_2299_ = v___x_2293_;
                        v_isShared_2300_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2297_);
                        crate::leanh::lean_dec(v___x_2293_);
                        v___x_2299_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
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
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
    mut v_a_2307_: *mut crate::leanh::LeanObject,
    mut v_a_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
    mut v_a_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
        v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_,
    );
    crate::leanh::lean_dec(v_a_2312_);
    crate::leanh::lean_dec_ref(v_a_2311_);
    crate::leanh::lean_dec(v_a_2310_);
    crate::leanh::lean_dec_ref(v_a_2309_);
    crate::leanh::lean_dec(v_a_2308_);
    crate::leanh::lean_dec_ref(v_a_2307_);
    crate::leanh::lean_dec(v_a_2306_);
    crate::leanh::lean_dec_ref(v_a_2305_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(
    mut v_x_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(
        v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_,
    );
    return v___x_2325_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed(
    mut v_x_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
    mut v_a_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2336_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(
        v_x_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_,
        v_a_2334_,
    );
    crate::leanh::lean_dec(v_a_2334_);
    crate::leanh::lean_dec_ref(v_a_2333_);
    crate::leanh::lean_dec(v_a_2332_);
    crate::leanh::lean_dec_ref(v_a_2331_);
    crate::leanh::lean_dec(v_a_2330_);
    crate::leanh::lean_dec_ref(v_a_2329_);
    crate::leanh::lean_dec(v_a_2328_);
    crate::leanh::lean_dec_ref(v_a_2327_);
    crate::leanh::lean_dec(v_x_2326_);
    return v_res_2336_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(
    mut v_00_u03b1_2337_: *mut crate::leanh::LeanObject,
    mut v_msg_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2349_: *mut crate::leanh::LeanObject,
    mut v_msg_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2358_);
    crate::leanh::lean_dec_ref(v___y_2357_);
    crate::leanh::lean_dec(v___y_2356_);
    crate::leanh::lean_dec_ref(v___y_2355_);
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    crate::leanh::lean_dec(v___y_2352_);
    crate::leanh::lean_dec_ref(v___y_2351_);
    return v_res_2360_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2377_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1;
    v___x_2378_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3;
    v___x_2379_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
    return v_res_2382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
}
