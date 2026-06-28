// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Exfalso
// Imports: Lean.Elab.Tactic.Do.ProofMode.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr6};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure,
    l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp4, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value) as *mut LeanObject,907667957179513571 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 120, 102, 97, 108, 115, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value
        ) as *mut LeanObject,
        1854437328798449011 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 101, 120, 102, 97, 108, 115, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value) as *mut LeanObject,13495434297544269268 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 77, 69, 120, 102, 97, 108, 115, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value) as *mut LeanObject,10608129229174386580 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2()
-> *mut LeanObject {
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_651_ = lean_box(0);
    v___x_652_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1;
    v___x_653_ = l_Lean_mkConst(v___x_652_, v___x_651_);
    return v___x_653_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(
    mut v_u_654_: *mut LeanObject,
    mut v_00_u03c3s_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2);
    v___x_657_ =
        l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_654_, v_00_u03c3s_655_, v___x_656_);
    return v___x_657_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(
    mut v_e_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut v_unused_682_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_661_ = l_Lean_Expr_hasMVar(v_e_658_);
                if v___x_661_ == 0 {
                    v___x_662_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_662_, 0, v_e_658_);
                    return v___x_662_;
                } else {
                    v___x_663_ = lean_st_ref_get(v___y_659_);
                    v_mctx_664_ = lean_ctor_get(v___x_663_, 0);
                    lean_inc_ref(v_mctx_664_);
                    lean_dec(v___x_663_);
                    v___x_665_ = l_Lean_instantiateMVarsCore(v_mctx_664_, v_e_658_);
                    v_fst_666_ = lean_ctor_get(v___x_665_, 0);
                    lean_inc(v_fst_666_);
                    v_snd_667_ = lean_ctor_get(v___x_665_, 1);
                    lean_inc(v_snd_667_);
                    lean_dec_ref(v___x_665_);
                    v___x_668_ = lean_st_ref_take(v___y_659_);
                    v_cache_669_ = lean_ctor_get(v___x_668_, 1);
                    v_zetaDeltaFVarIds_670_ = lean_ctor_get(v___x_668_, 2);
                    v_postponed_671_ = lean_ctor_get(v___x_668_, 3);
                    v_diag_672_ = lean_ctor_get(v___x_668_, 4);
                    v_isSharedCheck_681_ = (!lean_is_exclusive(v___x_668_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v_unused_682_ = lean_ctor_get(v___x_668_, 0);
                        lean_dec(v_unused_682_);
                        v___x_674_ = v___x_668_;
                        v_isShared_675_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_672_);
                        lean_inc(v_postponed_671_);
                        lean_inc(v_zetaDeltaFVarIds_670_);
                        lean_inc(v_cache_669_);
                        lean_dec(v___x_668_);
                        v___x_674_ = lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_675_ == 0 {
                    lean_ctor_set(v___x_674_, 0, v_snd_667_);
                    v___x_677_ = v___x_674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_680_, 0, v_snd_667_);
                    lean_ctor_set(v_reuseFailAlloc_680_, 1, v_cache_669_);
                    lean_ctor_set(v_reuseFailAlloc_680_, 2, v_zetaDeltaFVarIds_670_);
                    lean_ctor_set(v_reuseFailAlloc_680_, 3, v_postponed_671_);
                    lean_ctor_set(v_reuseFailAlloc_680_, 4, v_diag_672_);
                    v___x_677_ = v_reuseFailAlloc_680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_678_ = lean_st_ref_set(v___y_659_, v___x_677_);
                v___x_679_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_679_, 0, v_fst_666_);
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg___boxed(
    mut v_e_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_686_: *mut LeanObject = core::ptr::null_mut();
    v_res_686_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_e_683_, v___y_684_);
    lean_dec(v___y_684_);
    return v_res_686_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0(
    mut v_e_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_e_687_, v___y_693_);
    return v___x_697_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___boxed(
    mut v_e_698_: *mut LeanObject,
    mut v___y_699_: *mut LeanObject,
    mut v___y_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_res_708_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0(
            v_e_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_,
            v___y_705_, v___y_706_,
        );
    lean_dec(v___y_706_);
    lean_dec_ref(v___y_705_);
    lean_dec(v___y_704_);
    lean_dec_ref(v___y_703_);
    lean_dec(v___y_702_);
    lean_dec_ref(v___y_701_);
    lean_dec(v___y_700_);
    lean_dec_ref(v___y_699_);
    return v_res_708_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0(
    mut v_x_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
    mut v___y_715_: *mut LeanObject,
    mut v___y_716_: *mut LeanObject,
    mut v___y_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_713_);
    lean_inc_ref(v___y_712_);
    lean_inc(v___y_711_);
    lean_inc_ref(v___y_710_);
    v___x_719_ = lean_apply_9(
        v_x_709_,
        v___y_710_,
        v___y_711_,
        v___y_712_,
        v___y_713_,
        v___y_714_,
        v___y_715_,
        v___y_716_,
        v___y_717_,
        lean_box(0),
    );
    return v___x_719_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0___boxed(
    mut v_x_720_: *mut LeanObject,
    mut v___y_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
    mut v___y_726_: *mut LeanObject,
    mut v___y_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0(v_x_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
    lean_dec(v___y_724_);
    lean_dec_ref(v___y_723_);
    lean_dec(v___y_722_);
    lean_dec_ref(v___y_721_);
    return v_res_730_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(
    mut v_mvarId_731_: *mut LeanObject,
    mut v_x_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_747_: u8 = 0;
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_736_);
                lean_inc_ref(v___y_735_);
                lean_inc(v___y_734_);
                lean_inc_ref(v___y_733_);
                v___f_742_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_742_, 0, v_x_732_);
                lean_closure_set(v___f_742_, 1, v___y_733_);
                lean_closure_set(v___f_742_, 2, v___y_734_);
                lean_closure_set(v___f_742_, 3, v___y_735_);
                lean_closure_set(v___f_742_, 4, v___y_736_);
                v___x_743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_731_,
                    v___f_742_,
                    v___y_737_,
                    v___y_738_,
                    v___y_739_,
                    v___y_740_,
                );
                if lean_obj_tag(v___x_743_) == 0 {
                    return v___x_743_;
                } else {
                    v_a_744_ = lean_ctor_get(v___x_743_, 0);
                    v_isSharedCheck_751_ = (!lean_is_exclusive(v___x_743_)) as u8;
                    if v_isSharedCheck_751_ == 0 {
                        v___x_746_ = v___x_743_;
                        v_isShared_747_ = v_isSharedCheck_751_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_744_);
                        lean_dec(v___x_743_);
                        v___x_746_ = lean_box(0);
                        v_isShared_747_ = v_isSharedCheck_751_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_747_ == 0 {
                    v___x_749_ = v___x_746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
                    v___x_749_ = v_reuseFailAlloc_750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___boxed(
    mut v_mvarId_752_: *mut LeanObject,
    mut v_x_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
    mut v___y_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
    mut v___y_759_: *mut LeanObject,
    mut v___y_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_763_: *mut LeanObject = core::ptr::null_mut();
    v_res_763_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_mvarId_752_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
    lean_dec(v___y_761_);
    lean_dec_ref(v___y_760_);
    lean_dec(v___y_759_);
    lean_dec_ref(v___y_758_);
    lean_dec(v___y_757_);
    lean_dec_ref(v___y_756_);
    lean_dec(v___y_755_);
    lean_dec_ref(v___y_754_);
    return v_res_763_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3(
    mut v_00_u03b1_764_: *mut LeanObject,
    mut v_mvarId_765_: *mut LeanObject,
    mut v_x_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_mvarId_765_, v_x_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
    return v___x_776_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___boxed(
    mut v_00_u03b1_777_: *mut LeanObject,
    mut v_mvarId_778_: *mut LeanObject,
    mut v_x_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_789_: *mut LeanObject = core::ptr::null_mut();
    v_res_789_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3(
            v_00_u03b1_777_,
            v_mvarId_778_,
            v_x_779_,
            v___y_780_,
            v___y_781_,
            v___y_782_,
            v___y_783_,
            v___y_784_,
            v___y_785_,
            v___y_786_,
            v___y_787_,
        );
    lean_dec(v___y_787_);
    lean_dec_ref(v___y_786_);
    lean_dec(v___y_785_);
    lean_dec_ref(v___y_784_);
    lean_dec(v___y_783_);
    lean_dec_ref(v___y_782_);
    lean_dec(v___y_781_);
    lean_dec_ref(v___y_780_);
    return v_res_789_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(
    mut v_msgData_790_: *mut LeanObject,
    mut v___y_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    v___x_796_ = lean_st_ref_get(v___y_794_);
    v_env_797_ = lean_ctor_get(v___x_796_, 0);
    lean_inc_ref(v_env_797_);
    lean_dec(v___x_796_);
    v___x_798_ = lean_st_ref_get(v___y_792_);
    v_mctx_799_ = lean_ctor_get(v___x_798_, 0);
    lean_inc_ref(v_mctx_799_);
    lean_dec(v___x_798_);
    v_lctx_800_ = lean_ctor_get(v___y_791_, 2);
    v_options_801_ = lean_ctor_get(v___y_793_, 2);
    lean_inc_ref(v_options_801_);
    lean_inc_ref(v_lctx_800_);
    v___x_802_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_802_, 0, v_env_797_);
    lean_ctor_set(v___x_802_, 1, v_mctx_799_);
    lean_ctor_set(v___x_802_, 2, v_lctx_800_);
    lean_ctor_set(v___x_802_, 3, v_options_801_);
    v___x_803_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_803_, 0, v___x_802_);
    lean_ctor_set(v___x_803_, 1, v_msgData_790_);
    v___x_804_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_804_, 0, v___x_803_);
    return v___x_804_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3___boxed(
    mut v_msgData_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_811_: *mut LeanObject = core::ptr::null_mut();
    v_res_811_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msgData_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
    lean_dec(v___y_809_);
    lean_dec_ref(v___y_808_);
    lean_dec(v___y_807_);
    lean_dec_ref(v___y_806_);
    return v_res_811_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(
    mut v_msg_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
    mut v___y_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_818_ = lean_ctor_get(v___y_815_, 5);
                v___x_819_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msg_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
                v_a_820_ = lean_ctor_get(v___x_819_, 0);
                v_isSharedCheck_828_ = (!lean_is_exclusive(v___x_819_)) as u8;
                if v_isSharedCheck_828_ == 0 {
                    v___x_822_ = v___x_819_;
                    v_isShared_823_ = v_isSharedCheck_828_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_820_);
                    lean_dec(v___x_819_);
                    v___x_822_ = lean_box(0);
                    v_isShared_823_ = v_isSharedCheck_828_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_818_);
                v___x_824_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_824_, 0, v_ref_818_);
                lean_ctor_set(v___x_824_, 1, v_a_820_);
                if v_isShared_823_ == 0 {
                    lean_ctor_set_tag(v___x_822_, 1);
                    lean_ctor_set(v___x_822_, 0, v___x_824_);
                    v___x_826_ = v___x_822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
                    v___x_826_ = v_reuseFailAlloc_827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg___boxed(
    mut v_msg_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_835_: *mut LeanObject = core::ptr::null_mut();
    v_res_835_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(
            v_msg_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_,
        );
    lean_dec(v___y_833_);
    lean_dec_ref(v___y_832_);
    lean_dec(v___y_831_);
    lean_dec_ref(v___y_830_);
    return v_res_835_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(
    mut v_x_836_: *mut LeanObject,
    mut v_x_837_: *mut LeanObject,
    mut v_x_838_: *mut LeanObject,
    mut v_x_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_844_: u8 = 0;
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_840_ = lean_ctor_get(v_x_836_, 0);
                v_vs_841_ = lean_ctor_get(v_x_836_, 1);
                v_isSharedCheck_865_ = (!lean_is_exclusive(v_x_836_)) as u8;
                if v_isSharedCheck_865_ == 0 {
                    v___x_843_ = v_x_836_;
                    v_isShared_844_ = v_isSharedCheck_865_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_841_);
                    lean_inc(v_ks_840_);
                    lean_dec(v_x_836_);
                    v___x_843_ = lean_box(0);
                    v_isShared_844_ = v_isSharedCheck_865_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_845_ = lean_array_get_size(v_ks_840_);
                v___x_846_ = lean_nat_dec_lt(v_x_837_, v___x_845_);
                if v___x_846_ == 0 {
                    lean_dec(v_x_837_);
                    v___x_847_ = lean_array_push(v_ks_840_, v_x_838_);
                    v___x_848_ = lean_array_push(v_vs_841_, v_x_839_);
                    if v_isShared_844_ == 0 {
                        lean_ctor_set(v___x_843_, 1, v___x_848_);
                        lean_ctor_set(v___x_843_, 0, v___x_847_);
                        v___x_850_ = v___x_843_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
                        lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
                        v___x_850_ = v_reuseFailAlloc_851_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_852_ = lean_array_fget_borrowed(v_ks_840_, v_x_837_);
                    v___x_853_ = l_Lean_instBEqMVarId_beq(v_x_838_, v_k_x27_852_);
                    if v___x_853_ == 0 {
                        if v_isShared_844_ == 0 {
                            v___x_855_ = v___x_843_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_859_, 0, v_ks_840_);
                            lean_ctor_set(v_reuseFailAlloc_859_, 1, v_vs_841_);
                            v___x_855_ = v_reuseFailAlloc_859_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_860_ = lean_array_fset(v_ks_840_, v_x_837_, v_x_838_);
                        v___x_861_ = lean_array_fset(v_vs_841_, v_x_837_, v_x_839_);
                        lean_dec(v_x_837_);
                        if v_isShared_844_ == 0 {
                            lean_ctor_set(v___x_843_, 1, v___x_861_);
                            lean_ctor_set(v___x_843_, 0, v___x_860_);
                            v___x_863_ = v___x_843_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_860_);
                            lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_861_);
                            v___x_863_ = v_reuseFailAlloc_864_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_850_;
            }
            3 => {
                v___x_856_ = lean_unsigned_to_nat(1);
                v___x_857_ = lean_nat_add(v_x_837_, v___x_856_);
                lean_dec(v_x_837_);
                v_x_836_ = v___x_855_;
                v_x_837_ = v___x_857_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(
    mut v_n_866_: *mut LeanObject,
    mut v_k_867_: *mut LeanObject,
    mut v_v_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = lean_unsigned_to_nat(0);
    v___x_870_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_866_, v___x_869_, v_k_867_, v_v_868_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    let mut v___x_873_: usize = 0;
    v___x_871_ = 5usize;
    v___x_872_ = 1usize;
    v___x_873_ = lean_usize_shift_left(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_874_: usize = 0;
    let mut v___x_875_: usize = 0;
    let mut v___x_876_: usize = 0;
    v___x_874_ = 1usize;
    v___x_875_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_876_ = lean_usize_sub(v___x_875_, v___x_874_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_877_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(
    mut v_x_878_: *mut LeanObject,
    mut v_x_879_: usize,
    mut v_x_880_: usize,
    mut v_x_881_: *mut LeanObject,
    mut v_x_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: usize = 0;
    let mut v___x_885_: usize = 0;
    let mut v___x_886_: usize = 0;
    let mut v___x_887_: usize = 0;
    let mut v_j_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v_v_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v_node_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: usize = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_927_: u8 = 0;
    let mut v_unused_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_938_: u8 = 0;
    let mut v_ks_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: usize = 0;
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v_reuseFailAlloc_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_878_) == 0 {
                    v_es_883_ = lean_ctor_get(v_x_878_, 0);
                    v___x_884_ = 5usize;
                    v___x_885_ = 1usize;
                    v___x_886_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_887_ = lean_usize_land(v_x_879_, v___x_886_);
                    v_j_888_ = lean_usize_to_nat(v___x_887_);
                    v___x_889_ = lean_array_get_size(v_es_883_);
                    v___x_890_ = lean_nat_dec_lt(v_j_888_, v___x_889_);
                    if v___x_890_ == 0 {
                        lean_dec(v_j_888_);
                        lean_dec(v_x_882_);
                        lean_dec(v_x_881_);
                        return v_x_878_;
                    } else {
                        lean_inc_ref(v_es_883_);
                        v_isSharedCheck_927_ = (!lean_is_exclusive(v_x_878_)) as u8;
                        if v_isSharedCheck_927_ == 0 {
                            v_unused_928_ = lean_ctor_get(v_x_878_, 0);
                            lean_dec(v_unused_928_);
                            v___x_892_ = v_x_878_;
                            v_isShared_893_ = v_isSharedCheck_927_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_878_);
                            v___x_892_ = lean_box(0);
                            v_isShared_893_ = v_isSharedCheck_927_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_929_ = lean_ctor_get(v_x_878_, 0);
                    v_vs_930_ = lean_ctor_get(v_x_878_, 1);
                    v_isSharedCheck_950_ = (!lean_is_exclusive(v_x_878_)) as u8;
                    if v_isSharedCheck_950_ == 0 {
                        v___x_932_ = v_x_878_;
                        v_isShared_933_ = v_isSharedCheck_950_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_930_);
                        lean_inc(v_ks_929_);
                        lean_dec(v_x_878_);
                        v___x_932_ = lean_box(0);
                        v_isShared_933_ = v_isSharedCheck_950_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_894_ = lean_array_fget(v_es_883_, v_j_888_);
                v___x_895_ = lean_box(0);
                v_xs_x27_896_ = lean_array_fset(v_es_883_, v_j_888_, v___x_895_);
                match lean_obj_tag(v_v_894_) {
                    0 => {
                        v_key_903_ = lean_ctor_get(v_v_894_, 0);
                        v_val_904_ = lean_ctor_get(v_v_894_, 1);
                        v_isSharedCheck_914_ = (!lean_is_exclusive(v_v_894_)) as u8;
                        if v_isSharedCheck_914_ == 0 {
                            v___x_906_ = v_v_894_;
                            v_isShared_907_ = v_isSharedCheck_914_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_904_);
                            lean_inc(v_key_903_);
                            lean_dec(v_v_894_);
                            v___x_906_ = lean_box(0);
                            v_isShared_907_ = v_isSharedCheck_914_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_915_ = lean_ctor_get(v_v_894_, 0);
                        v_isSharedCheck_925_ = (!lean_is_exclusive(v_v_894_)) as u8;
                        if v_isSharedCheck_925_ == 0 {
                            v___x_917_ = v_v_894_;
                            v_isShared_918_ = v_isSharedCheck_925_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_915_);
                            lean_dec(v_v_894_);
                            v___x_917_ = lean_box(0);
                            v_isShared_918_ = v_isSharedCheck_925_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_926_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_926_, 0, v_x_881_);
                        lean_ctor_set(v___x_926_, 1, v_x_882_);
                        v___y_898_ = v___x_926_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_899_ = lean_array_fset(v_xs_x27_896_, v_j_888_, v___y_898_);
                lean_dec(v_j_888_);
                if v_isShared_893_ == 0 {
                    lean_ctor_set(v___x_892_, 0, v___x_899_);
                    v___x_901_ = v___x_892_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
                    v___x_901_ = v_reuseFailAlloc_902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_901_;
            }
            4 => {
                v___x_908_ = l_Lean_instBEqMVarId_beq(v_x_881_, v_key_903_);
                if v___x_908_ == 0 {
                    lean_del_object(v___x_906_);
                    v___x_909_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_903_, v_val_904_, v_x_881_, v_x_882_,
                    );
                    v___x_910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_910_, 0, v___x_909_);
                    v___y_898_ = v___x_910_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_904_);
                    lean_dec(v_key_903_);
                    if v_isShared_907_ == 0 {
                        lean_ctor_set(v___x_906_, 1, v_x_882_);
                        lean_ctor_set(v___x_906_, 0, v_x_881_);
                        v___x_912_ = v___x_906_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_913_, 0, v_x_881_);
                        lean_ctor_set(v_reuseFailAlloc_913_, 1, v_x_882_);
                        v___x_912_ = v_reuseFailAlloc_913_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_898_ = v___x_912_;
                state = 2;
                continue;
            }
            6 => {
                v___x_919_ = lean_usize_shift_right(v_x_879_, v___x_884_);
                v___x_920_ = lean_usize_add(v_x_880_, v___x_885_);
                v___x_921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_node_915_, v___x_919_, v___x_920_, v_x_881_, v_x_882_);
                if v_isShared_918_ == 0 {
                    lean_ctor_set(v___x_917_, 0, v___x_921_);
                    v___x_923_ = v___x_917_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
                    v___x_923_ = v_reuseFailAlloc_924_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_898_ = v___x_923_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_933_ == 0 {
                    v___x_935_ = v___x_932_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_949_, 0, v_ks_929_);
                    lean_ctor_set(v_reuseFailAlloc_949_, 1, v_vs_930_);
                    v___x_935_ = v_reuseFailAlloc_949_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_936_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v___x_935_, v_x_881_, v_x_882_);
                v___x_944_ = 7usize;
                v___x_945_ = lean_usize_dec_le(v___x_944_, v_x_880_);
                if v___x_945_ == 0 {
                    v___x_946_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_936_);
                    v___x_947_ = lean_unsigned_to_nat(4);
                    v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
                    lean_dec(v___x_946_);
                    v___y_938_ = v___x_948_;
                    state = 10;
                    continue;
                } else {
                    v___y_938_ = v___x_945_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_938_ == 0 {
                    v_ks_939_ = lean_ctor_get(v_newNode_936_, 0);
                    lean_inc_ref(v_ks_939_);
                    v_vs_940_ = lean_ctor_get(v_newNode_936_, 1);
                    lean_inc_ref(v_vs_940_);
                    lean_dec_ref(v_newNode_936_);
                    v___x_941_ = lean_unsigned_to_nat(0);
                    v___x_942_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_x_880_, v_ks_939_, v_vs_940_, v___x_941_, v___x_942_);
                    lean_dec_ref(v_vs_940_);
                    lean_dec_ref(v_ks_939_);
                    return v___x_943_;
                } else {
                    return v_newNode_936_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(
    mut v_depth_951_: usize,
    mut v_keys_952_: *mut LeanObject,
    mut v_vals_953_: *mut LeanObject,
    mut v_i_954_: *mut LeanObject,
    mut v_entries_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    let mut v_k_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u64 = 0;
    let mut v_h_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: usize = 0;
    let mut v___x_965_: usize = 0;
    let mut v___x_966_: usize = 0;
    let mut v_h_967_: usize = 0;
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_956_ = lean_array_get_size(v_keys_952_);
                v___x_957_ = lean_nat_dec_lt(v_i_954_, v___x_956_);
                if v___x_957_ == 0 {
                    lean_dec(v_i_954_);
                    return v_entries_955_;
                } else {
                    v_k_958_ = lean_array_fget_borrowed(v_keys_952_, v_i_954_);
                    v_v_959_ = lean_array_fget_borrowed(v_vals_953_, v_i_954_);
                    v___x_960_ = l_Lean_instHashableMVarId_hash(v_k_958_);
                    v_h_961_ = lean_uint64_to_usize(v___x_960_);
                    v___x_962_ = 5usize;
                    v___x_963_ = lean_unsigned_to_nat(1);
                    v___x_964_ = 1usize;
                    v___x_965_ = lean_usize_sub(v_depth_951_, v___x_964_);
                    v___x_966_ = lean_usize_mul(v___x_962_, v___x_965_);
                    v_h_967_ = lean_usize_shift_right(v_h_961_, v___x_966_);
                    v___x_968_ = lean_nat_add(v_i_954_, v___x_963_);
                    lean_dec(v_i_954_);
                    lean_inc(v_v_959_);
                    lean_inc(v_k_958_);
                    v___x_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_entries_955_, v_h_967_, v_depth_951_, v_k_958_, v_v_959_);
                    v_i_954_ = v___x_968_;
                    v_entries_955_ = v___x_969_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_971_: *mut LeanObject,
    mut v_keys_972_: *mut LeanObject,
    mut v_vals_973_: *mut LeanObject,
    mut v_i_974_: *mut LeanObject,
    mut v_entries_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_976_: usize = 0;
    let mut v_res_977_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_976_ = lean_unbox_usize(v_depth_971_);
    lean_dec(v_depth_971_);
    v_res_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_976_, v_keys_972_, v_vals_973_, v_i_974_, v_entries_975_);
    lean_dec_ref(v_vals_973_);
    lean_dec_ref(v_keys_972_);
    return v_res_977_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_978_: *mut LeanObject,
    mut v_x_979_: *mut LeanObject,
    mut v_x_980_: *mut LeanObject,
    mut v_x_981_: *mut LeanObject,
    mut v_x_982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5680__boxed_983_: usize = 0;
    let mut v_x_5681__boxed_984_: usize = 0;
    let mut v_res_985_: *mut LeanObject = core::ptr::null_mut();
    v_x_5680__boxed_983_ = lean_unbox_usize(v_x_979_);
    lean_dec(v_x_979_);
    v_x_5681__boxed_984_ = lean_unbox_usize(v_x_980_);
    lean_dec(v_x_980_);
    v_res_985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_978_, v_x_5680__boxed_983_, v_x_5681__boxed_984_, v_x_981_, v_x_982_);
    return v_res_985_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(
    mut v_x_986_: *mut LeanObject,
    mut v_x_987_: *mut LeanObject,
    mut v_x_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_989_: u64 = 0;
    let mut v___x_990_: usize = 0;
    let mut v___x_991_: usize = 0;
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_989_ = l_Lean_instHashableMVarId_hash(v_x_987_);
    v___x_990_ = lean_uint64_to_usize(v___x_989_);
    v___x_991_ = 1usize;
    v___x_992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_986_, v___x_990_, v___x_991_, v_x_987_, v_x_988_);
    return v___x_992_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(
    mut v_mvarId_993_: *mut LeanObject,
    mut v_val_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v_depth_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1018_: u8 = 0;
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_997_ = lean_st_ref_take(v___y_995_);
                v_mctx_998_ = lean_ctor_get(v___x_997_, 0);
                v_cache_999_ = lean_ctor_get(v___x_997_, 1);
                v_zetaDeltaFVarIds_1000_ = lean_ctor_get(v___x_997_, 2);
                v_postponed_1001_ = lean_ctor_get(v___x_997_, 3);
                v_diag_1002_ = lean_ctor_get(v___x_997_, 4);
                v_isSharedCheck_1030_ = (!lean_is_exclusive(v___x_997_)) as u8;
                if v_isSharedCheck_1030_ == 0 {
                    v___x_1004_ = v___x_997_;
                    v_isShared_1005_ = v_isSharedCheck_1030_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1002_);
                    lean_inc(v_postponed_1001_);
                    lean_inc(v_zetaDeltaFVarIds_1000_);
                    lean_inc(v_cache_999_);
                    lean_inc(v_mctx_998_);
                    lean_dec(v___x_997_);
                    v___x_1004_ = lean_box(0);
                    v_isShared_1005_ = v_isSharedCheck_1030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1006_ = lean_ctor_get(v_mctx_998_, 0);
                v_levelAssignDepth_1007_ = lean_ctor_get(v_mctx_998_, 1);
                v_lmvarCounter_1008_ = lean_ctor_get(v_mctx_998_, 2);
                v_mvarCounter_1009_ = lean_ctor_get(v_mctx_998_, 3);
                v_lDecls_1010_ = lean_ctor_get(v_mctx_998_, 4);
                v_decls_1011_ = lean_ctor_get(v_mctx_998_, 5);
                v_userNames_1012_ = lean_ctor_get(v_mctx_998_, 6);
                v_lAssignment_1013_ = lean_ctor_get(v_mctx_998_, 7);
                v_eAssignment_1014_ = lean_ctor_get(v_mctx_998_, 8);
                v_dAssignment_1015_ = lean_ctor_get(v_mctx_998_, 9);
                v_isSharedCheck_1029_ = (!lean_is_exclusive(v_mctx_998_)) as u8;
                if v_isSharedCheck_1029_ == 0 {
                    v___x_1017_ = v_mctx_998_;
                    v_isShared_1018_ = v_isSharedCheck_1029_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1015_);
                    lean_inc(v_eAssignment_1014_);
                    lean_inc(v_lAssignment_1013_);
                    lean_inc(v_userNames_1012_);
                    lean_inc(v_decls_1011_);
                    lean_inc(v_lDecls_1010_);
                    lean_inc(v_mvarCounter_1009_);
                    lean_inc(v_lmvarCounter_1008_);
                    lean_inc(v_levelAssignDepth_1007_);
                    lean_inc(v_depth_1006_);
                    lean_dec(v_mctx_998_);
                    v___x_1017_ = lean_box(0);
                    v_isShared_1018_ = v_isSharedCheck_1029_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1019_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_eAssignment_1014_, v_mvarId_993_, v_val_994_);
                if v_isShared_1018_ == 0 {
                    lean_ctor_set(v___x_1017_, 8, v___x_1019_);
                    v___x_1021_ = v___x_1017_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_depth_1006_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_levelAssignDepth_1007_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_lmvarCounter_1008_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_mvarCounter_1009_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_lDecls_1010_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 5, v_decls_1011_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 6, v_userNames_1012_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 7, v_lAssignment_1013_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 8, v___x_1019_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 9, v_dAssignment_1015_);
                    v___x_1021_ = v_reuseFailAlloc_1028_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1005_ == 0 {
                    lean_ctor_set(v___x_1004_, 0, v___x_1021_);
                    v___x_1023_ = v___x_1004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1021_);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_cache_999_);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_zetaDeltaFVarIds_1000_);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_postponed_1001_);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_diag_1002_);
                    v___x_1023_ = v_reuseFailAlloc_1027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1024_ = lean_st_ref_set(v___y_995_, v___x_1023_);
                v___x_1025_ = lean_box(0);
                v___x_1026_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1026_, 0, v___x_1025_);
                return v___x_1026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg___boxed(
    mut v_mvarId_1031_: *mut LeanObject,
    mut v_val_1032_: *mut LeanObject,
    mut v___y_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(
            v_mvarId_1031_,
            v_val_1032_,
            v___y_1033_,
        );
    lean_dec(v___y_1033_);
    return v_res_1035_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5;
    v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(
    mut v_a_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_reuseFailAlloc_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1048_);
                v___x_1058_ = l_Lean_MVarId_getType(
                    v_a_1048_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                    v___y_1056_,
                );
                if lean_obj_tag(v___x_1058_) == 0 {
                    v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
                    lean_inc(v_a_1059_);
                    lean_dec_ref_known(v___x_1058_, 1);
                    v___x_1060_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_a_1059_, v___y_1054_);
                    v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
                    lean_inc(v_a_1061_);
                    lean_dec_ref(v___x_1060_);
                    v___x_1062_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1061_);
                    lean_dec(v_a_1061_);
                    if lean_obj_tag(v___x_1062_) == 1 {
                        v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
                        lean_inc(v_val_1063_);
                        lean_dec_ref_known(v___x_1062_, 1);
                        v_u_1064_ = lean_ctor_get(v_val_1063_, 0);
                        v_00_u03c3s_1065_ = lean_ctor_get(v_val_1063_, 1);
                        v_hyps_1066_ = lean_ctor_get(v_val_1063_, 2);
                        v_target_1067_ = lean_ctor_get(v_val_1063_, 3);
                        v_isSharedCheck_1096_ = (!lean_is_exclusive(v_val_1063_)) as u8;
                        if v_isSharedCheck_1096_ == 0 {
                            v___x_1069_ = v_val_1063_;
                            v_isShared_1070_ = v_isSharedCheck_1096_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_target_1067_);
                            lean_inc(v_hyps_1066_);
                            lean_inc(v_00_u03c3s_1065_);
                            lean_inc(v_u_1064_);
                            lean_dec(v_val_1063_);
                            v___x_1069_ = lean_box(0);
                            v_isShared_1070_ = v_isSharedCheck_1096_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1062_);
                        lean_dec(v_a_1048_);
                        v___x_1097_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6);
                        v___x_1098_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v___x_1097_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
                        return v___x_1098_;
                    }
                } else {
                    lean_dec(v_a_1048_);
                    v_a_1099_ = lean_ctor_get(v___x_1058_, 0);
                    v_isSharedCheck_1106_ = (!lean_is_exclusive(v___x_1058_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1101_ = v___x_1058_;
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1099_);
                        lean_dec(v___x_1058_);
                        v___x_1101_ = lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v_00_u03c3s_1065_, 2);
                lean_inc_n(v_u_1064_, 2);
                v___x_1071_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(v_u_1064_, v_00_u03c3s_1065_);
                lean_inc_ref(v_hyps_1066_);
                if v_isShared_1070_ == 0 {
                    lean_ctor_set(v___x_1069_, 3, v___x_1071_);
                    v___x_1073_ = v___x_1069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_u_1064_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_00_u03c3s_1065_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_hyps_1066_);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 3, v___x_1071_);
                    v___x_1073_ = v_reuseFailAlloc_1095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1074_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1073_);
                v___x_1075_ = lean_box(0);
                v___x_1076_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1074_,
                    v___x_1075_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                    v___y_1056_,
                );
                if lean_obj_tag(v___x_1076_) == 0 {
                    v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
                    lean_inc_n(v_a_1077_, 2);
                    lean_dec_ref_known(v___x_1076_, 1);
                    v___x_1078_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4;
                    v___x_1079_ = lean_box(0);
                    v___x_1080_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1080_, 0, v_u_1064_);
                    lean_ctor_set(v___x_1080_, 1, v___x_1079_);
                    v___x_1081_ = l_Lean_mkConst(v___x_1078_, v___x_1080_);
                    v___x_1082_ = l_Lean_mkApp4(
                        v___x_1081_,
                        v_00_u03c3s_1065_,
                        v_hyps_1066_,
                        v_target_1067_,
                        v_a_1077_,
                    );
                    v___x_1083_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_a_1048_, v___x_1082_, v___y_1054_);
                    lean_dec_ref(v___x_1083_);
                    v___x_1084_ = l_Lean_Expr_mvarId_x21(v_a_1077_);
                    lean_dec(v_a_1077_);
                    v___x_1085_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1085_, 0, v___x_1084_);
                    lean_ctor_set(v___x_1085_, 1, v___x_1079_);
                    v___x_1086_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1085_,
                        v___y_1050_,
                        v___y_1053_,
                        v___y_1054_,
                        v___y_1055_,
                        v___y_1056_,
                    );
                    return v___x_1086_;
                } else {
                    lean_dec_ref(v_target_1067_);
                    lean_dec_ref(v_hyps_1066_);
                    lean_dec_ref(v_00_u03c3s_1065_);
                    lean_dec(v_u_1064_);
                    lean_dec(v_a_1048_);
                    v_a_1087_ = lean_ctor_get(v___x_1076_, 0);
                    v_isSharedCheck_1094_ = (!lean_is_exclusive(v___x_1076_)) as u8;
                    if v_isSharedCheck_1094_ == 0 {
                        v___x_1089_ = v___x_1076_;
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1087_);
                        lean_dec(v___x_1076_);
                        v___x_1089_ = lean_box(0);
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1090_ == 0 {
                    v___x_1092_ = v___x_1089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
                    v___x_1092_ = v_reuseFailAlloc_1093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1092_;
            }
            5 => {
                if v_isShared_1102_ == 0 {
                    v___x_1104_ = v___x_1101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed(
    mut v_a_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1117_: *mut LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(
        v_a_1107_,
        v___y_1108_,
        v___y_1109_,
        v___y_1110_,
        v___y_1111_,
        v___y_1112_,
        v___y_1113_,
        v___y_1114_,
        v___y_1115_,
    );
    lean_dec(v___y_1115_);
    lean_dec_ref(v___y_1114_);
    lean_dec(v___y_1113_);
    lean_dec_ref(v___y_1112_);
    lean_dec(v___y_1111_);
    lean_dec_ref(v___y_1110_);
    lean_dec(v___y_1109_);
    lean_dec_ref(v___y_1108_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1127_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1119_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_,
                );
                if lean_obj_tag(v___x_1127_) == 0 {
                    v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
                    lean_inc_n(v_a_1128_, 2);
                    lean_dec_ref_known(v___x_1127_, 1);
                    v___f_1129_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_1129_, 0, v_a_1128_);
                    v___x_1130_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_a_1128_, v___f_1129_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
                    return v___x_1130_;
                } else {
                    v_a_1131_ = lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1138_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1138_ == 0 {
                        v___x_1133_ = v___x_1127_;
                        v_isShared_1134_ = v_isSharedCheck_1138_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1131_);
                        lean_dec(v___x_1127_);
                        v___x_1133_ = lean_box(0);
                        v_isShared_1134_ = v_isSharedCheck_1138_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1134_ == 0 {
                    v___x_1136_ = v___x_1133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___boxed(
    mut v_a_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
    mut v_a_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(
        v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_,
    );
    lean_dec(v_a_1146_);
    lean_dec_ref(v_a_1145_);
    lean_dec(v_a_1144_);
    lean_dec_ref(v_a_1143_);
    lean_dec(v_a_1142_);
    lean_dec_ref(v_a_1141_);
    lean_dec(v_a_1140_);
    lean_dec_ref(v_a_1139_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(
    mut v_x_1149_: *mut LeanObject,
    mut v_a_1150_: *mut LeanObject,
    mut v_a_1151_: *mut LeanObject,
    mut v_a_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(
        v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_,
    );
    return v___x_1159_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed(
    mut v_x_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(
        v_x_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_,
        v_a_1168_,
    );
    lean_dec(v_a_1168_);
    lean_dec_ref(v_a_1167_);
    lean_dec(v_a_1166_);
    lean_dec_ref(v_a_1165_);
    lean_dec(v_a_1164_);
    lean_dec_ref(v_a_1163_);
    lean_dec(v_a_1162_);
    lean_dec_ref(v_a_1161_);
    lean_dec(v_x_1160_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(
    mut v_mvarId_1171_: *mut LeanObject,
    mut v_val_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(
            v_mvarId_1171_,
            v_val_1172_,
            v___y_1178_,
        );
    return v___x_1182_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___boxed(
    mut v_mvarId_1183_: *mut LeanObject,
    mut v_val_1184_: *mut LeanObject,
    mut v___y_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
    mut v___y_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1194_: *mut LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(
        v_mvarId_1183_,
        v_val_1184_,
        v___y_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        v___y_1190_,
        v___y_1191_,
        v___y_1192_,
    );
    lean_dec(v___y_1192_);
    lean_dec_ref(v___y_1191_);
    lean_dec(v___y_1190_);
    lean_dec_ref(v___y_1189_);
    lean_dec(v___y_1188_);
    lean_dec_ref(v___y_1187_);
    lean_dec(v___y_1186_);
    lean_dec_ref(v___y_1185_);
    return v_res_1194_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(
    mut v_00_u03b1_1195_: *mut LeanObject,
    mut v_msg_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    v___x_1206_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(
            v_msg_1196_,
            v___y_1201_,
            v___y_1202_,
            v___y_1203_,
            v___y_1204_,
        );
    return v___x_1206_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___boxed(
    mut v_00_u03b1_1207_: *mut LeanObject,
    mut v_msg_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1218_: *mut LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(
        v_00_u03b1_1207_,
        v_msg_1208_,
        v___y_1209_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
        v___y_1214_,
        v___y_1215_,
        v___y_1216_,
    );
    lean_dec(v___y_1216_);
    lean_dec_ref(v___y_1215_);
    lean_dec(v___y_1214_);
    lean_dec_ref(v___y_1213_);
    lean_dec(v___y_1212_);
    lean_dec_ref(v___y_1211_);
    lean_dec(v___y_1210_);
    lean_dec_ref(v___y_1209_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1(
    mut v_00_u03b2_1219_: *mut LeanObject,
    mut v_x_1220_: *mut LeanObject,
    mut v_x_1221_: *mut LeanObject,
    mut v_x_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    v___x_1223_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_x_1220_, v_x_1221_, v_x_1222_);
    return v___x_1223_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(
    mut v_00_u03b2_1224_: *mut LeanObject,
    mut v_x_1225_: *mut LeanObject,
    mut v_x_1226_: usize,
    mut v_x_1227_: usize,
    mut v_x_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    v___x_1230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_1225_, v_x_1226_, v_x_1227_, v_x_1228_, v_x_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_1231_: *mut LeanObject,
    mut v_x_1232_: *mut LeanObject,
    mut v_x_1233_: *mut LeanObject,
    mut v_x_1234_: *mut LeanObject,
    mut v_x_1235_: *mut LeanObject,
    mut v_x_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6160__boxed_1237_: usize = 0;
    let mut v_x_6161__boxed_1238_: usize = 0;
    let mut v_res_1239_: *mut LeanObject = core::ptr::null_mut();
    v_x_6160__boxed_1237_ = lean_unbox_usize(v_x_1233_);
    lean_dec(v_x_1233_);
    v_x_6161__boxed_1238_ = lean_unbox_usize(v_x_1234_);
    lean_dec(v_x_1234_);
    v_res_1239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(v_00_u03b2_1231_, v_x_1232_, v_x_6160__boxed_1237_, v_x_6161__boxed_1238_, v_x_1235_, v_x_1236_);
    return v_res_1239_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1240_: *mut LeanObject,
    mut v_n_1241_: *mut LeanObject,
    mut v_k_1242_: *mut LeanObject,
    mut v_v_1243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    v___x_1244_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v_n_1241_, v_k_1242_, v_v_1243_);
    return v___x_1244_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(
    mut v_00_u03b2_1245_: *mut LeanObject,
    mut v_depth_1246_: usize,
    mut v_keys_1247_: *mut LeanObject,
    mut v_vals_1248_: *mut LeanObject,
    mut v_heq_1249_: *mut LeanObject,
    mut v_i_1250_: *mut LeanObject,
    mut v_entries_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_1246_, v_keys_1247_, v_vals_1248_, v_i_1250_, v_entries_1251_);
    return v___x_1252_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_1253_: *mut LeanObject,
    mut v_depth_1254_: *mut LeanObject,
    mut v_keys_1255_: *mut LeanObject,
    mut v_vals_1256_: *mut LeanObject,
    mut v_heq_1257_: *mut LeanObject,
    mut v_i_1258_: *mut LeanObject,
    mut v_entries_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1260_: usize = 0;
    let mut v_res_1261_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1260_ = lean_unbox_usize(v_depth_1254_);
    lean_dec(v_depth_1254_);
    v_res_1261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_1253_, v_depth_boxed_1260_, v_keys_1255_, v_vals_1256_, v_heq_1257_, v_i_1258_, v_entries_1259_);
    lean_dec_ref(v_vals_1256_);
    lean_dec_ref(v_keys_1255_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7(
    mut v_00_u03b2_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
    mut v_x_1264_: *mut LeanObject,
    mut v_x_1265_: *mut LeanObject,
    mut v_x_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
    return v___x_1267_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1()
-> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1289_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4;
    v___x_1290_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8;
    v___x_1291_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1292_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1288_,
        v___x_1289_,
        v___x_1290_,
        v___x_1291_,
    );
    return v___x_1292_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(
    mut v_a_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_res_1294_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
    return v_res_1294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
}
