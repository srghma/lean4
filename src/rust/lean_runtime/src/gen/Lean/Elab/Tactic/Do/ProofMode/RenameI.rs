// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.RenameI
// Imports: Lean.Elab.Tactic.Do.ProofMode.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
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
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_9, lean_apply_10, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 114, 101, 110, 97, 109, 101, 73, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__3_value) as *mut LeanObject,12101716647590738894 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__3_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__6_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__6_value) as *mut LeanObject,14659826576719934041 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__8_value) as *mut LeanObject,4071431237389361899 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__10_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 110, 97, 109, 101, 73, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__10_value) as *mut LeanObject,16496990144058559046 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,12633748724407117007 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__0_value) as *mut LeanObject,17061652278011288802 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__3_value) as *mut LeanObject,8739641584612497344 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__2_value) as *mut LeanObject,14768364912228272605 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__6_value) as *mut LeanObject,17404095511016610289 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__16_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__8_value) as *mut LeanObject,15584572159853941027 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__18_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 77, 82, 101, 110, 97, 109, 101, 73, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__18_value) as *mut LeanObject,14549366300451879238 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__19_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___redArg___lam__0(
    mut v_k_678_: *mut LeanObject,
    mut v_goal_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = lean_apply_1(v_k_678_, v_goal_679_);
    return v___x_680_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___redArg(
    mut v_inst_681_: *mut LeanObject,
    mut v_inst_682_: *mut LeanObject,
    mut v_goal_683_: *mut LeanObject,
    mut v_idents_684_: *mut LeanObject,
    mut v_k_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_686_ = lean_ctor_get(v_inst_681_, 1);
    lean_inc(v_toBind_686_);
    lean_dec_ref(v_inst_681_);
    v___f_687_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_687_, 0, v_k_685_);
    v___x_688_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_688_, 0, v_goal_683_);
    lean_closure_set(v___x_688_, 1, v_idents_684_);
    v___x_689_ = lean_apply_2(v_inst_682_, lean_box(0), v___x_688_);
    v___x_690_ = lean_apply_4(
        v_toBind_686_,
        lean_box(0),
        lean_box(0),
        v___x_689_,
        v___f_687_,
    );
    return v___x_690_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI(
    mut v_m_691_: *mut LeanObject,
    mut v_00_u03b1_692_: *mut LeanObject,
    mut v_inst_693_: *mut LeanObject,
    mut v_inst_694_: *mut LeanObject,
    mut v_inst_695_: *mut LeanObject,
    mut v_goal_696_: *mut LeanObject,
    mut v_idents_697_: *mut LeanObject,
    mut v_k_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v___x_699_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___redArg(v_inst_693_, v_inst_695_, v_goal_696_, v_idents_697_, v_k_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___boxed(
    mut v_m_700_: *mut LeanObject,
    mut v_00_u03b1_701_: *mut LeanObject,
    mut v_inst_702_: *mut LeanObject,
    mut v_inst_703_: *mut LeanObject,
    mut v_inst_704_: *mut LeanObject,
    mut v_goal_705_: *mut LeanObject,
    mut v_idents_706_: *mut LeanObject,
    mut v_k_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_res_708_ =
        l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI(
            v_m_700_,
            v_00_u03b1_701_,
            v_inst_702_,
            v_inst_703_,
            v_inst_704_,
            v_goal_705_,
            v_idents_706_,
            v_k_707_,
        );
    lean_dec_ref(v_inst_703_);
    return v_res_708_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_box(0);
    v___x_710_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_711_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_711_, 0, v___x_710_);
    lean_ctor_set(v___x_711_, 1, v___x_709_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_713_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___closed__0);
    v___x_714_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_714_, 0, v___x_713_);
    return v___x_714_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg___boxed(
    mut v___y_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg();
    return v_res_716_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0(
    mut v_00_u03b1_717_: *mut LeanObject,
    mut v___y_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
    mut v___y_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg();
    return v___x_727_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___boxed(
    mut v_00_u03b1_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_738_: *mut LeanObject = core::ptr::null_mut();
    v_res_738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0(v_00_u03b1_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
    lean_dec(v___y_736_);
    lean_dec_ref(v___y_735_);
    lean_dec(v___y_734_);
    lean_dec_ref(v___y_733_);
    lean_dec(v___y_732_);
    lean_dec_ref(v___y_731_);
    lean_dec(v___y_730_);
    lean_dec_ref(v___y_729_);
    return v_res_738_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___redArg(
    mut v_goal_739_: *mut LeanObject,
    mut v_idents_740_: *mut LeanObject,
    mut v_k_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_751_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(
                    v_goal_739_,
                    v_idents_740_,
                    v___y_746_,
                    v___y_747_,
                    v___y_748_,
                    v___y_749_,
                );
                if lean_obj_tag(v___x_751_) == 0 {
                    v_a_752_ = lean_ctor_get(v___x_751_, 0);
                    lean_inc(v_a_752_);
                    lean_dec_ref_known(v___x_751_, 1);
                    lean_inc(v___y_749_);
                    lean_inc_ref(v___y_748_);
                    lean_inc(v___y_747_);
                    lean_inc_ref(v___y_746_);
                    lean_inc(v___y_745_);
                    lean_inc_ref(v___y_744_);
                    lean_inc(v___y_743_);
                    lean_inc_ref(v___y_742_);
                    v___x_753_ = lean_apply_10(
                        v_k_741_,
                        v_a_752_,
                        v___y_742_,
                        v___y_743_,
                        v___y_744_,
                        v___y_745_,
                        v___y_746_,
                        v___y_747_,
                        v___y_748_,
                        v___y_749_,
                        lean_box(0),
                    );
                    return v___x_753_;
                } else {
                    lean_dec_ref(v_k_741_);
                    v_a_754_ = lean_ctor_get(v___x_751_, 0);
                    v_isSharedCheck_761_ = (!lean_is_exclusive(v___x_751_)) as u8;
                    if v_isSharedCheck_761_ == 0 {
                        v___x_756_ = v___x_751_;
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_754_);
                        lean_dec(v___x_751_);
                        v___x_756_ = lean_box(0);
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___redArg___boxed(
    mut v_goal_762_: *mut LeanObject,
    mut v_idents_763_: *mut LeanObject,
    mut v_k_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___redArg(v_goal_762_, v_idents_763_, v_k_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
    lean_dec(v___y_772_);
    lean_dec_ref(v___y_771_);
    lean_dec(v___y_770_);
    lean_dec_ref(v___y_769_);
    lean_dec(v___y_768_);
    lean_dec_ref(v___y_767_);
    lean_dec(v___y_766_);
    lean_dec_ref(v___y_765_);
    return v_res_774_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1(
    mut v_00_u03b1_775_: *mut LeanObject,
    mut v_goal_776_: *mut LeanObject,
    mut v_idents_777_: *mut LeanObject,
    mut v_k_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___redArg(v_goal_776_, v_idents_777_, v_k_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
    return v___x_788_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___boxed(
    mut v_00_u03b1_789_: *mut LeanObject,
    mut v_goal_790_: *mut LeanObject,
    mut v_idents_791_: *mut LeanObject,
    mut v_k_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
    mut v___y_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
    mut v___y_797_: *mut LeanObject,
    mut v___y_798_: *mut LeanObject,
    mut v___y_799_: *mut LeanObject,
    mut v___y_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_802_: *mut LeanObject = core::ptr::null_mut();
    v_res_802_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1(v_00_u03b1_789_, v_goal_790_, v_idents_791_, v_k_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
    lean_dec(v___y_800_);
    lean_dec_ref(v___y_799_);
    lean_dec(v___y_798_);
    lean_dec_ref(v___y_797_);
    lean_dec(v___y_796_);
    lean_dec_ref(v___y_795_);
    lean_dec(v___y_794_);
    lean_dec_ref(v___y_793_);
    return v_res_802_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg___lam__0(
    mut v_x_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_807_);
    lean_inc_ref(v___y_806_);
    lean_inc(v___y_805_);
    lean_inc_ref(v___y_804_);
    v___x_813_ = lean_apply_9(
        v_x_803_,
        v___y_804_,
        v___y_805_,
        v___y_806_,
        v___y_807_,
        v___y_808_,
        v___y_809_,
        v___y_810_,
        v___y_811_,
        lean_box(0),
    );
    return v___x_813_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg___lam__0___boxed(
    mut v_x_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
    mut v___y_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
    mut v___y_820_: *mut LeanObject,
    mut v___y_821_: *mut LeanObject,
    mut v___y_822_: *mut LeanObject,
    mut v___y_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_824_: *mut LeanObject = core::ptr::null_mut();
    v_res_824_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg___lam__0(v_x_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
    lean_dec(v___y_818_);
    lean_dec_ref(v___y_817_);
    lean_dec(v___y_816_);
    lean_dec_ref(v___y_815_);
    return v_res_824_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg(
    mut v_mvarId_825_: *mut LeanObject,
    mut v_x_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_830_);
                lean_inc_ref(v___y_829_);
                lean_inc(v___y_828_);
                lean_inc_ref(v___y_827_);
                v___f_836_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_836_, 0, v_x_826_);
                lean_closure_set(v___f_836_, 1, v___y_827_);
                lean_closure_set(v___f_836_, 2, v___y_828_);
                lean_closure_set(v___f_836_, 3, v___y_829_);
                lean_closure_set(v___f_836_, 4, v___y_830_);
                v___x_837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_825_,
                    v___f_836_,
                    v___y_831_,
                    v___y_832_,
                    v___y_833_,
                    v___y_834_,
                );
                if lean_obj_tag(v___x_837_) == 0 {
                    return v___x_837_;
                } else {
                    v_a_838_ = lean_ctor_get(v___x_837_, 0);
                    v_isSharedCheck_845_ = (!lean_is_exclusive(v___x_837_)) as u8;
                    if v_isSharedCheck_845_ == 0 {
                        v___x_840_ = v___x_837_;
                        v_isShared_841_ = v_isSharedCheck_845_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_838_);
                        lean_dec(v___x_837_);
                        v___x_840_ = lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_845_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_841_ == 0 {
                    v___x_843_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
                    v___x_843_ = v_reuseFailAlloc_844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg___boxed(
    mut v_mvarId_846_: *mut LeanObject,
    mut v_x_847_: *mut LeanObject,
    mut v___y_848_: *mut LeanObject,
    mut v___y_849_: *mut LeanObject,
    mut v___y_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_857_: *mut LeanObject = core::ptr::null_mut();
    v_res_857_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg(v_mvarId_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
    lean_dec(v___y_855_);
    lean_dec_ref(v___y_854_);
    lean_dec(v___y_853_);
    lean_dec_ref(v___y_852_);
    lean_dec(v___y_851_);
    lean_dec_ref(v___y_850_);
    lean_dec(v___y_849_);
    lean_dec_ref(v___y_848_);
    return v_res_857_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3(
    mut v_00_u03b1_858_: *mut LeanObject,
    mut v_mvarId_859_: *mut LeanObject,
    mut v_x_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg(v_mvarId_859_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___boxed(
    mut v_00_u03b1_871_: *mut LeanObject,
    mut v_mvarId_872_: *mut LeanObject,
    mut v_x_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
    mut v___y_879_: *mut LeanObject,
    mut v___y_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3(v_00_u03b1_871_, v_mvarId_872_, v_x_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
    lean_dec(v___y_881_);
    lean_dec_ref(v___y_880_);
    lean_dec(v___y_879_);
    lean_dec_ref(v___y_878_);
    lean_dec(v___y_877_);
    lean_dec_ref(v___y_876_);
    lean_dec(v___y_875_);
    lean_dec_ref(v___y_874_);
    return v_res_883_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__0(
    mut v_val_884_: *mut LeanObject,
    mut v_newGoal_885_: *mut LeanObject,
    mut v___y_886_: *mut LeanObject,
    mut v___y_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
    mut v___y_889_: *mut LeanObject,
    mut v___y_890_: *mut LeanObject,
    mut v___y_891_: *mut LeanObject,
    mut v___y_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_a_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_895_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_885_);
                v___x_896_ = lean_box(0);
                v___x_897_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_895_, v___x_896_, v___y_890_, v___y_891_, v___y_892_, v___y_893_,
                );
                if lean_obj_tag(v___x_897_) == 0 {
                    v_a_898_ = lean_ctor_get(v___x_897_, 0);
                    v_isSharedCheck_911_ = (!lean_is_exclusive(v___x_897_)) as u8;
                    if v_isSharedCheck_911_ == 0 {
                        v___x_900_ = v___x_897_;
                        v_isShared_901_ = v_isSharedCheck_911_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_898_);
                        lean_dec(v___x_897_);
                        v___x_900_ = lean_box(0);
                        v_isShared_901_ = v_isSharedCheck_911_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_912_ = lean_ctor_get(v___x_897_, 0);
                    v_isSharedCheck_919_ = (!lean_is_exclusive(v___x_897_)) as u8;
                    if v_isSharedCheck_919_ == 0 {
                        v___x_914_ = v___x_897_;
                        v_isShared_915_ = v_isSharedCheck_919_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_912_);
                        lean_dec(v___x_897_);
                        v___x_914_ = lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_919_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_902_ = lean_st_ref_take(v_val_884_);
                v___x_903_ = l_Lean_Expr_mvarId_x21(v_a_898_);
                v___x_904_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_904_, 0, v___x_903_);
                lean_ctor_set(v___x_904_, 1, v___x_902_);
                v___x_905_ = lean_st_ref_set(v_val_884_, v___x_904_);
                v___x_906_ = lean_box(0);
                v___x_907_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_907_, 0, v___x_906_);
                lean_ctor_set(v___x_907_, 1, v_a_898_);
                if v_isShared_901_ == 0 {
                    lean_ctor_set(v___x_900_, 0, v___x_907_);
                    v___x_909_ = v___x_900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
                    v___x_909_ = v_reuseFailAlloc_910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_909_;
            }
            3 => {
                if v_isShared_915_ == 0 {
                    v___x_917_ = v___x_914_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
                    v___x_917_ = v_reuseFailAlloc_918_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__0___boxed(
    mut v_val_920_: *mut LeanObject,
    mut v_newGoal_921_: *mut LeanObject,
    mut v___y_922_: *mut LeanObject,
    mut v___y_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
    mut v___y_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_931_: *mut LeanObject = core::ptr::null_mut();
    v_res_931_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__0(v_val_920_, v_newGoal_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
    lean_dec(v___y_929_);
    lean_dec_ref(v___y_928_);
    lean_dec(v___y_927_);
    lean_dec_ref(v___y_926_);
    lean_dec(v___y_925_);
    lean_dec_ref(v___y_924_);
    lean_dec(v___y_923_);
    lean_dec_ref(v___y_922_);
    lean_dec(v_val_920_);
    return v_res_931_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_932_: *mut LeanObject,
    mut v_x_933_: *mut LeanObject,
    mut v_x_934_: *mut LeanObject,
    mut v_x_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_936_ = lean_ctor_get(v_x_932_, 0);
                v_vs_937_ = lean_ctor_get(v_x_932_, 1);
                v_isSharedCheck_961_ = (!lean_is_exclusive(v_x_932_)) as u8;
                if v_isSharedCheck_961_ == 0 {
                    v___x_939_ = v_x_932_;
                    v_isShared_940_ = v_isSharedCheck_961_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_937_);
                    lean_inc(v_ks_936_);
                    lean_dec(v_x_932_);
                    v___x_939_ = lean_box(0);
                    v_isShared_940_ = v_isSharedCheck_961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_941_ = lean_array_get_size(v_ks_936_);
                v___x_942_ = lean_nat_dec_lt(v_x_933_, v___x_941_);
                if v___x_942_ == 0 {
                    lean_dec(v_x_933_);
                    v___x_943_ = lean_array_push(v_ks_936_, v_x_934_);
                    v___x_944_ = lean_array_push(v_vs_937_, v_x_935_);
                    if v_isShared_940_ == 0 {
                        lean_ctor_set(v___x_939_, 1, v___x_944_);
                        lean_ctor_set(v___x_939_, 0, v___x_943_);
                        v___x_946_ = v___x_939_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_943_);
                        lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_944_);
                        v___x_946_ = v_reuseFailAlloc_947_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_948_ = lean_array_fget_borrowed(v_ks_936_, v_x_933_);
                    v___x_949_ = l_Lean_instBEqMVarId_beq(v_x_934_, v_k_x27_948_);
                    if v___x_949_ == 0 {
                        if v_isShared_940_ == 0 {
                            v___x_951_ = v___x_939_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_955_, 0, v_ks_936_);
                            lean_ctor_set(v_reuseFailAlloc_955_, 1, v_vs_937_);
                            v___x_951_ = v_reuseFailAlloc_955_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_956_ = lean_array_fset(v_ks_936_, v_x_933_, v_x_934_);
                        v___x_957_ = lean_array_fset(v_vs_937_, v_x_933_, v_x_935_);
                        lean_dec(v_x_933_);
                        if v_isShared_940_ == 0 {
                            lean_ctor_set(v___x_939_, 1, v___x_957_);
                            lean_ctor_set(v___x_939_, 0, v___x_956_);
                            v___x_959_ = v___x_939_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_956_);
                            lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_957_);
                            v___x_959_ = v_reuseFailAlloc_960_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_946_;
            }
            3 => {
                v___x_952_ = lean_unsigned_to_nat(1);
                v___x_953_ = lean_nat_add(v_x_933_, v___x_952_);
                lean_dec(v_x_933_);
                v_x_932_ = v___x_951_;
                v_x_933_ = v___x_953_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5___redArg(
    mut v_n_962_: *mut LeanObject,
    mut v_k_963_: *mut LeanObject,
    mut v_v_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = lean_unsigned_to_nat(0);
    v___x_966_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_n_962_, v___x_965_, v_k_963_, v_v_964_);
    return v___x_966_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_967_: usize = 0;
    let mut v___x_968_: usize = 0;
    let mut v___x_969_: usize = 0;
    v___x_967_ = 5usize;
    v___x_968_ = 1usize;
    v___x_969_ = lean_usize_shift_left(v___x_968_, v___x_967_);
    return v___x_969_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_970_: usize = 0;
    let mut v___x_971_: usize = 0;
    let mut v___x_972_: usize = 0;
    v___x_970_ = 1usize;
    v___x_971_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_972_ = lean_usize_sub(v___x_971_, v___x_970_);
    return v___x_972_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_973_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(
    mut v_x_974_: *mut LeanObject,
    mut v_x_975_: usize,
    mut v_x_976_: usize,
    mut v_x_977_: *mut LeanObject,
    mut v_x_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: usize = 0;
    let mut v___x_981_: usize = 0;
    let mut v___x_982_: usize = 0;
    let mut v___x_983_: usize = 0;
    let mut v_j_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_989_: u8 = 0;
    let mut v_v_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v_node_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1014_: u8 = 0;
    let mut v___x_1015_: usize = 0;
    let mut v___x_1016_: usize = 0;
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1021_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_unused_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: u8 = 0;
    let mut v_ks_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: usize = 0;
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v_reuseFailAlloc_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_974_) == 0 {
                    v_es_979_ = lean_ctor_get(v_x_974_, 0);
                    v___x_980_ = 5usize;
                    v___x_981_ = 1usize;
                    v___x_982_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_983_ = lean_usize_land(v_x_975_, v___x_982_);
                    v_j_984_ = lean_usize_to_nat(v___x_983_);
                    v___x_985_ = lean_array_get_size(v_es_979_);
                    v___x_986_ = lean_nat_dec_lt(v_j_984_, v___x_985_);
                    if v___x_986_ == 0 {
                        lean_dec(v_j_984_);
                        lean_dec(v_x_978_);
                        lean_dec(v_x_977_);
                        return v_x_974_;
                    } else {
                        lean_inc_ref(v_es_979_);
                        v_isSharedCheck_1023_ = (!lean_is_exclusive(v_x_974_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v_unused_1024_ = lean_ctor_get(v_x_974_, 0);
                            lean_dec(v_unused_1024_);
                            v___x_988_ = v_x_974_;
                            v_isShared_989_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_974_);
                            v___x_988_ = lean_box(0);
                            v_isShared_989_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1025_ = lean_ctor_get(v_x_974_, 0);
                    v_vs_1026_ = lean_ctor_get(v_x_974_, 1);
                    v_isSharedCheck_1046_ = (!lean_is_exclusive(v_x_974_)) as u8;
                    if v_isSharedCheck_1046_ == 0 {
                        v___x_1028_ = v_x_974_;
                        v_isShared_1029_ = v_isSharedCheck_1046_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1026_);
                        lean_inc(v_ks_1025_);
                        lean_dec(v_x_974_);
                        v___x_1028_ = lean_box(0);
                        v_isShared_1029_ = v_isSharedCheck_1046_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_990_ = lean_array_fget(v_es_979_, v_j_984_);
                v___x_991_ = lean_box(0);
                v_xs_x27_992_ = lean_array_fset(v_es_979_, v_j_984_, v___x_991_);
                match lean_obj_tag(v_v_990_) {
                    0 => {
                        v_key_999_ = lean_ctor_get(v_v_990_, 0);
                        v_val_1000_ = lean_ctor_get(v_v_990_, 1);
                        v_isSharedCheck_1010_ = (!lean_is_exclusive(v_v_990_)) as u8;
                        if v_isSharedCheck_1010_ == 0 {
                            v___x_1002_ = v_v_990_;
                            v_isShared_1003_ = v_isSharedCheck_1010_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1000_);
                            lean_inc(v_key_999_);
                            lean_dec(v_v_990_);
                            v___x_1002_ = lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1010_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1011_ = lean_ctor_get(v_v_990_, 0);
                        v_isSharedCheck_1021_ = (!lean_is_exclusive(v_v_990_)) as u8;
                        if v_isSharedCheck_1021_ == 0 {
                            v___x_1013_ = v_v_990_;
                            v_isShared_1014_ = v_isSharedCheck_1021_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1011_);
                            lean_dec(v_v_990_);
                            v___x_1013_ = lean_box(0);
                            v_isShared_1014_ = v_isSharedCheck_1021_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1022_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1022_, 0, v_x_977_);
                        lean_ctor_set(v___x_1022_, 1, v_x_978_);
                        v___y_994_ = v___x_1022_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_995_ = lean_array_fset(v_xs_x27_992_, v_j_984_, v___y_994_);
                lean_dec(v_j_984_);
                if v_isShared_989_ == 0 {
                    lean_ctor_set(v___x_988_, 0, v___x_995_);
                    v___x_997_ = v___x_988_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_997_;
            }
            4 => {
                v___x_1004_ = l_Lean_instBEqMVarId_beq(v_x_977_, v_key_999_);
                if v___x_1004_ == 0 {
                    lean_del_object(v___x_1002_);
                    v___x_1005_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_999_,
                        v_val_1000_,
                        v_x_977_,
                        v_x_978_,
                    );
                    v___x_1006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1006_, 0, v___x_1005_);
                    v___y_994_ = v___x_1006_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1000_);
                    lean_dec(v_key_999_);
                    if v_isShared_1003_ == 0 {
                        lean_ctor_set(v___x_1002_, 1, v_x_978_);
                        lean_ctor_set(v___x_1002_, 0, v_x_977_);
                        v___x_1008_ = v___x_1002_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_x_977_);
                        lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_x_978_);
                        v___x_1008_ = v_reuseFailAlloc_1009_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_994_ = v___x_1008_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1015_ = lean_usize_shift_right(v_x_975_, v___x_980_);
                v___x_1016_ = lean_usize_add(v_x_976_, v___x_981_);
                v___x_1017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(v_node_1011_, v___x_1015_, v___x_1016_, v_x_977_, v_x_978_);
                if v_isShared_1014_ == 0 {
                    lean_ctor_set(v___x_1013_, 0, v___x_1017_);
                    v___x_1019_ = v___x_1013_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
                    v___x_1019_ = v_reuseFailAlloc_1020_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_994_ = v___x_1019_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1029_ == 0 {
                    v___x_1031_ = v___x_1028_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_ks_1025_);
                    lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_vs_1026_);
                    v___x_1031_ = v_reuseFailAlloc_1045_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5___redArg(v___x_1031_, v_x_977_, v_x_978_);
                v___x_1040_ = 7usize;
                v___x_1041_ = lean_usize_dec_le(v___x_1040_, v_x_976_);
                if v___x_1041_ == 0 {
                    v___x_1042_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1032_);
                    v___x_1043_ = lean_unsigned_to_nat(4);
                    v___x_1044_ = lean_nat_dec_lt(v___x_1042_, v___x_1043_);
                    lean_dec(v___x_1042_);
                    v___y_1034_ = v___x_1044_;
                    state = 10;
                    continue;
                } else {
                    v___y_1034_ = v___x_1041_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1034_ == 0 {
                    v_ks_1035_ = lean_ctor_get(v_newNode_1032_, 0);
                    lean_inc_ref(v_ks_1035_);
                    v_vs_1036_ = lean_ctor_get(v_newNode_1032_, 1);
                    lean_inc_ref(v_vs_1036_);
                    lean_dec_ref(v_newNode_1032_);
                    v___x_1037_ = lean_unsigned_to_nat(0);
                    v___x_1038_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_1039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___redArg(v_x_976_, v_ks_1035_, v_vs_1036_, v___x_1037_, v___x_1038_);
                    lean_dec_ref(v_vs_1036_);
                    lean_dec_ref(v_ks_1035_);
                    return v___x_1039_;
                } else {
                    return v_newNode_1032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___redArg(
    mut v_depth_1047_: usize,
    mut v_keys_1048_: *mut LeanObject,
    mut v_vals_1049_: *mut LeanObject,
    mut v_i_1050_: *mut LeanObject,
    mut v_entries_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v_k_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: u64 = 0;
    let mut v_h_1057_: usize = 0;
    let mut v___x_1058_: usize = 0;
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: usize = 0;
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v_h_1063_: usize = 0;
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1052_ = lean_array_get_size(v_keys_1048_);
                v___x_1053_ = lean_nat_dec_lt(v_i_1050_, v___x_1052_);
                if v___x_1053_ == 0 {
                    lean_dec(v_i_1050_);
                    return v_entries_1051_;
                } else {
                    v_k_1054_ = lean_array_fget_borrowed(v_keys_1048_, v_i_1050_);
                    v_v_1055_ = lean_array_fget_borrowed(v_vals_1049_, v_i_1050_);
                    v___x_1056_ = l_Lean_instHashableMVarId_hash(v_k_1054_);
                    v_h_1057_ = lean_uint64_to_usize(v___x_1056_);
                    v___x_1058_ = 5usize;
                    v___x_1059_ = lean_unsigned_to_nat(1);
                    v___x_1060_ = 1usize;
                    v___x_1061_ = lean_usize_sub(v_depth_1047_, v___x_1060_);
                    v___x_1062_ = lean_usize_mul(v___x_1058_, v___x_1061_);
                    v_h_1063_ = lean_usize_shift_right(v_h_1057_, v___x_1062_);
                    v___x_1064_ = lean_nat_add(v_i_1050_, v___x_1059_);
                    lean_dec(v_i_1050_);
                    lean_inc(v_v_1055_);
                    lean_inc(v_k_1054_);
                    v___x_1065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(v_entries_1051_, v_h_1063_, v_depth_1047_, v_k_1054_, v_v_1055_);
                    v_i_1050_ = v___x_1064_;
                    v_entries_1051_ = v___x_1065_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_depth_1067_: *mut LeanObject,
    mut v_keys_1068_: *mut LeanObject,
    mut v_vals_1069_: *mut LeanObject,
    mut v_i_1070_: *mut LeanObject,
    mut v_entries_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1072_: usize = 0;
    let mut v_res_1073_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1072_ = lean_unbox_usize(v_depth_1067_);
    lean_dec(v_depth_1067_);
    v_res_1073_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_boxed_1072_, v_keys_1068_, v_vals_1069_, v_i_1070_, v_entries_1071_);
    lean_dec_ref(v_vals_1069_);
    lean_dec_ref(v_keys_1068_);
    return v_res_1073_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1074_: *mut LeanObject,
    mut v_x_1075_: *mut LeanObject,
    mut v_x_1076_: *mut LeanObject,
    mut v_x_1077_: *mut LeanObject,
    mut v_x_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5778__boxed_1079_: usize = 0;
    let mut v_x_5779__boxed_1080_: usize = 0;
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_x_5778__boxed_1079_ = lean_unbox_usize(v_x_1075_);
    lean_dec(v_x_1075_);
    v_x_5779__boxed_1080_ = lean_unbox_usize(v_x_1076_);
    lean_dec(v_x_1076_);
    v_res_1081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(v_x_1074_, v_x_5778__boxed_1079_, v_x_5779__boxed_1080_, v_x_1077_, v_x_1078_);
    return v_res_1081_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2___redArg(
    mut v_x_1082_: *mut LeanObject,
    mut v_x_1083_: *mut LeanObject,
    mut v_x_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1085_: u64 = 0;
    let mut v___x_1086_: usize = 0;
    let mut v___x_1087_: usize = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_instHashableMVarId_hash(v_x_1083_);
    v___x_1086_ = lean_uint64_to_usize(v___x_1085_);
    v___x_1087_ = 1usize;
    v___x_1088_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(v_x_1082_, v___x_1086_, v___x_1087_, v_x_1083_, v_x_1084_);
    return v___x_1088_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___redArg(
    mut v_mvarId_1089_: *mut LeanObject,
    mut v_val_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v_depth_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_isSharedCheck_1126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_st_ref_take(v___y_1091_);
                v_mctx_1094_ = lean_ctor_get(v___x_1093_, 0);
                v_cache_1095_ = lean_ctor_get(v___x_1093_, 1);
                v_zetaDeltaFVarIds_1096_ = lean_ctor_get(v___x_1093_, 2);
                v_postponed_1097_ = lean_ctor_get(v___x_1093_, 3);
                v_diag_1098_ = lean_ctor_get(v___x_1093_, 4);
                v_isSharedCheck_1126_ = (!lean_is_exclusive(v___x_1093_)) as u8;
                if v_isSharedCheck_1126_ == 0 {
                    v___x_1100_ = v___x_1093_;
                    v_isShared_1101_ = v_isSharedCheck_1126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1098_);
                    lean_inc(v_postponed_1097_);
                    lean_inc(v_zetaDeltaFVarIds_1096_);
                    lean_inc(v_cache_1095_);
                    lean_inc(v_mctx_1094_);
                    lean_dec(v___x_1093_);
                    v___x_1100_ = lean_box(0);
                    v_isShared_1101_ = v_isSharedCheck_1126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1102_ = lean_ctor_get(v_mctx_1094_, 0);
                v_levelAssignDepth_1103_ = lean_ctor_get(v_mctx_1094_, 1);
                v_lmvarCounter_1104_ = lean_ctor_get(v_mctx_1094_, 2);
                v_mvarCounter_1105_ = lean_ctor_get(v_mctx_1094_, 3);
                v_lDecls_1106_ = lean_ctor_get(v_mctx_1094_, 4);
                v_decls_1107_ = lean_ctor_get(v_mctx_1094_, 5);
                v_userNames_1108_ = lean_ctor_get(v_mctx_1094_, 6);
                v_lAssignment_1109_ = lean_ctor_get(v_mctx_1094_, 7);
                v_eAssignment_1110_ = lean_ctor_get(v_mctx_1094_, 8);
                v_dAssignment_1111_ = lean_ctor_get(v_mctx_1094_, 9);
                v_isSharedCheck_1125_ = (!lean_is_exclusive(v_mctx_1094_)) as u8;
                if v_isSharedCheck_1125_ == 0 {
                    v___x_1113_ = v_mctx_1094_;
                    v_isShared_1114_ = v_isSharedCheck_1125_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1111_);
                    lean_inc(v_eAssignment_1110_);
                    lean_inc(v_lAssignment_1109_);
                    lean_inc(v_userNames_1108_);
                    lean_inc(v_decls_1107_);
                    lean_inc(v_lDecls_1106_);
                    lean_inc(v_mvarCounter_1105_);
                    lean_inc(v_lmvarCounter_1104_);
                    lean_inc(v_levelAssignDepth_1103_);
                    lean_inc(v_depth_1102_);
                    lean_dec(v_mctx_1094_);
                    v___x_1113_ = lean_box(0);
                    v_isShared_1114_ = v_isSharedCheck_1125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1115_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2___redArg(v_eAssignment_1110_, v_mvarId_1089_, v_val_1090_);
                if v_isShared_1114_ == 0 {
                    lean_ctor_set(v___x_1113_, 8, v___x_1115_);
                    v___x_1117_ = v___x_1113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_depth_1102_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_levelAssignDepth_1103_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_lmvarCounter_1104_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_mvarCounter_1105_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_lDecls_1106_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_decls_1107_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 6, v_userNames_1108_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 7, v_lAssignment_1109_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 8, v___x_1115_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 9, v_dAssignment_1111_);
                    v___x_1117_ = v_reuseFailAlloc_1124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1101_ == 0 {
                    lean_ctor_set(v___x_1100_, 0, v___x_1117_);
                    v___x_1119_ = v___x_1100_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_cache_1095_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_zetaDeltaFVarIds_1096_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_postponed_1097_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_diag_1098_);
                    v___x_1119_ = v_reuseFailAlloc_1123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1120_ = lean_st_ref_set(v___y_1091_, v___x_1119_);
                v___x_1121_ = lean_box(0);
                v___x_1122_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                return v___x_1122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___redArg___boxed(
    mut v_mvarId_1127_: *mut LeanObject,
    mut v_val_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___redArg(v_mvarId_1127_, v_val_1128_, v___y_1129_);
    lean_dec(v___y_1129_);
    return v_res_1131_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__1(
    mut v___x_1132_: *mut LeanObject,
    mut v_snd_1133_: *mut LeanObject,
    mut v_idents_1134_: *mut LeanObject,
    mut v_fst_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1145_ = lean_st_mk_ref(v___x_1132_);
                lean_inc(v___x_1145_);
                v___f_1146_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                lean_closure_set(v___f_1146_, 0, v___x_1145_);
                v___x_1147_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_mRenameI___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__1___redArg(v_snd_1133_, v_idents_1134_, v___f_1146_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
                if lean_obj_tag(v___x_1147_) == 0 {
                    v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
                    lean_inc(v_a_1148_);
                    lean_dec_ref_known(v___x_1147_, 1);
                    v_snd_1149_ = lean_ctor_get(v_a_1148_, 1);
                    lean_inc(v_snd_1149_);
                    lean_dec(v_a_1148_);
                    v___x_1150_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___redArg(v_fst_1135_, v_snd_1149_, v___y_1141_);
                    lean_dec_ref(v___x_1150_);
                    v___x_1151_ = lean_st_ref_get(v___x_1145_);
                    lean_dec(v___x_1145_);
                    v___x_1152_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1151_,
                        v___y_1137_,
                        v___y_1140_,
                        v___y_1141_,
                        v___y_1142_,
                        v___y_1143_,
                    );
                    return v___x_1152_;
                } else {
                    lean_dec(v___x_1145_);
                    lean_dec(v_fst_1135_);
                    v_a_1153_ = lean_ctor_get(v___x_1147_, 0);
                    v_isSharedCheck_1160_ = (!lean_is_exclusive(v___x_1147_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v___x_1155_ = v___x_1147_;
                        v_isShared_1156_ = v_isSharedCheck_1160_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1153_);
                        lean_dec(v___x_1147_);
                        v___x_1155_ = lean_box(0);
                        v_isShared_1156_ = v_isSharedCheck_1160_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1156_ == 0 {
                    v___x_1158_ = v___x_1155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
                    v___x_1158_ = v_reuseFailAlloc_1159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__1___boxed(
    mut v___x_1161_: *mut LeanObject,
    mut v_snd_1162_: *mut LeanObject,
    mut v_idents_1163_: *mut LeanObject,
    mut v_fst_1164_: *mut LeanObject,
    mut v___y_1165_: *mut LeanObject,
    mut v___y_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1174_: *mut LeanObject = core::ptr::null_mut();
    v_res_1174_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__1(v___x_1161_, v_snd_1162_, v_idents_1163_, v_fst_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
    lean_dec(v___y_1172_);
    lean_dec_ref(v___y_1171_);
    lean_dec(v___y_1170_);
    lean_dec_ref(v___y_1169_);
    lean_dec(v___y_1168_);
    lean_dec_ref(v___y_1167_);
    lean_dec(v___y_1166_);
    lean_dec_ref(v___y_1165_);
    return v_res_1174_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI(
    mut v_x_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idents_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1194_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4;
                lean_inc(v_x_1184_);
                v___x_1195_ = l_Lean_Syntax_isOfKind(v_x_1184_, v___x_1194_);
                if v___x_1195_ == 0 {
                    lean_dec(v_x_1184_);
                    v___x_1196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__0___redArg();
                    return v___x_1196_;
                } else {
                    v___x_1197_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                        v_a_1186_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_,
                    );
                    if lean_obj_tag(v___x_1197_) == 0 {
                        v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
                        lean_inc(v_a_1198_);
                        lean_dec_ref_known(v___x_1197_, 1);
                        v_fst_1199_ = lean_ctor_get(v_a_1198_, 0);
                        lean_inc_n(v_fst_1199_, 2);
                        v_snd_1200_ = lean_ctor_get(v_a_1198_, 1);
                        lean_inc(v_snd_1200_);
                        lean_dec(v_a_1198_);
                        v___x_1201_ = lean_unsigned_to_nat(1);
                        v___x_1202_ = l_Lean_Syntax_getArg(v_x_1184_, v___x_1201_);
                        lean_dec(v_x_1184_);
                        v_idents_1203_ = l_Lean_Syntax_getArgs(v___x_1202_);
                        lean_dec(v___x_1202_);
                        v___x_1204_ = lean_box(0);
                        v___f_1205_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___lam__1___boxed as *mut core::ffi::c_void, 13, 4);
                        lean_closure_set(v___f_1205_, 0, v___x_1204_);
                        lean_closure_set(v___f_1205_, 1, v_snd_1200_);
                        lean_closure_set(v___f_1205_, 2, v_idents_1203_);
                        lean_closure_set(v___f_1205_, 3, v_fst_1199_);
                        v___x_1206_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__3___redArg(v_fst_1199_, v___f_1205_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
                        return v___x_1206_;
                    } else {
                        lean_dec(v_x_1184_);
                        v_a_1207_ = lean_ctor_get(v___x_1197_, 0);
                        v_isSharedCheck_1214_ = (!lean_is_exclusive(v___x_1197_)) as u8;
                        if v_isSharedCheck_1214_ == 0 {
                            v___x_1209_ = v___x_1197_;
                            v_isShared_1210_ = v_isSharedCheck_1214_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1207_);
                            lean_dec(v___x_1197_);
                            v___x_1209_ = lean_box(0);
                            v_isShared_1210_ = v_isSharedCheck_1214_;
                            state = 1;
                            continue;
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
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
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
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___boxed(
    mut v_x_1215_: *mut LeanObject,
    mut v_a_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_a_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
    mut v_a_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
    mut v_a_1222_: *mut LeanObject,
    mut v_a_1223_: *mut LeanObject,
    mut v_a_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI(v_x_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
    lean_dec(v_a_1223_);
    lean_dec_ref(v_a_1222_);
    lean_dec(v_a_1221_);
    lean_dec_ref(v_a_1220_);
    lean_dec(v_a_1219_);
    lean_dec_ref(v_a_1218_);
    lean_dec(v_a_1217_);
    lean_dec_ref(v_a_1216_);
    return v_res_1225_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2(
    mut v_mvarId_1226_: *mut LeanObject,
    mut v_val_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___redArg(v_mvarId_1226_, v_val_1227_, v___y_1233_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2___boxed(
    mut v_mvarId_1238_: *mut LeanObject,
    mut v_val_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2(v_mvarId_1238_, v_val_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
    lean_dec(v___y_1247_);
    lean_dec_ref(v___y_1246_);
    lean_dec(v___y_1245_);
    lean_dec_ref(v___y_1244_);
    lean_dec(v___y_1243_);
    lean_dec_ref(v___y_1242_);
    lean_dec(v___y_1241_);
    lean_dec_ref(v___y_1240_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2(
    mut v_00_u03b2_1250_: *mut LeanObject,
    mut v_x_1251_: *mut LeanObject,
    mut v_x_1252_: *mut LeanObject,
    mut v_x_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2___redArg(v_x_1251_, v_x_1252_, v_x_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1255_: *mut LeanObject,
    mut v_x_1256_: *mut LeanObject,
    mut v_x_1257_: usize,
    mut v_x_1258_: usize,
    mut v_x_1259_: *mut LeanObject,
    mut v_x_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___redArg(v_x_1256_, v_x_1257_, v_x_1258_, v_x_1259_, v_x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
    mut v_x_1264_: *mut LeanObject,
    mut v_x_1265_: *mut LeanObject,
    mut v_x_1266_: *mut LeanObject,
    mut v_x_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6176__boxed_1268_: usize = 0;
    let mut v_x_6177__boxed_1269_: usize = 0;
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_x_6176__boxed_1268_ = lean_unbox_usize(v_x_1264_);
    lean_dec(v_x_1264_);
    v_x_6177__boxed_1269_ = lean_unbox_usize(v_x_1265_);
    lean_dec(v_x_1265_);
    v_res_1270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4(v_00_u03b2_1262_, v_x_1263_, v_x_6176__boxed_1268_, v_x_6177__boxed_1269_, v_x_1266_, v_x_1267_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1271_: *mut LeanObject,
    mut v_n_1272_: *mut LeanObject,
    mut v_k_1273_: *mut LeanObject,
    mut v_v_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5___redArg(v_n_1272_, v_k_1273_, v_v_1274_);
    return v___x_1275_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6(
    mut v_00_u03b2_1276_: *mut LeanObject,
    mut v_depth_1277_: usize,
    mut v_keys_1278_: *mut LeanObject,
    mut v_vals_1279_: *mut LeanObject,
    mut v_heq_1280_: *mut LeanObject,
    mut v_i_1281_: *mut LeanObject,
    mut v_entries_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___redArg(v_depth_1277_, v_keys_1278_, v_vals_1279_, v_i_1281_, v_entries_1282_);
    return v___x_1283_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_1284_: *mut LeanObject,
    mut v_depth_1285_: *mut LeanObject,
    mut v_keys_1286_: *mut LeanObject,
    mut v_vals_1287_: *mut LeanObject,
    mut v_heq_1288_: *mut LeanObject,
    mut v_i_1289_: *mut LeanObject,
    mut v_entries_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1291_: usize = 0;
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1291_ = lean_unbox_usize(v_depth_1285_);
    lean_dec(v_depth_1285_);
    v_res_1292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_1284_, v_depth_boxed_1291_, v_keys_1286_, v_vals_1287_, v_heq_1288_, v_i_1289_, v_entries_1290_);
    lean_dec_ref(v_vals_1287_);
    lean_dec_ref(v_keys_1286_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1293_: *mut LeanObject,
    mut v_x_1294_: *mut LeanObject,
    mut v_x_1295_: *mut LeanObject,
    mut v_x_1296_: *mut LeanObject,
    mut v_x_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI_spec__2_spec__2_spec__4_spec__5_spec__6___redArg(v_x_1294_, v_x_1295_, v_x_1296_, v_x_1297_);
    return v___x_1298_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1()
-> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1348_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1349_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___closed__4;
    v___x_1350_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___closed__19;
    v___x_1351_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1352_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1348_,
        v___x_1349_,
        v___x_1350_,
        v___x_1351_,
    );
    return v___x_1352_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1___boxed(
    mut v_a_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_res_1354_ = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1();
    return v_res_1354_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(
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
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_RenameI_0__Lean_Elab_Tactic_Do_ProofMode_elabMRenameI__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_RenameI(builtin);
}
